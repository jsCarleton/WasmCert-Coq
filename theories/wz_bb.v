From Coq Require Import Lia Wf_nat.
From Coq Require Import List.
From Coq Require Import BinNat Strings.Byte.
From Coq Require Import ZArith ZArith.Int ZArith.BinInt ZArith.Zpower.
From compcert Require Integers.
From mathcomp Require Import ssrnat.
From Wasm Require Import datatypes list_extra.
Import ListNotations.


Inductive bb_t :=
  BB_unknown
  | BB_exit_end | BB_exit_return | BB_exit_unreachable
  | BB_unreachable 
  | BB_block | BB_loop 
  | BB_if | BB_br | BB_br_if | BB_br_table | BB_return
  | BB_code.

Definition bb_t_of_instr (i: basic_instruction): bb_t :=
  match i with
  | BI_unreachable  => BB_unreachable
  | BI_block _ _    => BB_unreachable
  | BI_loop _ _     => BB_loop
  | BI_if _ _ _     => BB_if
  | BI_br _         => BB_br
  | BI_br_if _      => BB_br_if
  | BI_br_table _ _ => BB_br_table
  | BI_return       => BB_return
  | _               => BB_code
  end.

Inductive bb : Type :=
{
  bbindex:  nat;        (* the index of this bb in the list of bblocks, makes things easier to have this *)
          start_op: nat;        (* index into e of the first op in the expr *)
(*  mutable *) end_op:   nat;        (* index+1 of the last op in the expr *)
(*  mutable *) succ:     list bb;    (* bblocks that can be directly reached from this bb *)
(*  mutable *) pred:     list bb;    (* bblocks that can directly reach this bb *)
(*  mutable *) bbtype:	 bb_t;       (* effectively the control opcode that created this bb *)
(*  mutable *) nesting:  nat;        (* nesting level of the last opcode in the bb *)
(*  mutable *) labels:   list nat;   (* destination labels used in BR, BR_IF, BR_TABLE instructions *)
(*  mutable *) br_dest:	 option bb;  (* for LOOP, BLOCK and IF instructions the bb that's the target of a branch for this instruction  *)
}.

Inductive bb': Type :=
{
  bb_index:   nat;
  bb_type:    bb_t;
  bb_nesting: nat;
  bb_instrs:  list basic_instruction;
  bb_succ:    list bb';
  bb_pred:    list bb';
}.

Record bbs_progress: Type :=
{
    p_bb:       bb';
    p_bbs:      list bb';
}.

Definition init_bb (idx: nat) (t: bb_t) (nesting: nat) (is: list basic_instruction): bb' :=
  {|  bb_index    := idx;
      bb_type     := t;
      bb_nesting  := nesting;
      bb_instrs   := is;
      bb_succ     := []; 
      bb_pred     := [] |}.

Definition empty_bb (idx: nat) (nesting: nat): bb' := init_bb idx BB_code nesting [].

(* bb's_pass1 determines bb_index, bb_type, bb_nesting, bb_instrs *)
Fixpoint bb's_pass1 (bbs_prog: bbs_progress) (i: basic_instruction): bbs_progress :=
  let bb's_pass1' (bbs_prog: bbs_progress) (e: expr): bbs_progress :=
    
    let bbs_prog' := List.fold_left bb's_pass1 e bbs_prog in
    let bb_acc    := (p_bb bbs_prog') in
    let bbs_acc   := (p_bbs bbs_prog') in
      (* did we wind up having a bb at the end?*)
      match bb_instrs bb_acc with
      (* no, we're done *)
      | [] => bbs_prog'
      (* yes, add it to the list of bbs *)
      | _ => {| p_bb  := empty_bb ((bb_index bb_acc)+1) (bb_nesting bb_acc);
                p_bbs := ((init_bb (bb_index bb_acc) BB_code (bb_nesting bb_acc) (List.rev(bb_instrs bb_acc))))::bbs_acc |}
      end
    in
    let bb_acc    := (p_bb  bbs_prog) in
    let bbs_acc   := (p_bbs bbs_prog) in
    match i with
      | BI_block b e1 =>
          let e1_p := bb's_pass1' {| p_bb := empty_bb ((bb_index bb_acc)+1) ((bb_nesting (p_bb bbs_prog))+1);
                                        p_bbs := [] |} e1 in
            {| p_bb   := empty_bb (bb_index (p_bb e1_p)) (bb_nesting bb_acc);
               p_bbs  := (p_bbs e1_p)
                          ++ (init_bb (bb_index bb_acc)
                                      BB_block
                                      (bb_nesting bb_acc)
                                      (List.rev ((BI_block b [])::(bb_instrs bb_acc))))::bbs_acc |}
      | BI_loop b e1 =>
          let e1_p := bb's_pass1' {| p_bb := empty_bb((bb_index bb_acc)+1) ((bb_nesting (p_bb bbs_prog))+1);
                                        p_bbs := [] |} e1 in
            {| p_bb   := empty_bb (bb_index (p_bb e1_p)) (bb_nesting bb_acc);
               p_bbs  := (p_bbs e1_p)
                          ++ (init_bb (bb_index bb_acc)
                                      BB_loop
                                      (bb_nesting bb_acc)
                                      (List.rev ((BI_loop b [])::(bb_instrs bb_acc))))::bbs_acc |}
      | BI_if b e1 e2 =>
          let e1_p := bb's_pass1' {| p_bb := empty_bb((bb_index bb_acc)+1) ((bb_nesting (p_bb bbs_prog))+1);
                                        p_bbs := [] |} e1 in
          let e2_p := bb's_pass1' {| p_bb := empty_bb((bb_index (p_bb e1_p))+1) ((bb_nesting (p_bb e1_p))+1);
                                        p_bbs := []  |} e1 in
            {| p_bb   := (p_bb e2_p);
               p_bbs  := (p_bbs e2_p) ++ (p_bbs e2_p)
                          ++ (init_bb (bb_index (p_bb e2_p))
                                      BB_if
                                      (bb_nesting (p_bb e2_p))
                                      (List.rev ((BI_loop b [])::(bb_instrs bb_acc))))::bbs_acc |}
    | BI_unreachable
    | BI_br _
    | BI_br_if _
    | BI_br_table _ _
    | BI_return =>
        {|  p_bb  := empty_bb ((bb_index bb_acc)+1) (bb_nesting (p_bb bbs_prog));
            p_bbs := (init_bb (bb_index bb_acc)
                              (bb_t_of_instr i)
                              (bb_nesting (p_bb bbs_prog))
                              (List.rev (i::(bb_instrs bb_acc))))::bbs_acc |}
    | _ => 
        {|  p_bb  := init_bb ((bb_index bb_acc)) BB_code (bb_nesting (p_bb bbs_prog)) (i::(bb_instrs bb_acc));
            p_bbs := bbs_acc |}
  end.

(* bb's_pass isn't really a pass, it adds the syntetic bbs to the list *)
Definition bb's_pass2 (bbs: list bb'): list bb' :=
  let i := List.length bbs in
    bbs ++ [init_bb (i) BB_exit_end         0 [];
            init_bb (i+1) BB_exit_return      0 [];
            init_bb (i+2) BB_exit_unreachable 0 []]
  .

(* bb's pass 3 determines the succ *)
Definition bb's_pass3 (bbs: list bb'): list (list nat) :=
  let idx_of_else (idx: nat) (n: nat): option nat :=
    let bbs' := sublist idx (List.length bbs - idx) bbs in
      match find (fun b => (bb_nesting b) >= n) bbs' with
      | None   => None
      | Some b => Some (bb_index b)
      end
  in
  let succ_of_bb (idx: nat) (b: bb'): list nat :=
    let is := bb_instrs b in
    match is with
    | [] => [ idx + 1]
    | _  =>
      match last_of_list is with
      | None => [ idx + 1]
      | Some i =>
        match i with
        | BI_if _ _ _ => 
            let i := idx_of_else (idx+2) (bb_nesting b) in
            match i with
            | None => [ idx + 1 ]
            | Some i => [ idx + 1; i]
            end  
        | BI_unreachable => []
        | BI_br _ => [ 0 ]
        | BI_br_if _ => [ idx + 1; 0 ]
        | BI_br_table _ _ => [ 0; 0; 0 ]
        | BI_return => []
        | _ => [ idx + 1]
        end
      end
    end
  in
  mapi succ_of_bb bbs.

Definition bb's_of_expr (e: expr): list bb' :=
  bb's_pass2 (
  let p := List.fold_left bb's_pass1 e {| p_bb := empty_bb 0 0; p_bbs := [] |}
  in
    (* did we wind up having a bb at the end?*)
    match bb_instrs (p_bb p) with
    (* no, we're done *)
    | [] => List.rev (p_bbs p)
    (* yes, add it to the list of bbs*)
    | _ => List.rev ((init_bb ((bb_index (p_bb p)))
                              BB_code
                              (bb_nesting (p_bb p))
                              (List.rev (bb_instrs (p_bb p))))::(p_bbs p))
    end).


(* The simplest basic block *)
Example simple_bb1 :
forall (v1: value_num), 
  bb's_of_expr [BI_const_num v1] 
  = bb's_pass2
      [{| bb_index := 0; bb_type := BB_code; bb_nesting := 0; bb_instrs := [BI_const_num v1]; bb_pred := []; bb_succ := []|}].
Proof.
  compute. reflexivity.
Qed.

Definition i32_of n: i32 := Wasm_int.Int32.repr n.

(* A slightly more complicated example*)
Example simple_bb2 :
forall (v1: value_num) (v2: value_num), 
  bb's_of_expr [BI_const_num v1; BI_const_num v2]
  = bb's_pass2
      [{| bb_index := 0; bb_type := BB_code; bb_nesting := 0; bb_instrs := [BI_const_num v1; BI_const_num v2]; bb_pred := []; bb_succ := [] |}].
Proof.
  reflexivity.
Qed.

(* Now examples with instructions that terminate a bb *)
Example branch_bb1 :
forall v1 v2 v3 l, 
  bb's_of_expr [BI_const_num v1; BI_const_num v2; BI_const_num v3; BI_br l]
    = bb's_pass2
      [{| bb_index := 0; bb_type := BB_br; bb_nesting := 0;
          bb_instrs := [BI_const_num v1; BI_const_num v2; BI_const_num v3; BI_br l];
          bb_pred := []; bb_succ := [] |}].
Proof.
  compute. reflexivity.
Qed.

Example branch_bb2 :
forall v1 v2 v3 l, 
  bb's_of_expr [BI_const_num v1; BI_const_num v2; BI_br l; BI_const_num v3]
  =   bb's_pass2
      [ {|  bb_index := 0; bb_type := BB_br; bb_nesting := 0;
            bb_instrs := [BI_const_num v1; BI_const_num v2; BI_br l];
            bb_pred := []; bb_succ := [] |};
        {|  bb_index := 1; bb_type := BB_code; bb_nesting := 0;
            bb_instrs := [BI_const_num v3];
            bb_pred := []; bb_succ := [] |}].
Proof.
  compute. reflexivity.
Qed.

Definition bubble_sort_expr: expr :=
[
    BI_block (BT_id 0%num) [
        BI_local_get 0%num;
        BI_const_num (VAL_int32 (i32_of 2));
        BI_relop T_i32 (Relop_i (ROI_lt SX_S));
        BI_br_if 0%num;
        BI_local_get 0%num;
        BI_const_num (VAL_int32 (i32_of (-1)));
        BI_binop T_i32 (Binop_i BOI_add);
        BI_local_tee 2%num;
        BI_local_set 3%num;
        BI_const_num (VAL_int32 (i32_of 0));
        BI_local_set 4%num;
        BI_loop  (BT_id 2%num) [
            BI_local_get 3%num;
            BI_local_set 5%num;
            BI_const_num (VAL_int32 (i32_of 0));
            BI_local_set 6%num;
            BI_block (BT_id 0%num) [
                BI_local_get 4%num;
                BI_local_tee 7%num;
                BI_local_get 0%num;
                BI_binop T_i32 (Binop_i BOI_sub);
                BI_const_num (VAL_int32 (i32_of (-2)));
                BI_relop T_i32 (Relop_i (ROI_gt SX_S));
                BI_br_if 0%num;
                BI_loop (BT_id 4%num) [
                    BI_block (BT_id 0%num) [
                        BI_local_get 1%num;
                        BI_local_get 6%num;
                        BI_local_tee 3%num;
                        BI_const_num (VAL_int32 (i32_of 2));
                        BI_binop T_i32 (Binop_i BOI_shl);
                        BI_binop T_i32 (Binop_i BOI_add);
                        BI_local_tee 6%num;
                        BI_load T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |};
                        BI_local_tee 4%num;
                        BI_local_get 1%num;
                        BI_local_get 3%num;
                        BI_const_num (VAL_int32 (i32_of 1));
                        BI_binop T_i32 (Binop_i BOI_add);
                        BI_local_tee 3%num;
                        BI_const_num (VAL_int32 (i32_of 2));
                        BI_binop T_i32 (Binop_i BOI_shl);
                        BI_binop T_i32 (Binop_i BOI_add);
                        BI_local_tee 8%num;
                        BI_load T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |};
                        BI_local_tee 9%num;
                        BI_relop T_i32 (Relop_i (ROI_le SX_S));
                        BI_br_if 0%num;
                        BI_local_get 6%num;
                        BI_local_get 9%num;
                        BI_store T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |};
                        BI_local_get 8%num;
                        BI_local_get 4%num;
                        BI_store T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |}
                    ];
                    BI_local_get 3%num;
                    BI_local_set 6%num;
                    BI_local_get 3%num;
                    BI_local_get 5%num;
                    BI_relop T_i32 (Relop_i ROI_ne);
                    BI_br_if 0%num
                ]
            ]
        ];
        BI_local_get 5%num;
        BI_const_num (VAL_int32 (i32_of (-1)));
        BI_binop T_i32 (Binop_i BOI_add);
        BI_local_set 3%num;
        BI_local_get 7%num;
        BI_const_num (VAL_int32 (i32_of 1));
        BI_binop T_i32 (Binop_i BOI_add);
        BI_local_tee 6%num;
        BI_local_set 4%num;
        BI_local_get 6%num;
        BI_local_get 2%num;
        BI_relop T_i32 (Relop_i ROI_ne);
        BI_br_if 0%num
    ]
].

Compute bb's_pass3 (bb's_of_expr bubble_sort_expr).

Definition bubble_sort_bbs: list bb' :=
[ init_bb 0 BB_block 0 [BI_block (BT_id 0%num) []];
  init_bb 1 BB_br_if 1 [BI_local_get 0%num;
          BI_const_num (VAL_int32 (i32_of 2));
          BI_relop T_i32 (Relop_i (ROI_lt SX_S));
          BI_br_if 0%num];
  init_bb 2 BB_loop 1 [BI_local_get 0%num;
          BI_const_num (VAL_int32 (i32_of (-1)));
          BI_binop T_i32 (Binop_i BOI_add);
          BI_local_tee 2%num;
          BI_local_set 3%num;
          BI_const_num (VAL_int32 (i32_of 0));
          BI_local_set 4%num;
          BI_loop (BT_id 2%num) []];
  init_bb 3 BB_block 2 [BI_local_get 3%num;
          BI_local_set 5%num;
          BI_const_num (VAL_int32 (i32_of 0));
          BI_local_set 6%num;
          BI_block (BT_id 0%num) []];
  init_bb 4 BB_br_if 3 [BI_local_get 4%num;
          BI_local_tee 7%num;
          BI_local_get 0%num;
          BI_binop T_i32 (Binop_i BOI_sub);
          BI_const_num (VAL_int32 (i32_of (-2)));
          BI_relop T_i32 (Relop_i (ROI_gt SX_S));
          BI_br_if 0%num];
  init_bb 5 BB_loop 3 [BI_loop (BT_id 4%num) []];
  init_bb 6 BB_block 4 [BI_block (BT_id 0%num) []];
  init_bb 7 BB_br_if 5 [BI_local_get 1%num;
          BI_local_get 6%num;
          BI_local_tee 3%num;
          BI_const_num (VAL_int32 (i32_of 2));
          BI_binop T_i32 (Binop_i BOI_shl);
          BI_binop T_i32 (Binop_i BOI_add);
          BI_local_tee 6%num;
          BI_load T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |};
          BI_local_tee 4%num;
          BI_local_get 1%num;
          BI_local_get 3%num;
          BI_const_num (VAL_int32 (i32_of 1));
          BI_binop T_i32 (Binop_i BOI_add);
          BI_local_tee 3%num;
          BI_const_num (VAL_int32 (i32_of 2));
          BI_binop T_i32 (Binop_i BOI_shl);
          BI_binop T_i32 (Binop_i BOI_add);
          BI_local_tee 8%num;
          BI_load T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |};
          BI_local_tee 9%num;
          BI_relop T_i32 (Relop_i (ROI_le SX_S));
          BI_br_if 0%num];
  init_bb 8 BB_code 5 [BI_local_get 6%num;
          BI_local_get 9%num;
          BI_store T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |};
          BI_local_get 8%num;
          BI_local_get 4%num;
          BI_store T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |}];
  init_bb 9 BB_br_if 4 [BI_local_get 3%num;
          BI_local_set 6%num;
          BI_local_get 3%num;
          BI_local_get 5%num;
          BI_relop T_i32 (Relop_i ROI_ne);
          BI_br_if 0%num];
  init_bb 10 BB_br_if 1 [BI_local_get 5%num;
          BI_const_num (VAL_int32 (i32_of (-1)));
          BI_binop T_i32 (Binop_i BOI_add);
          BI_local_set 3%num;
          BI_local_get 7%num;
          BI_const_num (VAL_int32 (i32_of 1));
          BI_binop T_i32 (Binop_i BOI_add);
          BI_local_tee 6%num;
          BI_local_set 4%num;
          BI_local_get 6%num;
          BI_local_get 2%num;
          BI_relop T_i32 (Relop_i ROI_ne);
          BI_br_if 0%num
    ]
].

Compute List.length bubble_sort_bbs.
Compute List.length (bb's_of_expr bubble_sort_expr).
Compute List.fold_left (fun a x => a + List.length (bb_instrs x)) bubble_sort_bbs 0.
Compute List.fold_left (fun a x => a + List.length (bb_instrs x)) (bb's_of_expr bubble_sort_expr) 0.
Compute List.map (fun x => List.length (bb_instrs x)) bubble_sort_bbs.
Compute List.map (fun x => List.length (bb_instrs x)) (bb's_of_expr bubble_sort_expr).
Compute List.map (fun x => (bb_nesting x)) bubble_sort_bbs.
Compute List.map (fun x => (bb_nesting x)) (bb's_of_expr bubble_sort_expr).

Example bubble_sort: bb's_of_expr bubble_sort_expr = bb's_pass2 bubble_sort_bbs.
Proof.
  compute. reflexivity.
Qed.

Definition bb_instr: Type := option basic_instruction.

Definition bb_instr_of_basic_instruction (i: basic_instruction): bb_instr :=
  match i with
    | BI_unreachable
    | BI_block _ _
    | BI_loop _ _
    | BI_if _ _ _
    | BI_br _
    | BI_br_if _
    | BI_br_table _ _
    | BI_return => None
    | _ => Some i
  end.

Lemma bb_instr_not_block: forall (i: basic_instruction) (b: block_type) (e: expr),
  bb_instr_of_basic_instruction i = Some i ->
  i <> BI_block b e.
Proof. intros i b e H. compute. intros E.
Admitted.

(*
Lemma bb_of_instr: forall (i: basic_instruction),
    bb_instr_of_basic_instruction i = Some i ->
    bb's_of_expr ([i]) = [(init_bb ([i]))].
Proof.
Admitted.
*)

Definition bb_is_exit (b: bb): bool :=
  match bbtype b with 
    | BB_exit_end | BB_exit_return | BB_exit_unreachable => true 
    | _ => false
  end.

Definition non_exit_bbs (bblocks: list bb): list bb :=
  List.filter (fun bblock => (orb (bb_is_exit bblock) true)) bblocks.

Definition cost_of_bb (b: bb): nat := 
  (end_op b) - (start_op b).

Definition compare_bbs (b1: bb) (b2: bb): comparison :=
  Nat.compare (bbindex b1) (bbindex b2).

Definition bb_in_bblocks (b: bb) (bbs: list bb): bool :=
  List.existsb 
    (fun b' =>
      match (bbindex b) - (bbindex b') with |0 => true |_ => false
      end
    )
    bbs.

Definition bb_not_in_bblocks (b: bb) (bbs: list bb): bool :=
  List.forallb
    (fun b' => 
      match (bbindex b) - (bbindex b') with |0 => false |_ => true
      end
    )
    bbs.
    
Definition indexes_of_bbs (bbs: list bb): list nat :=
  List.map (fun x => (bbindex x)) bbs.

Definition mult_succ_count (bbs: list bb): nat :=
  List.fold_left
    (fun a x => match (succ x) with |[] | [_] => a | _ => a+1 end)
    bbs 0.

Definition bblocks_of_expr (_: expr): list bb :=
[].

Definition expr_of_bb (e: expr) (bblock: bb): expr :=
  sublist (start_op bblock) ((end_op bblock) - (start_op bblock)) e.

(* 
val expr_of_bb        : Wm.expr -> bb -> Wm.expr
val bblocks_of_expr   : Wm.expr -> bb list
*)
