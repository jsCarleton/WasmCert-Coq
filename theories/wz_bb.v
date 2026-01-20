From Coq Require Import Lia Wf_nat.
From Coq Require Import List.
From Coq Require Import BinNat Strings.Byte.
From Coq Require Import ZArith ZArith.Int ZArith.BinInt ZArith.Zpower.
From compcert Require Integers.
From mathcomp Require Import ssrnat.
From Wasm Require Import datatypes list_extra.
Import ListNotations.

Local Open Scope bool_scope.
(* 
Inductive bb_instr_type :=
  | BB_it_body
  | BB_it_term.

Definition bb_instr_type_of_bi (i: basic_instruction): bb_instr_type :=
  match i with
  | BI_unreachable
  | BI_block _ _
  | BI_loop _ _
  | BI_if _ _ _
  | BI_br _
  | BI_br_if _
  | BI_br_table _ _
  | BI_return         => BB_it_term
  | _                 => BB_it_body
  end.

Fixpoint is_bb_expr (is: list basic_instruction): bool :=
  match is with
  | [] => true
  | x::xa => land (bb_instr_type_of_bi x) = BB_it_body
  end.
 *)  
Inductive bb_t :=
  | BB_exit_end | BB_exit_return | BB_exit_unreachable
  | BB_block | BB_loop 
  | BB_if 
  | BB_br : labelidx -> bb_t
  | BB_br_if : labelidx -> bb_t
  | BB_br_table : list labelidx -> labelidx -> bb_t
  | BB_unreachable | BB_return
  | BB_code.

Definition bb_t_of_instr (i: basic_instruction): bb_t :=
  match i with
  | BI_unreachable    => BB_unreachable
  | BI_block _ _      => BB_unreachable
  | BI_loop _ _       => BB_loop
  | BI_if _ _ _       => BB_if
  | BI_br i           => BB_br i
  | BI_br_if i        => BB_br_if i
  | BI_br_table is i  => BB_br_table is i
  | BI_return         => BB_return
  | _                 => BB_code
  end.

(* basic block - bb *)
Record bb: Type :=
{
  bb_index:   nat;          (* the index of this bb in the list of bblocks *)
  bb_instrs:  list basic_instruction; (* code of the bb *)
  bb_type:    bb_t;         (* effectively the control opcode that created this bb *)
  bb_nesting: nat;          (* nesting level of the last opcode in the bb *)
  bb_labels:  list labelidx;(* destination labels used in BR, BR_IF, BR_TABLE instructions *)
  bb_succ:    list nat;     (* bbs that can be directly reached from this bb *)
  bb_pred:    list nat;     (* bbs that can directly reach this bb *)
  bb_br_dest: option nat;   (* for LOOP, BLOCK and IF instructions the bb that's the target 
                                of a branch for this instruction  *)
}.

Record bbs_progress: Type :=
{
    p_bb:       bb;
    p_bbs:      list bb;
}.

Definition init_bb (idx: nat) (t: bb_t) (nesting: nat) (labels: list labelidx)
             (is: list basic_instruction): bb :=
  {|  bb_index    := idx;
      bb_type     := t;
      bb_nesting  := nesting;
      bb_instrs   := is;
      bb_labels   := labels;
      bb_succ     := []; 
      bb_pred     := [];
      bb_br_dest  := None |}.

Definition bb_with_br_dest  (i: nat) (b: bb): bb :=
  {|  bb_index    := bb_index b;
      bb_type     := bb_type b;
      bb_nesting  := bb_nesting b;
      bb_instrs   := bb_instrs b;
      bb_labels   := bb_labels b;
      bb_succ     := bb_succ b; 
      bb_pred     := bb_pred b;
      bb_br_dest  := Some i |}.
  

Definition empty_bb (idx: nat) (nesting: nat): bb := init_bb idx BB_code nesting [] [].

(* bbs_pass1 determines bb_index, bb_type, bb_nesting, bb_instrs *)
Fixpoint bbs_pass1 (bbs_prog: bbs_progress) (i: basic_instruction): bbs_progress :=
  let bbs_pass1' (bbs_prog: bbs_progress) (e: expr): bbs_progress :=
    
    let bbs_prog' := List.fold_left bbs_pass1 e bbs_prog in
    let bb_acc    := (p_bb bbs_prog') in
    let bbs_acc   := (p_bbs bbs_prog') in
      (* did we wind up having a bb at the end?*)
      match bb_instrs bb_acc with
      (* no, we're done *)
      | [] => bbs_prog'
      (* yes, add it to the list of bbs *)
      | _ => {| p_bb  := empty_bb ((bb_index bb_acc)+1) (bb_nesting bb_acc);
                p_bbs := ((init_bb (bb_index bb_acc) BB_code (bb_nesting bb_acc) [] (List.rev(bb_instrs bb_acc))))::bbs_acc |}
      end
    in
    let bb_acc    := (p_bb  bbs_prog) in
    let bbs_acc   := (p_bbs bbs_prog) in
    match i with
      | BI_block b e1 =>
          let e1_p := bbs_pass1' {| p_bb := empty_bb ((bb_index bb_acc)+1) ((bb_nesting (p_bb bbs_prog))+1);
                                        p_bbs := [] |} e1 in
            {| p_bb   := empty_bb (bb_index (p_bb e1_p)) (bb_nesting bb_acc);
               p_bbs  := (p_bbs e1_p)
                          ++ (init_bb (bb_index bb_acc)
                                      BB_block
                                      (bb_nesting bb_acc)
                                      []
                                      (List.rev ((BI_block b [])::(bb_instrs bb_acc))))::bbs_acc |}
      | BI_loop b e1 =>
          let e1_p := bbs_pass1' {| p_bb := empty_bb((bb_index bb_acc)+1) ((bb_nesting (p_bb bbs_prog))+1);
                                        p_bbs := [] |} e1 in
            {| p_bb   := empty_bb (bb_index (p_bb e1_p)) (bb_nesting bb_acc);
               p_bbs  := (p_bbs e1_p)
                          ++ (init_bb (bb_index bb_acc)
                                      BB_loop
                                      (bb_nesting bb_acc)
                                      []
                                      (List.rev ((BI_loop b [])::(bb_instrs bb_acc))))::bbs_acc |}
      | BI_if b e1 e2 =>
          let e1_p := bbs_pass1' {| p_bb := empty_bb((bb_index bb_acc)+1) ((bb_nesting (p_bb bbs_prog))+1);
                                        p_bbs := [] |} e1 in
          let e2_p := bbs_pass1' {| p_bb := empty_bb((bb_index (p_bb e1_p))+1) ((bb_nesting (p_bb e1_p))+1);
                                        p_bbs := []  |} e1 in
            {| p_bb   := (p_bb e2_p);
               p_bbs  := (p_bbs e2_p) ++ (p_bbs e2_p)
                          ++ (init_bb (bb_index (p_bb e2_p))
                                      BB_if
                                      (bb_nesting (p_bb e2_p))
                                      []
                                      (List.rev ((BI_loop b [])::(bb_instrs bb_acc))))::bbs_acc |}
    | BI_unreachable
    | BI_return =>
        {|  p_bb  := empty_bb ((bb_index bb_acc)+1) (bb_nesting (p_bb bbs_prog));
            p_bbs := (init_bb (bb_index bb_acc)
                              (bb_t_of_instr i)
                              (bb_nesting (p_bb bbs_prog))
                              []
                              (List.rev (i::(bb_instrs bb_acc))))::bbs_acc |}
    | BI_br idx
    | BI_br_if idx =>
        {|  p_bb  := empty_bb ((bb_index bb_acc)+1) (bb_nesting (p_bb bbs_prog));
            p_bbs := (init_bb (bb_index bb_acc)
                              (bb_t_of_instr i)
                              (bb_nesting (p_bb bbs_prog))
                              [idx]
                              (List.rev (i::(bb_instrs bb_acc))))::bbs_acc |}
    | BI_br_table is _ =>
        {|  p_bb  := empty_bb ((bb_index bb_acc)+1) (bb_nesting (p_bb bbs_prog));
            p_bbs := (init_bb (bb_index bb_acc)
                              (bb_t_of_instr i)
                              (bb_nesting (p_bb bbs_prog))
                              is
                              (List.rev (i::(bb_instrs bb_acc))))::bbs_acc |}
    | _ => 
        {|  p_bb  := init_bb ((bb_index bb_acc)) BB_code (bb_nesting (p_bb bbs_prog)) [] (i::(bb_instrs bb_acc));
            p_bbs := bbs_acc |}
  end.

(* bbs_pass2 isn't really a pass, it adds the synthetic bbs to the list *)
Definition bbs_pass2 (bbs: list bb): list bb :=
  let i := List.length bbs in
    bbs ++ [init_bb (i)   BB_exit_end         0 [] [];
            init_bb (i+1) BB_exit_return      0 [] [];
            init_bb (i+2) BB_exit_unreachable 0 [] []]
  .

(* bbs_pass3 determines bb_br_dest *)
Definition bbs_pass3 (bbs: list bb): list bb :=
  let bbs_pass3' (b: bb) :=
    match bb_type b with
    | BB_loop   => bb_with_br_dest ((bb_index b) + 1) b
    | BB_block 
    | BB_if     => 
        match find
          (fun b' => ((bb_index b') > (bb_index b)) && ((bb_nesting b') <= (bb_nesting b)))
          bbs with
        | Some b' => bb_with_br_dest (bb_index b') b
        | None    => bb_with_br_dest (List.length bbs) b
        end
    | _ => b
    end
    in
  List.map bbs_pass3' bbs.

(* bbs_pass_4 determines the succ *)
Definition bbs_pass4 (bbs: list bb): list (list nat) :=
  let idx_of_else (idx: nat) (n: nat): option nat :=
    let bbs' := sublist idx (List.length bbs - idx) bbs in
      match find (fun b => (bb_nesting b) >= n) bbs' with
      | None   => None
      | Some b => Some (bb_index b)
      end
  in
  let succ_of_bb (idx: nat) (b: bb): list nat :=
    match bb_type b with
    | BB_exit_end
    | BB_exit_return
    | BB_exit_unreachable => []
    | BB_unreachable      => [(List.length bbs) + 2]
    | BB_block
    | BB_loop             
    | BB_code             => [(bb_index b) + 1]
    | BB_if               =>
        let i := idx_of_else (idx+2) (bb_nesting b) in
        match i with
        | None => [ idx + 1 ]
        | Some i => [ idx + 1; i]
        end  
    | BB_br _             => [ 0 ]
    | BB_br_if _          => [ idx + 1; 0 ]
    | BB_br_table _ _     => [ 0; 0; 0 ]
    | BB_return           => [(List.length bbs) + 2]
    end
  in
  mapi succ_of_bb bbs.

Definition bbs_of_expr (e: expr): list bb :=
  bbs_pass3 (
  bbs_pass2 (
  let p := List.fold_left bbs_pass1 e {| p_bb := empty_bb 0 0; p_bbs := [] |}
  in
    (* did we wind up having a bb at the end?*)
    match bb_instrs (p_bb p) with
    (* no, we're done *)
    | [] => List.rev (p_bbs p)
    (* yes, add it to the list of bbs*)
    | _ => List.rev ((init_bb ((bb_index (p_bb p)))
                              BB_code
                              (bb_nesting (p_bb p))
                              []
                              (List.rev (bb_instrs (p_bb p))))::(p_bbs p))
    end)).

(* The simplest basic block *)
Example simple_bb1 :
forall (v1: value_num), 
  bbs_of_expr [BI_const_num v1] 
  = bbs_pass2 [(init_bb 0 BB_code 0 [] [BI_const_num v1])].
Proof. reflexivity.
Qed.

Definition i32_of n: i32 := Wasm_int.Int32.repr n.

(* A slightly more complicated example*)
Example simple_bb2 :
forall (v1: value_num) (v2: value_num), 
  bbs_of_expr [BI_const_num v1; BI_const_num v2]
  = bbs_pass2
      [init_bb 0 BB_code 0 [] [BI_const_num v1; BI_const_num v2]].
Proof. reflexivity.
Qed.

(* Now examples with instructions that terminate a bb *)
Example branch_bb1 :
forall v1 v2 v3 l, 
  bbs_of_expr [BI_const_num v1; BI_const_num v2; BI_const_num v3; BI_br l]
    = bbs_pass2
      [init_bb 0 (BB_br l) 0 [l] [BI_const_num v1; BI_const_num v2; BI_const_num v3; BI_br l]].
Proof. reflexivity.
Qed.

Example branch_bb2 :
forall v1 v2 v3 l, 
  bbs_of_expr [BI_const_num v1; BI_const_num v2; BI_br l; BI_const_num v3]
  =   bbs_pass2
      [ init_bb 0 (BB_br l) 0 [l] [BI_const_num v1; BI_const_num v2; BI_br l];
        init_bb 1 BB_code 0 [] [BI_const_num v3]].
Proof. reflexivity.
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

Compute bbs_pass4 (bbs_of_expr bubble_sort_expr).

Definition bubble_sort_bbs: list bb :=
[ bb_with_br_dest 11 (init_bb 0 BB_block 0 [] [BI_block (BT_id 0%num) []]);
  init_bb 1 (BB_br_if 0%num) 1 [0%num] [BI_local_get 0%num;
          BI_const_num (VAL_int32 (i32_of 2));
          BI_relop T_i32 (Relop_i (ROI_lt SX_S));
          BI_br_if 0%num];
  bb_with_br_dest 3 (init_bb 2 BB_loop 1 [] [BI_local_get 0%num;
          BI_const_num (VAL_int32 (i32_of (-1)));
          BI_binop T_i32 (Binop_i BOI_add);
          BI_local_tee 2%num;
          BI_local_set 3%num;
          BI_const_num (VAL_int32 (i32_of 0));
          BI_local_set 4%num;
          BI_loop (BT_id 2%num) []]);
  bb_with_br_dest 10 (init_bb 3 BB_block 2 [] [BI_local_get 3%num;
          BI_local_set 5%num;
          BI_const_num (VAL_int32 (i32_of 0));
          BI_local_set 6%num;
          BI_block (BT_id 0%num) []]);
  init_bb 4 (BB_br_if 0%num) 3 [0%num] [BI_local_get 4%num;
          BI_local_tee 7%num;
          BI_local_get 0%num;
          BI_binop T_i32 (Binop_i BOI_sub);
          BI_const_num (VAL_int32 (i32_of (-2)));
          BI_relop T_i32 (Relop_i (ROI_gt SX_S));
          BI_br_if 0%num];
  bb_with_br_dest 6 (init_bb 5 BB_loop 3 [] [BI_loop (BT_id 4%num) []]);
  bb_with_br_dest 9 (init_bb 6 BB_block 4 [] [BI_block (BT_id 0%num) []]);
  init_bb 7 (BB_br_if 0%num) 5 [0%num] [BI_local_get 1%num;
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
  init_bb 8 BB_code 5 [] [BI_local_get 6%num;
          BI_local_get 9%num;
          BI_store T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |};
          BI_local_get 8%num;
          BI_local_get 4%num;
          BI_store T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |}];
  init_bb 9 (BB_br_if 0%num) 4 [0%num] [BI_local_get 3%num;
          BI_local_set 6%num;
          BI_local_get 3%num;
          BI_local_get 5%num;
          BI_relop T_i32 (Relop_i ROI_ne);
          BI_br_if 0%num];
  init_bb 10 (BB_br_if 0%num) 1 [0%num] [BI_local_get 5%num;
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
Compute List.length (bbs_of_expr bubble_sort_expr).
Compute List.fold_left (fun a x => a + List.length (bb_instrs x)) bubble_sort_bbs 0.
Compute List.fold_left (fun a x => a + List.length (bb_instrs x)) (bbs_of_expr bubble_sort_expr) 0.
Compute List.map (fun x => List.length (bb_instrs x)) bubble_sort_bbs.
Compute List.map (fun x => List.length (bb_instrs x)) (bbs_of_expr bubble_sort_expr).
Compute List.map (fun x => (bb_nesting x)) bubble_sort_bbs.
Compute List.map (fun x => (bb_nesting x)) (bbs_of_expr bubble_sort_expr).
Compute List.map (fun x => (bb_br_dest x)) (bbs_pass2 bubble_sort_bbs).
Compute List.map (fun x => (bb_br_dest x)) (bbs_of_expr bubble_sort_expr).

Example bubble_sort: bbs_of_expr bubble_sort_expr = bbs_pass2 bubble_sort_bbs.
Proof. reflexivity.
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

Definition bb_is_exit (b: bb): bool :=
  match bb_type b with 
    | BB_exit_end | BB_exit_return | BB_exit_unreachable => true 
    | _ => false
  end.

Definition non_exit_bbs (bblocks: list bb): list bb :=
  List.filter (fun bblock => (orb (bb_is_exit bblock) true)) bblocks.

Definition cost_of_bb (b: bb): nat := List.length (bb_instrs b).

Definition compare_bbs (b1: bb) (b2: bb): comparison :=
  Nat.compare (bb_index b1) (bb_index b2).

Definition bb_in_bblocks (b: bb) (bbs: list bb): bool :=
  List.existsb 
    (fun b' =>
      match (bb_index b) - (bb_index b') with |0 => true |_ => false
      end
    )
    bbs.

Definition bb_not_in_bblocks (b: bb) (bbs: list bb): bool :=
  List.forallb
    (fun b' => 
      match (bb_index b) - (bb_index b') with |0 => false |_ => true
      end
    )
    bbs.
    
Definition indexes_of_bbs (bbs: list bb): list nat :=
  List.map (fun x => (bb_index x)) bbs.

Definition mult_succ_count (bbs: list bb): nat :=
  List.fold_left
    (fun a x => match (bb_succ x) with |[] | [_] => a | _ => a+1 end)
    bbs 0.

Definition expr_of_bb (b: bb): expr := bb_instrs b.
