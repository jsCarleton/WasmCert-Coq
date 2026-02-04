From Coq Require Import Lia Wf_nat.
From Coq Require Import List.
From Coq Require Import BinNat Strings.Byte.
From Coq Require Import ZArith ZArith.Int ZArith.BinInt ZArith.Zpower.
From Coq Require Import Bool.Bool.

Require Import Coq.Program.Program.
From compcert Require Integers.
From mathcomp Require Import ssrnat.

From Wasm Require Import datatypes list_extra.
Import ListNotations.

Definition is_body_instr (bi : basic_instruction) : bool := 
  match bi with
  (* instructions that can be in the body of a basic block*)
  | BI_const_num _
  | BI_unop _ _
  | BI_binop _ _
  | BI_testop _ _
  | BI_relop _ _
  | BI_cvtop _ _ _ _
  | BI_const_vec _
  | BI_vunop _
  | BI_vbinop _
  | BI_vternop _
  | BI_vtestop _
  | BI_vshiftop _
  | BI_splat_vec _
  | BI_extract_vec _ _ _
  | BI_replace_vec _ _
  | BI_ref_null _
  | BI_ref_is_null
  | BI_ref_func _
  | BI_drop
  | BI_select _
  | BI_local_get _
  | BI_local_set _
  | BI_local_tee _
  | BI_global_get _
  | BI_global_set _
  | BI_table_get _
  | BI_table_set _
  | BI_table_size _
  | BI_table_grow _
  | BI_table_fill _
  | BI_table_copy _ _
  | BI_table_init _ _
  | BI_elem_drop _
  | BI_load _ _ _
  | BI_load_vec _ _
  | BI_load_vec_lane _ _ _
  | BI_store _ _ _
  | BI_store_vec _
  | BI_store_vec_lane _ _ _
  | BI_memory_size
  | BI_memory_grow
  | BI_memory_fill
  | BI_memory_copy
  | BI_memory_init _
  | BI_data_drop _
  | BI_nop                      => true                   
  (* instructions that terminate a basic block *)
  | BI_unreachable
  | BI_block _ _
  | BI_loop _ _
  | BI_if _ _ _
  | BI_br _
  | BI_br_if _
  | BI_br_table _ _
  | BI_return                   => false
  | BI_call _  (* later, when we implement full program analysis, call and call_indirect will terminate a bb *)
  | BI_call_indirect _ _        => true
  | BI_return_call _
  | BI_return_call_indirect _ _ => false                                          
  end.

  Record bb: Type :=
  {
    bb_instrs:      list basic_instruction;     (* body of bb *)
    bb_term_instr:  option basic_instruction;   (* branching instr that terminates bb *)

    bb_instrs_constraint:
    forall i : basic_instruction, 
        In i bb_instrs -> is_body_instr i = true;
    bb_term_constraint:
    forall i : basic_instruction, 
        bb_term_instr = Some i -> is_body_instr i = false;
  }.

Program Definition empty_bb 
    : bb :=
  {| bb_instrs      := [];
     bb_term_instr  := None |}.

Program Definition add_body_i
    (i : basic_instruction)
    (b : bb)
    (H : is_body_instr i = true) 
    : bb :=
  {|
    bb_instrs     := i :: bb_instrs b;
    bb_term_instr := bb_term_instr b
  |}.
  Next Obligation.
    destruct H0.
    - rewrite H0 in H. assumption.
    - apply bb_instrs_constraint in H0. assumption.
  Qed.
  Next Obligation.
    apply bb_term_constraint in H0. assumption.
  Qed.

Program Definition rev_body
    (b : bb)
    : bb :=
  {|
      bb_instrs := rev (bb_instrs b);
      bb_term_instr := bb_term_instr b
  |}.
  Next Obligation.
    apply in_rev in H. 
    apply bb_instrs_constraint in H.
    assumption.
  Qed.
  Next Obligation.
    apply bb_term_constraint in H.
    assumption.
  Qed.

Program Definition close_block 
    (i : basic_instruction)
    (b : bb) 
    (H : is_body_instr i = false)
    : bb :=
    rev_body
    {|
      bb_instrs := bb_instrs b;
      bb_term_instr := Some i
    |}.
  Next Obligation.
    apply bb_instrs_constraint in H0. assumption.
  Qed.

(* This is an attempt at converting an [expr] into a [list bb]
    that recurses on each instruction in the [expr].
    This approach is a dead-end since handling BI_loop, BI_block and
    BI_if correctly requires recursion on bbs_of_expr' that
    Rocq can't determine 
    The passing test cases below don't have any of these instructions.
    The bubble sort test case does and this approach can't pass that
    test case *)
Program Fixpoint bbs_of_expr'
    (e    : list basic_instruction)
    (bbs  : list bb)
    (b    : bb)
    : list bb :=
  match e with
  | []  =>
    match bb_instrs b with
    | [] => bbs
    | _  => (rev_body b)::bbs
    end
  | i::e' =>
      match is_body_instr i with
      | true =>   bbs_of_expr' e' bbs (add_body_i i b _)
      (* the next line of code has to handle BI_loop, BI_block,
          BI_if correctly *)
      | false => (close_block i b _) :: bbs_of_expr' e' bbs empty_bb
      end
  end.

Definition bbs_of_expr (e: expr): list bb := bbs_of_expr' e [] empty_bb.


Definition bb_bodies (bbs: list bb): list (list basic_instruction) :=
  map (fun x => bb_instrs x) bbs.

Definition bb_terms (bbs: list bb): list (option basic_instruction) :=
  map (fun x => bb_term_instr x) bbs.

(* a bb with 1 instruction *)
Example bb_test1 :
forall (v1: value_num), 
      bb_bodies (bbs_of_expr [BI_const_num v1]) = [[BI_const_num v1]]
  /\  bb_terms (bbs_of_expr [BI_const_num v1]) = [None].
Proof. split; reflexivity.
Qed.

(* a bb with a body and term instruction *)
Example bb_test2 :
forall (v1: value_num), 
      bb_bodies (bbs_of_expr [BI_const_num v1; BI_return]) = [[BI_const_num v1]]
  /\  bb_terms (bbs_of_expr [BI_const_num v1; BI_return]) = [Some BI_return].
Proof. split; reflexivity.
Qed.

(* a bb with 2 body instructions *)
Example bb_test3 :
forall (v1 v2: value_num), 
      bb_bodies (bbs_of_expr [BI_const_num v1; BI_const_num v2]) = [[BI_const_num v1; BI_const_num v2]]
  /\  bb_terms (bbs_of_expr [BI_const_num v1; BI_const_num v2]) = [None].
Proof. split; reflexivity.
Qed.

(* an example with 2 bbs *)
Example bb_test4 :
forall (v1 v2: value_num), 
      bb_bodies (bbs_of_expr
        [BI_const_num v1; BI_return; BI_const_num v2; BI_return])
            = [[BI_const_num v1]; [BI_const_num v2]]
  /\  bb_terms (bbs_of_expr 
        [BI_const_num v1; BI_return; BI_const_num v2; BI_return]) 
            = [Some BI_return; Some BI_return].
Proof. split; reflexivity.
Qed.

(* Now examples with instructions that terminate a bb *)
Example bb_test5 :
forall v1 v2 v3 l, 
      bb_bodies (bbs_of_expr
        [BI_const_num v1; BI_const_num v2; BI_const_num v3; BI_br l])
            = [[BI_const_num v1; BI_const_num v2; BI_const_num v3]]
  /\  bb_terms (bbs_of_expr 
        [BI_const_num v1; BI_const_num v2; BI_const_num v3; BI_br l])
            = [Some (BI_br l)].
Proof. split; reflexivity.
Qed.

Example bb_test6 :
forall v1 v2 v3 l, 
      bb_bodies (bbs_of_expr
        [BI_const_num v1; BI_const_num v2; BI_br l; BI_const_num v3])
            = [[BI_const_num v1; BI_const_num v2]; [BI_const_num v3]]
  /\  bb_terms (bbs_of_expr 
        [BI_const_num v1; BI_const_num v2; BI_br l; BI_const_num v3])
            = [Some (BI_br l); None].
Proof. split; reflexivity.
Qed.

Example bb_test7 :
forall v1 v2 v3 l1 l2, 
      bb_bodies (bbs_of_expr
        [BI_const_num v1; BI_const_num v2; BI_br l1; BI_const_num v3; BI_br l1])
            = [[BI_const_num v1; BI_const_num v2]; [BI_const_num v3]]
  /\  bb_terms (bbs_of_expr 
        [BI_const_num v1; BI_const_num v2; BI_br l1; BI_const_num v3; BI_br l2])
            = [Some (BI_br l1); Some (BI_br l2)].
Proof. split; reflexivity.
Qed.

(* To resolve the recursion termination of the code above, we use
    [fold_left] to process the [expr]. This way there's no explicit
    recursion on the [expr] in the function that processes each instruction.
    Rocq allows recursion in the BI_loop, BI_block and BI_if cases *)

(* Since the function that we provide to [fold_left] operates on a single
    instruction at a time it's output is an in-progress [bb] and [list bb].
*)
Record bbs_progress: Type :=
{
    p_bb:       bb;
    p_bbs:      list bb;
}.

(* This is the function that we provide to [fold_left] *)
Program Fixpoint bbs_pass1 
    (bbs_prog: bbs_progress) 
    (i: basic_instruction)
    : bbs_progress :=

  let bbs_pass1' (bbs_prog: bbs_progress) (e: expr): bbs_progress :=
    let bbs_prog' := List.fold_left bbs_pass1 e bbs_prog in
    let bb_acc    := (p_bb bbs_prog') in
    let bbs_acc   := (p_bbs bbs_prog') in
      (* did we wind up having a bb at the end?*)
      match bb_instrs bb_acc with
      (* no, we're done *)
      | [] => bbs_prog' 
      (* yes, add it to the list of bbs *)
      | _ =>  {|  p_bb  := empty_bb; p_bbs := (rev_body bb_acc)::bbs_acc
              |}
      end
  in

    (* bbs_pass1 starts here *)
    let bb_acc    := (p_bb  bbs_prog) in
    let bbs_acc   := (p_bbs bbs_prog) in
    match is_body_instr i with
    | true => {|  p_bb  := add_body_i i bb_acc _;
                  p_bbs := bbs_acc |}
    | false =>
      match i with
      | BI_block b1 e1 =>
          let e1_p := bbs_pass1' {| p_bb := empty_bb; p_bbs := [] |} e1 in
            {| p_bb   := empty_bb;
              p_bbs  := (p_bbs e1_p)
                          ++ (close_block (BI_block b1 []) bb_acc _)::bbs_acc |}
      | BI_loop b1 e1 =>
          let e1_p := bbs_pass1' {| p_bb := empty_bb; p_bbs := [] |} e1 in
            {| p_bb   := empty_bb;
              p_bbs  := (p_bbs e1_p)
                          ++ (close_block (BI_loop b1 []) bb_acc _)::bbs_acc |}
      | BI_if b1 e1 e2 =>
          let e1_p := bbs_pass1' {| p_bb := empty_bb;
                                        p_bbs := [] |} e1 in
          let e2_p := bbs_pass1' {| p_bb := empty_bb;
                                        p_bbs := []  |} e2 in
            {| p_bb   := empty_bb;
               p_bbs  := (p_bbs e2_p) ++ (p_bbs e1_p)
                          ++ (close_block (BI_if b1 [] []) bb_acc _)::bbs_acc |}
      | _ =>
           {| p_bb  := empty_bb;
              p_bbs := (close_block i bb_acc _)::bbs_acc |}
    end
  end.
Solve All Obligations with (split; try discriminate; split; try discriminate).

Definition bbs_of_expr'' (e: expr): list bb :=
  let p := List.fold_left
              bbs_pass1
              e
              {| p_bb := empty_bb; p_bbs := [] |}
  in
    (* did we wind up having a bb at the end?*)
    match bb_instrs (p_bb p) with
    (* no, we're done *)
    | [] => rev (p_bbs p)
    (* yes, add it to the list of bbs *)
    | _ =>  rev ((rev_body (p_bb p))::(p_bbs p))
    end.

(* a bb with 1 instruction *)
Example bb_test1' :
forall (v1: value_num), 
      bb_bodies (bbs_of_expr'' [BI_const_num v1]) = [[BI_const_num v1]]
  /\  bb_terms (bbs_of_expr'' [BI_const_num v1]) = [None].
Proof. split; reflexivity.
Qed.

(* a bb with a body and term instruction *)
Example bb_test2' :
forall (v1: value_num), 
      bb_bodies (bbs_of_expr'' [BI_const_num v1; BI_return]) = [[BI_const_num v1]]
  /\  bb_terms (bbs_of_expr'' [BI_const_num v1; BI_return]) = [Some BI_return].
Proof. split; reflexivity.
Qed.

(* a bb with 2 body instructions *)
Example bb_test3' :
forall (v1 v2: value_num), 
      bb_bodies (bbs_of_expr'' [BI_const_num v1; BI_const_num v2]) = [[BI_const_num v1; BI_const_num v2]]
  /\  bb_terms (bbs_of_expr'' [BI_const_num v1; BI_const_num v2]) = [None].
Proof. split; reflexivity.
Qed.

Definition i32_of n: i32 := Wasm_int.Int32.repr n.

Definition v1: value_num := VAL_int32 (i32_of 1).
Definition v2: value_num := VAL_int32 (i32_of 2).

Compute bb_bodies (bbs_of_expr''
        [BI_const_num v1; BI_return; BI_const_num v2; BI_return]).

        
(* an example with 2 bbs *)
Example bb_test4' :
forall (v1 v2: value_num), 
      bb_bodies (bbs_of_expr''
        [BI_const_num v1; BI_return; BI_const_num v2; BI_return])
            = [[BI_const_num v1]; [BI_const_num v2]]
  /\  bb_terms (bbs_of_expr'' 
        [BI_const_num v1; BI_return; BI_const_num v2; BI_return]) 
            = [Some BI_return; Some BI_return].
Proof. split; reflexivity.
Qed.

(* Now examples with instructions that terminate a bb *)
Example bb_test5' :
forall v1 v2 v3 l, 
      bb_bodies (bbs_of_expr''
        [BI_const_num v1; BI_const_num v2; BI_const_num v3; BI_br l])
            = [[BI_const_num v1; BI_const_num v2; BI_const_num v3]]
  /\  bb_terms (bbs_of_expr'' 
        [BI_const_num v1; BI_const_num v2; BI_const_num v3; BI_br l])
            = [Some (BI_br l)].
Proof. split; reflexivity.
Qed.

Example bb_test6' :
forall v1 v2 v3 l, 
      bb_bodies (bbs_of_expr''
        [BI_const_num v1; BI_const_num v2; BI_br l; BI_const_num v3])
            = [[BI_const_num v1; BI_const_num v2]; [BI_const_num v3]]
  /\  bb_terms (bbs_of_expr'' 
        [BI_const_num v1; BI_const_num v2; BI_br l; BI_const_num v3])
            = [Some (BI_br l); None].
Proof. split; reflexivity.
Qed.

Example bb_test7' :
forall v1 v2 v3 l1 l2, 
      bb_bodies (bbs_of_expr''
        [BI_const_num v1; BI_const_num v2; BI_br l1; BI_const_num v3; BI_br l1])
            = [[BI_const_num v1; BI_const_num v2]; [BI_const_num v3]]
  /\  bb_terms (bbs_of_expr'' 
        [BI_const_num v1; BI_const_num v2; BI_br l1; BI_const_num v3; BI_br l2])
            = [Some (BI_br l1); Some (BI_br l2)].
Proof. split; reflexivity.
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

Definition bubble_sort_bodies: list expr :=
[
    [];
    [   BI_local_get 0%num;
        BI_const_num (VAL_int32 (i32_of 2));
        BI_relop T_i32 (Relop_i (ROI_lt SX_S))];
    [   BI_local_get 0%num;
        BI_const_num (VAL_int32 (i32_of (-1)));
        BI_binop T_i32 (Binop_i BOI_add);
        BI_local_tee 2%num;
        BI_local_set 3%num;
        BI_const_num (VAL_int32 (i32_of 0));
        BI_local_set 4%num];
    [       BI_local_get 3%num;
            BI_local_set 5%num;
            BI_const_num (VAL_int32 (i32_of 0));
            BI_local_set 6%num];
    [           BI_local_get 4%num;
                BI_local_tee 7%num;
                BI_local_get 0%num;
                BI_binop T_i32 (Binop_i BOI_sub);
                BI_const_num (VAL_int32 (i32_of (-2)));
                BI_relop T_i32 (Relop_i (ROI_gt SX_S))];
                [];
                [];
    [                   BI_local_get 1%num;
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
                        BI_relop T_i32 (Relop_i (ROI_le SX_S))];
      [                 BI_local_get 6%num;
                        BI_local_get 9%num;
                        BI_store T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |};
                        BI_local_get 8%num;
                        BI_local_get 4%num;
                        BI_store T_i32 None {| memarg_offset := 0%num;  memarg_align := 0%num |}];
      [             BI_local_get 3%num;
                    BI_local_set 6%num;
                    BI_local_get 3%num;
                    BI_local_get 5%num;
                    BI_relop T_i32 (Relop_i ROI_ne)];
      [ BI_local_get 5%num;
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
        BI_relop T_i32 (Relop_i ROI_ne)]
].

Definition bubble_sort_terms: list (option basic_instruction) :=
[
    Some (BI_block (BT_id 0%num) []);
    Some (BI_br_if 0%num);
    Some (BI_loop  (BT_id 2%num) []);
    Some (BI_block (BT_id 0%num) []);
    Some (BI_br_if 0%num);
    Some (BI_loop (BT_id 4%num) []);
    Some (BI_block (BT_id 0%num) []);
    Some (BI_br_if 0%num);
    None;
    Some (BI_br_if 0%num);
    Some (BI_br_if 0%num)
].

(* Examples based on basic blocks code *)
Example bb_test8' :
  bb_terms (bbs_of_expr'' bubble_sort_expr)
    = bubble_sort_terms.
Proof. reflexivity.
Qed.

Example bb_test9' :
  bb_bodies (bbs_of_expr'' bubble_sort_expr)
    = bubble_sort_bodies.
Proof. reflexivity.
Qed.

(* basic block - bb *)
(* Record bb: Type :=
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
 *)