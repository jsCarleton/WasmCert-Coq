From Coq Require Import Lia Wf_nat.
From Coq Require Import List.
From Wasm Require Import datatypes list_extra.

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

Inductive bb': Type :=
{ 
  bb_instrs:   list basic_instruction;
  bb_succ:     list bb';
  bb_pred:     list bb';
}.

Definition init_bb (is: list basic_instruction): bb' :=
  {| bb_instrs := is; bb_succ := nil; bb_pred := nil; |}.
Definition empty_bb: bb' := init_bb nil.

Fixpoint bb's_of_expr' (acc: bb'*list bb') (i: basic_instruction): bb'*list bb' :=
  let bb's_of_expr'' (e: expr) (acc: bb'*list bb') : bb'*list bb' :=
    List.fold_left bb's_of_expr' e acc
  in
    match i with
      | BI_block _ e1
      | BI_loop _ e1 =>
          let e1_acc := bb's_of_expr'' e1 (empty_bb, nil) in
            (empty_bb,
              (snd e1_acc) 
              ++ (init_bb (List.rev (bb_instrs (fst acc)))::(snd acc)))
      | BI_if _ e1 e2 =>
          let e2_acc := bb's_of_expr'' e2 (empty_bb, nil) in
          let e1_acc := bb's_of_expr'' e1 (empty_bb, nil) in
            (empty_bb,
              (snd e2_acc)
              ++ (snd e1_acc) 
              ++ (init_bb (List.rev (bb_instrs (fst acc)))::(snd acc)))
    | BI_unreachable
    | BI_br _
    | BI_br_if _
    | BI_br_table _ _
    | BI_return =>
        (init_bb nil, ((init_bb (List.rev (bb_instrs (fst acc))))::(snd acc)))
    | _ => 
        (init_bb (i::(bb_instrs (fst acc))), (snd acc))
  end.

Definition bb's_of_expr (e: expr): list bb' :=
  let (bb, bbs) := List.fold_left bb's_of_expr' e (empty_bb, nil)
  in
    match bb_instrs bb with
    | nil => bbs
    | _ => List.rev ((init_bb (List.rev (bb_instrs bb))::(List.rev bbs)))
    end.

(* The simplest basic block *)
Example simple_bb1 :
forall (v1:value_num), 
  bb's_of_expr ((BI_const_num v1)::nil)
  = (init_bb ((BI_const_num v1)::nil))::nil.
Proof.
  reflexivity.
Qed.

(* A slightly more complicated example*)
Example simple_bb2 :
forall (v1:value_num)(v2:value_num), 
  bb's_of_expr ((BI_const_num v1)::(BI_const_num v2)::nil)
  = (init_bb ((BI_const_num v1)::(BI_const_num v2)::nil))::nil.
Proof.
  reflexivity.
Qed.

Example simple_bb3 :
forall (v1:value_num)(v2:value_num)(v3:value_num) x, 
  bb's_of_expr ((BI_const_num v1)::(BI_const_num v2)::(BI_const_num v3)::(BI_br x)::nil)
  = (init_bb ((BI_const_num v1)::(BI_const_num v2)::(BI_const_num v3)::nil))::nil.
Proof.
  reflexivity.
Qed.

(* Now examples with instructions that terminate a bb *)
Example branch_bb :
forall (v1:value_num)(v2:value_num)(v3:value_num) x, 
  bb's_of_expr ((BI_const_num v1)::(BI_const_num v2)::(BI_br x)::(BI_const_num v3)::nil)
  =   ((init_bb ((BI_const_num v1)::(BI_const_num v2)::nil)))
    ::((init_bb ((BI_const_num v3)::nil)))
    ::nil.
Proof.
  reflexivity.
Qed.

Lemma bb_instr_not_block: forall (i: basic_instruction) (b: block_type) (e: expr),
  bb_instr_of_basic_instruction i = Some i ->
  i <> BI_block b e.
Proof.
Admitted.

Lemma bb_of_instr: forall (i: basic_instruction),
    bb_instr_of_basic_instruction i = Some i ->
    bb's_of_expr (i::nil) = (init_bb (i::nil))::nil.
Proof.
Admitted.

Inductive bb_type :=
  BB_unknown
  | BB_exit_end | BB_exit_return | BB_exit_unreachable
  | BB_unreachable | BB_block | BB_loop | BB_if | BB_else | BB_end | BB_br | BB_br_if 
  | BB_br_table | BB_return.

Inductive bb : Type :=
{
  bbindex:  nat;        (* the index of this bb in the list of bblocks, makes things easier to have this *)
          start_op: nat;        (* index into e of the first op in the expr *)
(*  mutable *) end_op:   nat;        (* index+1 of the last op in the expr *)
(*  mutable *) succ:     list bb;    (* bblocks that can be directly reached from this bb *)
(*  mutable *) pred:     list bb;    (* bblocks that can directly reach this bb *)
(*  mutable *) bbtype:	 bb_type;    (* effectively the control opcode that created this bb *)
(*  mutable *) nesting:  nat;        (* nesting level of the last opcode in the bb *)
(*  mutable *) labels:   list nat;   (* destination labels used in BR, BR_IF, BR_TABLE instructions *)
(*  mutable *) br_dest:	 option bb;  (* for LOOP, BLOCK and IF instructions the bb that's the target of a branch for this instruction  *)
}.

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
    (fun a x => match (succ x) with |nil | _::nil => a | _ => a+1 end)
    bbs 0.

Definition bblocks_of_expr (_: expr): list bb :=
nil.

Definition expr_of_bb (e: expr) (bblock: bb): expr :=
  sublist (start_op bblock) ((end_op bblock) - (start_op bblock)) e.

(* 
val expr_of_bb        : Wm.expr -> bb -> Wm.expr
val bblocks_of_expr   : Wm.expr -> bb list
*)
