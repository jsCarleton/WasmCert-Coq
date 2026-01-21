From Wasm Require Import datatypes pp.
From Coq Require Import Floats.
From Coq Require Import List.
Require Import Strings.Byte Strings.String.
From mathcomp Require Import all_ssreflect seq.
Import ListNotations.


(* variables *)
Inductive var_type :=
  Var_parameter | Var_local | Var_global | Var_temp | Var_memory.

Record var : Type :=
{
  vtype:  var_type;
  nt:     value_type;
  idx:    nat;
  vname:  string;
}.
(* expression trees *)
Inductive constant_value := 
  | Num_constant: value_num -> constant_value
  | String_constant: string -> constant_value.

Inductive opdisplay := Infix | Prefix | Function.

Inductive et := 
  | Empty
  | Constant: constant_value -> et
  | Var: var -> et 
  | ExprList: list et -> et
  | Node: string -> opdisplay -> list et -> et.


Definition string_of_var (v: var): string :=
  let string_of_vart (vart: var_type): string :=
    match vart with 
      | Var_parameter => "p" | Var_local => "l" | Var_global => "g" 
      | Var_temp => "t" | Var_memory => ""
    end
  in
  let string_of_valt (valt: value_type): string :=
    match valt with 
      | T_num T_i32 => "n" | T_num T_i64 => "N" | T_num T_f32 => "f" 
      | T_num T_f64 => "F" | _ => "R"
    end
  in
  match (vtype v) with 
    | Var_parameter | Var_local | Var_global | Var_temp => (string_of_vart (vtype v)) ++ (string_of_valt (nt v)) ++ (pp.string_of_nat (idx v))
    | Var_memory => (vname v) ++ "[" ++ (pp.string_of_nat (idx v)) ++ "]"
  end.

Definition compare_vars (v1: var) (v2: var): comparison :=
  String.compare (string_of_var v1) (string_of_var v2).

Definition valtype_of_var (param_types: result_type) (local_types: list value_type) (idx: nat): option value_type :=
  if Nat.ltb idx (List.length param_types) then
    List.nth_error param_types idx
  else
    List.nth_error local_types (idx - List.length param_types).

Fixpoint vars_of_et' (tree: et): list var :=
  match tree with
  | Empty | Constant _  => [ ]
  | Var v               => [v]
  | ExprList el         => List.concat (List.map vars_of_et' el)
  | Node _ _ args       => List.concat (List.map vars_of_et' args)
  end.

Definition lebv (v1: var) (v2: var): bool :=
  leb (string_of_var v1) (string_of_var v2).

Fixpoint dedup (vars: list var): list var :=
  match vars with
  | []        => []
  | hd1::tl1  => match tl1 with
                 | []     => [hd1]
                 | hd2::_ => match compare_vars hd1 hd2 with
                             | Eq  => dedup tl1
                             | _   => hd1::(dedup tl1)
                             end
                 end
  end.

Definition vars_of_et (tree: et): list var :=
  dedup (sort lebv (vars_of_et' tree)).

(*
val v_in_vlist:             var -> var list -> bool
val format_et:              et -> string
val print_et:               et -> (string -> unit) -> unit
val compare:                et -> et -> int
val simplify:               et -> et
val simplify_sum:           et list -> et
val simplify_max:           et list -> et
val initialize_local_value: Wm.local_type list -> int -> int -> constant_value
val et_of_local_value:      Wm.resulttype list -> Wm.local_type list -> int -> et
val node_count:             et -> int
*)