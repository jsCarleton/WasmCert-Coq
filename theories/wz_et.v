From Wasm Require Import datatypes pp.
From Coq Require Import Floats.
Require Import Strings.Byte Strings.String.

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

(*
val valtype_of_var:         Wm.resulttype list -> Wm.local_type list -> int -> Wm.valtype
val vars_of_et:             et -> var list
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