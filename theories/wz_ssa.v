From Wasm Require Import datatypes list_extra.
From Wasm Require Import wz_et wz_ex wz_cp wz_bb.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Record ssa : Type :=
{
  result:         var;
  (* mutable *) etree:  et;
  (* mutable *) alive:  bool;
}.

Definition zero_i32: i32 := Wasm_int.Int32.zero.
Definition zero_i64: i64 := Wasm_int.Int64.zero.
Definition zero_f32: f32 := Wasm_float.float_zero f32m.
Definition zero_f64: f64 := Wasm_float.float_zero f64m.

Definition initial_local_value (nt: value_type): et :=
    match nt with
      | T_num T_i32 => Constant (Num_constant (VAL_int32 zero_i32))
      | T_num T_i64 => Constant (Num_constant (VAL_int64 zero_i64))
      | T_num T_f32 => Constant (Num_constant (VAL_float32 zero_f32))
      | T_num T_f64 => Constant (Num_constant (VAL_float64 zero_f64))
      | T_vec _ | T_ref _ | T_bot => Empty
    end.

Definition initial_ssa_of_local (idx: nat) (nt: value_type): ssa :=
  {| result := {| vtype := Var_local; nt := nt; idx := idx; vname := "v" |};
    etree := initial_local_value nt; 
    alive := true |}.

Definition ssa_of_codepath (ctx: execution_context) (codepath: cp) (init_locals: bool): list ssa :=
  let ssa_of_op (ctx: execution_context) (acc: list ssa) (op: basic_instruction): list ssa :=
    nil
  in
  let ssa_of_expr (ctx: execution_context) (e: expr) acc: list ssa :=
    List.fold_left (ssa_of_op ctx) e acc
  in
  let ssa_of_bb (ctx: execution_context) acc (bblock: bb): list ssa :=
    ssa_of_expr ctx (expr_of_bb (w_e ctx) bblock) acc
  in
  let initial_ssas_of_locals (ll: list value_type): list ssa :=
    mapi initial_ssa_of_local ll
  in
  List.fold_left
    (fun acc bb => ssa_of_bb ctx acc bb)
    codepath
    (if init_locals then (initial_ssas_of_locals (local_types ctx)) else nil). 

(*
let ssa_of_op (ctx: execution_context) (acc: ssa list) (op: op_type): ssa list =
  let param_count (w: wm) (arg: op_arg): int = 
    match arg with
    | Blocktype bt -> (
      match bt with
      | Emptytype | Valuetype _  -> 0
      | Typeindex n -> List.length (List.nth_exn w.type_section n).rt1
    )
    | _ -> failwith "Invalid blocktype arg"
  in

  match op.instrtype with
  | Control  ->
      (match op.opsym with
      | OP_unreachable | OP_nop | OP_else | OP_end | OP_br | OP_return -> acc
      | OP_loop ->
        mark_dead acc (param_count ctx.w op.arg); acc
      | OP_block ->
        mark_dead acc (param_count ctx.w op.arg); acc
      | OP_if ->
        mark_dead acc ((param_count ctx.w op.arg) + 1); acc
      | OP_br_if | OP_br_table -> 
          mark_dead acc 1; acc
      | OP_call ->
        (match op.arg with
        | Funcidx fidx ->
            (* mark the arguments to the function dead *)
            let params = List.map ~f:(fun p -> p.etree) (List.take acc (nparams ctx.w fidx)) in
            mark_dead acc (nparams ctx.w fidx);
            (* create SSAs for each of the return values *)
            let retvals = List.mapi ~f:(ssa_of_rt (List.length acc) fidx params) (ret_types ctx.w fidx) in
            List.append retvals acc
        | _ -> failwith "Invalid call argument")
      | OP_call_indirect ->
        (match op.arg with
          | CallIndirect c ->
              (* mark the arguments to the function dead *)
              let nparams = List.length (List.nth_exn ctx.w.type_section c.y).rt1 in
              let params = List.map ~f:(fun p -> p.etree) (List.take acc nparams) in
              mark_dead acc nparams;
              (* create SSAs for each of the return values *)
              List.append (List.mapi ~f:(ssa_of_rt (List.length acc) c.x params) (List.nth_exn ctx.w.type_section c.y).rt2) acc (*TODO c.x might not be enough *)
          | _ -> failwith "Invalid call_indirect argument")
      | _ -> failwith (sprintf "Invalid control opcode %s" (string_of_opcode op.opsym)))
  | Reference  -> failwith "Reference"
  | Parametric  ->
      (match op.opsym with
        | OP_drop ->
          mark_dead acc 1;
          acc
        | OP_select ->
          let c = find_and_kill acc in
          let val2 = find_and_kill acc in
          let val1 = find_and_kill acc in
            { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""}; (* TODO nt wrong *)
              etree = Node {op = "select"; op_disp = Function; args = [c; val2; val1]}; alive = true}
              :: acc
        | _ -> failwith (sprintf "Invalid parametric opcode %s" (string_of_opcode op.opsym)))
  | VariableGL ->
      let idx = int_of_get_argL op.arg in
      { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""}; (* TODO nt wrong *)
        etree = Variable {vtype = vtype_of_idx idx ctx;
                          nt    = valtype_of_var ctx.param_types ctx.local_types idx; 
                          idx;
                          vname = ""};
        alive = true} :: acc         
  | VariableSL  ->
      let idx = int_of_get_argL op.arg in
      { result = {vtype = vtype_of_idx idx ctx;
                  nt    = valtype_of_var ctx.param_types ctx.local_types idx; 
                  idx;
                  vname = ""};
        etree = find_and_kill acc;
        alive = false} :: acc
  | VariableTL  ->
      let idx = int_of_get_argL op.arg in
      { result = {vtype = vtype_of_idx idx ctx;
                  nt    = valtype_of_var ctx.param_types ctx.local_types idx; 
                  idx;
                  vname = ""};
        etree = find_alive acc;
        alive = false} :: acc
  | VariableGG  ->
      { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""};
        etree = Variable {vtype = Var_global;
                          nt    = nt_of_global (globals_of_imports ctx.w.import_section) ctx.w.global_section (int_of_get_argL op.arg);
                          idx   = int_of_get_argL op.arg;
                          vname = ""};
        alive = true} :: acc         
  | VariableSG  ->
      { result = {vtype = Var_global; nt = Numtype I32; idx = int_of_get_argL op.arg; vname = ""};
        etree = find_and_kill acc;
        alive = false} :: acc
  | Table  ->
      failwith "Table"
  | MemoryL  ->
      (* get the memory value that's being loaded *)
      { result = {vtype = Var_temp; nt = Numtype (elem_type_of_arg op.arg); idx = List.length acc; vname = ""}; 
        etree = find_mem_elem ctx.w_state.mem_values op.arg;
        alive = true} :: acc
  | MemoryS  ->
      { result = {vtype = Var_memory; nt = Numtype (elem_type_of_arg op.arg); idx = elem_offset_of_arg op.arg; vname = "m"}; 
        etree = find_and_kill acc; 
        alive = false} :: acc
  | MemoryM  ->
        acc
  | Constop  ->
      { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""};
        etree = (et_of_const_arg op.arg);
        alive = true} :: acc
  | Unop ->
      let arg1 = find_and_kill acc in
        { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""}; 
          etree = Node {op = op.opname; op_disp = Prefix; args = [arg1]};
          alive = true} :: acc         
  | Binop op
  | Relop op  ->
      let arg2 = find_and_kill acc in
      let arg1 = find_and_kill acc in
        { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""}; 
          etree = Node {op; op_disp = Infix; args = [arg1; arg2]};
          alive = true} :: acc         
  | Testop ->
      { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""};
        etree = Node {op = op.opname; op_disp = Prefix; args = [find_and_kill acc]};
        alive = true} :: acc
  | Cvtop   ->
      { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""};
        etree = Node {op = op.opname; op_disp = Prefix; args = [find_and_kill acc]};
        alive = true} :: acc         

*)
(*
val explode_var:        ssa list -> Et.var -> ssa
*)
