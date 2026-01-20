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
    match op with
      (* control operations *)
      | BI_unreachable | BI_nop | BI_br _ | BI_return => acc
      | BI_loop _ _
      | BI_block _ _  => (* mark_dead acc (param_count ctx.w op.arg);*) acc
      | BI_if _ _ _ => (* mark_dead acc ((param_count ctx.w op.arg) + 1);*) acc
      | BI_br_if _ | BI_br_table _ _ => (* mark_dead acc 1;*) acc
      (* the operations above this should never appear in a bb *)
      (* only the ones below this *)
      | BI_call _ (* fidx *) | BI_return_call _ (* fidx *) => (*
          (* mark the arguments to the function dead *)
          let params = List.map ~f:(fun p -> p.etree) (List.take acc (nparams ctx.w fidx)) in
          mark_dead acc (nparams ctx.w fidx);
          (* create SSAs for each of the return values *)
          let retvals = List.mapi ~f:(ssa_of_rt (List.length acc) fidx params) (ret_types ctx.w fidx) in
          List.append retvals acc *)
          acc
      | BI_call_indirect _ _ (* c *) | BI_return_call_indirect _ _ (* c *) => (*
          (* mark the arguments to the function dead *)
          let nparams = List.length (List.nth_exn ctx.w.type_section c.y).rt1 in
          let params = List.map ~f:(fun p -> p.etree) (List.take acc nparams) in
          mark_dead acc nparams;
          (* create SSAs for each of the return values *)
          List.append (List.mapi ~f:(ssa_of_rt (List.length acc) c.x params) (List.nth_exn ctx.w.type_section c.y).rt2) acc (*TODO c.x might not be enough *) *)
          acc
      (* parametric *)
      | BI_drop => (* mark_dead acc 1; *) acc
      | BI_select _ => 
        (*  let c = find_and_kill acc in
            let val2 = find_and_kill acc in
            let val1 = find_and_kill acc in
              { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""}; (* TODO nt wrong *)
                etree = Node {op = "select"; op_disp = Function; args = [c; val2; val1]}; alive = true}
                :: acc*)
        acc
    (* variables *)
    | BI_local_get _ (* idx *) => (*
        let idx = int_of_get_argL op.arg in
        { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""}; (* TODO nt wrong *)
          etree = Variable {vtype = vtype_of_idx idx ctx;
                            nt    = valtype_of_var ctx.param_types ctx.local_types idx; 
                            idx;
                            vname = ""};
          alive = true} :: acc
          *) acc
    | BI_local_set _  (* idx *) => (*
        let idx = int_of_get_argL op.arg in
        { result = {vtype = vtype_of_idx idx ctx;
                    nt    = valtype_of_var ctx.param_types ctx.local_types idx; 
                    idx;
                    vname = ""};
          etree = find_and_kill acc;
          alive = false} :: acc
          *) acc
    | BI_local_tee _  (* idx *) => (*
        let idx = int_of_get_argL op.arg in
        { result = {vtype = vtype_of_idx idx ctx;
                    nt    = valtype_of_var ctx.param_types ctx.local_types idx; 
                    idx;
                    vname = ""};
          etree = find_alive acc;
          alive = false} :: acc
          *) acc
    | BI_global_get _  (* idx *) => (*
        { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""};
          etree = Variable {vtype = Var_global;
                            nt    = nt_of_global (globals_of_imports ctx.w.import_section) ctx.w.global_section (int_of_get_argL op.arg);
                            idx   = int_of_get_argL op.arg;
                            vname = ""};
          alive = true} :: acc         
          *) acc
    | BI_global_set _ (* idx *) => (*
        { result = {vtype = Var_global; nt = Numtype I32; idx = int_of_get_argL op.arg; vname = ""};
          etree = find_and_kill acc;
          alive = false} :: acc
          *) acc
    (* memory operations *)
    | BI_load _ _ _  => (*
        (* get the memory value that's being loaded *)
        { result = {vtype = Var_temp; nt = Numtype (elem_type_of_arg op.arg); idx = List.length acc; vname = ""}; 
          etree = find_mem_elem ctx.w_state.mem_values op.arg;
          alive = true} :: acc
        *) acc
    | BI_load_vec _ _ => acc (* new *)
    | BI_load_vec_lane _ _ _ => acc  (* new *)
    | BI_store _ _ _  => (*
        { result = {vtype = Var_memory; nt = Numtype (elem_type_of_arg op.arg); idx = elem_offset_of_arg op.arg; vname = "m"}; 
          etree = find_and_kill acc; 
          alive = false} :: acc
        *) acc
    | BI_store_vec _ => acc  (* new *)
    | BI_store_vec_lane _ _ _ => acc  (* new *)
    | BI_memory_size
    | BI_memory_grow
    | BI_memory_fill
    | BI_memory_copy
    | BI_memory_init _ 
    | BI_data_drop _ => acc
    (* numeric instructions *)
    | BI_const_num _ (* value_num *) => (*
        { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""};
          etree = (et_of_const_arg op.arg);
          alive = true} :: acc *)
        acc 
    | BI_unop _ _ (* number_type -> unop *) => (*
        let arg1 = find_and_kill acc in
          { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""}; 
            etree = Node {op = op.opname; op_disp = Prefix; args = [arg1]};
            alive = true} :: acc
        *) acc
    | BI_binop _ _ (* number_type -> binop *)
    | BI_relop _ _ (* number_type -> relop *) => (*
        let arg2 = find_and_kill acc in
        let arg1 = find_and_kill acc in
          { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""}; 
            etree = Node {op; op_disp = Infix; args = [arg1; arg2]};
            alive = true} :: acc
      *) acc
    | BI_testop _ _ (* number_type -> testop *) => (*
        { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""};
          etree = Node {op = op.opname; op_disp = Prefix; args = [find_and_kill acc]};
          alive = true} :: acc *)
        acc
    | BI_cvtop _ _ _ _ (* number_type -> cvtop -> number_type -> option sx *) => (*
        { result = {vtype = Var_temp; nt = Numtype I32; idx = List.length acc; vname = ""};
          etree = Node {op = op.opname; op_disp = Prefix; args = [find_and_kill acc]};
          alive = true} :: acc *)
        acc
    (* vector instructions *)
    | BI_const_vec _
    | BI_vunop _
    | BI_vbinop _
    | BI_vternop _
    | BI_vtestop _
    | BI_vshiftop _
    | BI_splat_vec _
    | BI_extract_vec _ _ _
    | BI_replace_vec _ _ => acc
    (* references *)
    | BI_ref_null _
    | BI_ref_is_null
    | BI_ref_func _ => acc
    (* tables *)
    | BI_table_get _
    | BI_table_set _
    | BI_table_size _
    | BI_table_grow _
    | BI_table_fill _
    | BI_table_copy _ _
    | BI_table_init _ _
    | BI_elem_drop _ => acc
  end
  in
  let ssa_of_expr (ctx: execution_context) (e: expr) acc: list ssa :=
    List.fold_left (ssa_of_op ctx) e acc
  in
  let ssa_of_bb (ctx: execution_context) acc (bblock: bb): list ssa :=
    ssa_of_expr ctx (expr_of_bb bblock) acc
  in
  let initial_ssas_of_locals (ll: list value_type): list ssa :=
    mapi initial_ssa_of_local ll
  in
  List.fold_left
    (fun acc bb => ssa_of_bb ctx acc bb)
    codepath
    (if init_locals then (initial_ssas_of_locals (local_types ctx)) else nil). 


Definition explode_var (s: list ssa) (r: var): ssa :=
  let fix expand_et (e: et) (s: ssa): et :=
    match e with 
      | Var v
          => match compare_vars v (result s) with
              | Eq => etree s
              | _ => e
            end
      | Node op op_disp args => Node op op_disp (List.map (fun e' => expand_et e' s) args)
      | _ => e
    end
  in
  {| result := r; etree := List.fold_left expand_et s (Var r); alive := true |}.
