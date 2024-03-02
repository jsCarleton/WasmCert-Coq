(** Executable instantiation **)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import opsem interpreter_ctx instantiation_spec.
From Coq Require Import BinNat.

Section Instantiation_func.

Context `{hfc: host_function_class}.
  
Definition gather_m_f_type (tfs : list function_type) (m_f : module_func) : option function_type :=
  lookup_N tfs m_f.(modfunc_type).

Definition gather_m_f_types (tfs : list function_type) (m_fs : list module_func) : option (list function_type) :=
  those (map (gather_m_f_type tfs) m_fs).

Definition module_import_desc_typer (tfs: list function_type) (imp_desc : module_import_desc) : option extern_type :=
  match imp_desc with
  | MID_func i => option_map ET_func (lookup_N tfs i)
  | MID_table t_t =>
    if module_table_typing empty_t_context {| modtab_type := t_t |} then Some (ET_table t_t) else None
  | MID_mem mt =>
    if module_mem_typing empty_t_context {| modmem_type := mt |} then Some (ET_mem mt) else None
  | MID_global gt => Some (ET_global gt)
  end.

(* breaking circularity, therefore only taking the function types *)
Definition module_imports_typer (tfs: list function_type) (imps : list module_import) : option (list extern_type) :=
  those (map (fun imp => module_import_desc_typer tfs imp.(imp_desc)) imps).

(* Spec has a mistake? *)
Definition gather_m_e_type (tts: list table_type) (emode: module_elemmode) : option reference_type :=
  match emode with
  | ME_passive => Some T_funcref
  | ME_active x offset => option_map tt_elem_type (lookup_N tts x)
  | ME_declarative => Some T_funcref
  end.

Definition module_export_typer (C : t_context) (exp : module_export_desc) : option extern_type :=
  match exp with
  | MED_func i => option_map ET_func (lookup_N C.(tc_funcs) i)
  | MED_table i => option_map ET_table (lookup_N C.(tc_tables) i)
  | MED_mem i => option_map ET_mem (lookup_N C.(tc_mems) i)
  | MED_global i => option_map ET_global (lookup_N C.(tc_globals) i)
  end.

Definition module_exports_typer (c : t_context) exps :=
  those (List.map (fun exp => module_export_typer c exp.(modexp_desc)) exps).

Definition gather_m_g_types (mgs : list module_global) : list global_type :=
  List.map (fun mg => mg.(modglob_type)) mgs.

Definition module_func_type_checker (c : t_context) (m : module_func) : bool :=
  let '{| modfunc_type := i; modfunc_locals := t_locs; modfunc_body := b_es |} := m in
  match lookup_N c.(tc_types) i with
  | None => false
  | Some (Tf tn tm) =>
    let c' := {|
      tc_types := c.(tc_types);
      tc_funcs := c.(tc_funcs);
      tc_globals := c.(tc_globals);
      tc_tables := c.(tc_tables);
      tc_mems := c.(tc_mems);
      tc_elems := c.(tc_elems);
      tc_datas := c.(tc_datas);
      tc_locals := List.app c.(tc_locals) (List.app tn t_locs);
      tc_labels := tm :: c.(tc_labels);
      tc_return := Some tm;
      tc_refs := c.(tc_refs)
    |} in
    type_checker.b_e_type_checker c' b_es (Tf [::] tm)
  end.

Definition module_tab_type_checker := module_table_typing.
Definition module_memory_type_checker := module_mem_typing.

Definition module_global_type_checker (c : t_context) (mg : module_global) : bool :=
  let '{| modglob_type := tg; modglob_init := es |} := mg in
  const_exprs c es &&
  type_checker.b_e_type_checker c es (Tf nil [::tg.(tg_t)]).

Definition module_elem_type_checker (c : t_context) (e : module_element) : bool :=
  let '{| modelem_type := t; modelem_init := e_inits; modelem_mode := emode |} := e in
  all (const_exprs c) e_inits &&
  all (fun es => type_checker.b_e_type_checker c es (Tf nil [::T_ref t])) e_inits &&
  module_elem_mode_checker c emode t.  

Definition module_data_mode_checker (C: t_context) (dmode: module_datamode): bool :=
  match dmode with
  | MD_passive => true
  | MD_active x offset =>
      match lookup_N C.(tc_mems) x with
      | Some _ =>
          (type_checker.b_e_type_checker C offset (Tf nil [::T_num T_i32])) &&
            const_exprs C offset
      | None => false
      end
  end.

Definition module_data_type_checker (c : t_context) (d : module_data) : bool :=
  let '{| moddata_init := bs; moddata_mode := dmode |} := d in
  module_data_mode_checker c dmode.

Definition module_start_type_checker (c : t_context) (ms : module_start) : bool :=
  module_start_typing c ms.

Definition gather_m_e_type (tts: list table_type) (elem: module_element) : option refernece_type :=
  match elem. with
  | ME_


Definition module_type_checker (m : module) : option ((list extern_type) * (list extern_type)) :=
  let '{|
    mod_types := tfs;
    mod_funcs := fs;
    mod_tables := ts;
    mod_mems := ms;
    mod_globals := gs;
    mod_elems := els;
    mod_datas := ds;
    mod_start := i_opt;
    mod_imports := imps;
    mod_exports := exps;
    |} := m in
  match (gather_m_f_types tfs fs, module_imports_typer tfs imps) with
  | (Some fts, Some impts) =>
    let ifts := ext_t_funcs impts in
    let its := ext_t_tabs impts in
    let ims := ext_t_mems impts in
    let igs := ext_t_globs impts in
    let gts := gather_m_g_types gs in
    let rts := gather_
      tc_types := tfs;
      tc_funcs := ifts ++ fts;
      tc_globals := igs ++ gts;
      tc_tables := its ++ (map modtab_type ts);
      tc_mems := ims ++ (map modmem_type ms);
      tc_elems := rts;
      tc_datas := List.repeat tt (length ds);
      tc_locals := nil;
      tc_labels := nil;
      tc_return := None |} in
    let c' := {|
      tc_types := nil;
      tc_funcs := nil;
      tc_globals := igs;
      tc_tables := nil;
      tc_mems := nil;
      tc_locals := nil;
      tc_labels := nil;
      tc_return := None
    |} in
    if seq.all (module_func_type_checker c) fs &&
       seq.all module_tab_type_checker ts &&
       seq.all module_memory_type_checker ms &&
       seq.all (module_global_type_checker c') gs &&
       seq.all (module_elem_type_checker c) els &&
       seq.all (module_data_type_checker c) ds &&
       pred_option (module_start_type_checker c) i_opt then
       match module_exports_typer c exps with
       | Some expts => Some (impts, expts)
       | None => None
       end
    else None
  | (Some _, None) | (None, Some _) | (None, None) => None
  end.

Definition external_type_checker (s : store_record) (v : v_ext) (e : extern_type) : bool :=
  match (v, e) with
  | (MED_func (Mk_funcidx i), ET_func tf) =>
    (i < List.length s.(s_funcs)) &&
    match lookup_N s.(s_funcs) i with
    | None => false
    | Some cl => tf == operations.cl_type cl
    end
  | (MED_table (Mk_tableidx i), ET_table tf) =>
    (i < List.length s.(s_tables)) &&
    match lookup_N s.(s_tables) i with
    | None => false
    | Some ti => typing.tab_typing ti tf
    end
  | (MED_mem (Mk_memidx i), ET_mem mt) =>
    (i < List.length s.(s_mems)) &&
    match lookup_N s.(s_mems) i with
    | None => false
    | Some m => typing.mem_typing m mt
    end
  | (MED_global (Mk_globalidx i), ET_global gt) =>
    (i < List.length s.(s_globals)) &&
    match lookup_N s.(s_globals) i with
    | None => false
    | Some g => typing.global_agree g gt
    end
  | (_, _) => false
  end.

Definition interp_get_v (s : store_record) (inst : instance) (b_es : list basic_instruction) : option value :=
  match run_multi_step_raw 5 s (Build_frame [::] inst) (operations.to_e_list b_es) 1 with
  | inr vs =>
    match vs with
    | [:: v] => Some v
    | _ => None
    end
  | _ => None
  end.

Definition interp_get_i32 (s : store_record) (inst : instance) (b_es : list basic_instruction) : option i32 :=
  match interp_get_v s inst b_es with
  | Some (VAL_int32 c) => Some c
  | _ => None
  end.

(* Executable version of instantiation for extraction adapted from Isabelle; unverified yet *)
Definition interp_instantiate (s : store_record) (m : module) (v_imps : list v_ext) : option ((store_record * instance * list module_export) * option nat) :=
  match module_type_checker m with
  | None => None
  | Some (t_imps, t_exps) =>
    if seq.all2 (external_type_checker s) v_imps t_imps then
      let g_inits_opt :=
        let c := {|
          inst_types := nil;
          inst_funcs := nil;
          inst_tab := nil;
          inst_memory := nil;
          inst_globs := List.map (fun '(Mk_globalidx i) => i) (ext_globs v_imps);
        |} in
        those (map (fun g => interp_get_v s c g.(modglob_init)) m.(mod_globals)) in
      match g_inits_opt with
      | None => None
      | Some g_inits =>
        let '(s', inst, v_exps) := interp_alloc_module s m v_imps g_inits in
        let e_offs_opt := those (map (fun e => interp_get_i32 s' inst e.(modelem_offset)) m.(mod_elem)) in
        match e_offs_opt with
        | None => None
        | Some e_offs =>
          let d_offs_opt := those (map (fun d => interp_get_i32 s' inst d.(moddata_offset)) m.(mod_data)) in
          match d_offs_opt with
          | None => None
          | Some d_offs =>
            if check_bounds_elem inst s' m e_offs &&
               check_bounds_data inst s' m d_offs then
              let start : option nat := operations.option_bind (fun i_s => lookup_N inst.(inst_funcs) (match i_s.(modstart_func) with Mk_funcidx i => i end)) m.(mod_start) in
              let s'' := init_tabs s' inst (List.map nat_of_int e_offs) m.(mod_elem) in
              let s_end := init_mems s'' inst (List.map N_of_int d_offs) m.(mod_data) in
              Some ((s_end, inst, v_exps), start)
            else None
          end
        end
      end
    else None
  end.

Definition empty_store_record : store_record := {|
    s_funcs := nil;
    s_tables := nil;
    s_mems := nil;
    s_globals := nil;
  |}.

(* Add an empty host and provide an initial empty store *)
Definition interp_instantiate_wrapper (m : module) : option ((host_state * store_record * instance * list module_export) * option nat) :=
  match interp_instantiate empty_store_record m nil with
  | Some ((s, i, es), on) => Some ((tt, s, i, es), on)
  | None => None
  end.

Definition lookup_exported_function (n : name) (store_inst_exps : host_state * store_record * instance * list module_export)
    : option (host_state * store_record * frame * seq administrative_instruction) :=
  let '(hs, s, inst, exps) := store_inst_exps in
  List.fold_left
    (fun acc e =>
      match acc with
      | Some cfg => Some cfg
      | None =>
        if e.(modexp_name) == n then
          match e.(modexp_desc) with
          | MED_func (Mk_funcidx fi) =>
            match lookup_N s.(s_funcs) fi with
            | None => None
            | Some fc => Some (hs, s, (Build_frame nil inst), [::AI_invoke fi])
            end
          | _ => None
          end
        else None
      end)
    exps
    None.

End Instantiation_func.

(** Extraction **)

Module Instantiation_func_extract.

Import interpreter_func.EmptyHost.

Definition lookup_exported_function :
    name -> host_state * store_record * instance * seq module_export ->
    option (host_state * store_record * frame * seq administrative_instruction) :=
  lookup_exported_function.

Definition interp_instantiate_wrapper :
  module ->
  option (host_state * store_record * instance * seq module_export * option nat) :=
  interp_instantiate_wrapper.

End Instantiation_func_extract.
