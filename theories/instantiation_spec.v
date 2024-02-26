(** Relational instantiation in the spec **)
(* see https://webassembly.github.io/spec/core/exec/modules.html#exec-instantiation *)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import list_extra datatypes datatypes_properties
                         interpreter_func binary_format_parser operations
                         typing opsem type_checker memory memory_list.
From Coq Require Import BinNat.

(* TODO: Documentation *)

Section Instantiation_spec.
  
Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record_eq_dec := @store_record_eq_dec host_function.
Let store_record_eqType := @store_record_eqType host_function.

(* Before adding a canonical structure to [name], we save the base one to ensure better extraction. *)
Local Canonical Structure name_eqType := Eval hnf in EqType name (seq_eqMixin _).

Let store_record := store_record host_function.
Let host_state := host_state host_instance.

Definition alloc_Xs {A B} f (s : store_record) (xs : list A) : store_record * list B :=
  let '(s', fas) :=
    List.fold_left
      (fun '(s, ys) x =>
        let '(s', y) := f s x in
        (s', y :: ys))
        xs
        (s, nil) in
  (s', List.rev fas).

Definition funcs_of_externals (evs : list extern_value) : list funcaddr :=
  seq.pmap (fun ev => match ev with | EV_func fa => Some fa | _ => None end) evs.

Definition tables_of_externals (evs : list extern_value) : list tableaddr :=
  seq.pmap (fun ev => match ev with | EV_table ta => Some ta | _ => None end) evs.

Definition mems_of_externals (evs : list extern_value) : list memaddr :=
  seq.pmap (fun ev => match ev with | EV_mem ta => Some ta | _ => None end) evs.

Definition globals_of_externals (evs : list extern_value) : list globaladdr :=
  seq.pmap (fun ev => match ev with | EV_global ta => Some ta | _ => None end) evs.

Definition add_func (s : store_record) funcinst := {|
  s_funcs := List.app s.(s_funcs) [::funcinst];
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
  s_elems := s.(s_elems);
  s_datas := s.(s_datas);
|}.

Definition alloc_func (s : store_record) (m_f : module_func) (mi : moduleinst) : store_record * funcaddr :=
  let funcaddr := N.of_nat (List.length s.(s_funcs)) in
  (* Spec didn't say what if this is out of bound; but it cannot happen to valid modules *)
  let functype := List.nth m_f.(modfunc_type) mi.(inst_types) (Tf nil nil) in
  let funcinst := FC_func_native functype mi m_f in
  let S' := add_func s funcinst in
  (S', funcaddr).

Definition alloc_funcs (s : store_record) (m_fs : list module_func) (mi : moduleinst) : store_record * list funcaddr :=
  alloc_Xs (fun s m_f => alloc_func s m_f mi) s m_fs.

Definition add_table (s : store_record) (ti : tableinst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := List.app s.(s_tables) [::ti];
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
  s_elems := s.(s_elems);
  s_datas := s.(s_datas);
|}.

Definition alloc_tab_ref (s : store_record) (tty : table_type) (ref: value_ref) : store_record * tableaddr :=
  let '{| tt_limits := {| lim_min := min; lim_max := maxo |} as lim; tt_elem_type := ety |} := tty in
  let tableaddr := N.of_nat (List.length s.(s_tables)) in
  let tableinst := {|
    tableinst_elem := (List.repeat ref min);
    tableinst_type := tty;
  |} in
  (add_table s tableinst, tableaddr).

Definition alloc_tab s tty: store_record * tableaddr :=
  alloc_tab_ref s tty (VAL_ref_null tty.(tt_elem_type)).

Definition alloc_tabs (s : store_record) (ts : list table_type) : store_record * list tableaddr :=
  alloc_Xs alloc_tab s ts.

Definition mem_mk (lim : limits) : meminst :=
  let len := BinNatDef.N.mul page_size lim.(lim_min) in
  {| meminst_data := mem_make Integers.Byte.zero len;
    meminst_type := lim;
  |}.

Definition add_mem (s : store_record) (m_m : meminst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := List.app s.(s_mems) [::m_m];
  s_globals := s.(s_globals);
  s_elems := s.(s_elems);
  s_datas := s.(s_datas);
|}.

Definition alloc_mem (s : store_record) (m_m : module_mem) : store_record * memaddr :=
  let '{| modmem_type := {| lim_min := min; lim_max := maxo |} |} := m_m in
  let memaddr := N.of_nat (List.length s.(s_mems)) in
  let meminst := mem_mk m_m.(modmem_type) in
  (add_mem s meminst, memaddr).

Definition alloc_mems (s : store_record) (m_ms : list module_mem) : store_record * list memaddr :=
  alloc_Xs alloc_mem s m_ms.

Definition add_glob (s : store_record) (m_g : globalinst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := List.app s.(s_globals) [::m_g];
  s_elems := s.(s_elems);
  s_datas := s.(s_datas);
|}.

Definition alloc_glob (s : store_record) (m_g_v : module_global * value) : store_record * globaladdr :=
  let '(mg_type, v) := m_g_v in
  let globaddr := N.of_nat (List.length s.(s_globals)) in
  let globinst := Build_globalinst (Build_global_type mg_type.(modglob_type).(tg_mut) mg_type.(modglob_type).(tg_t)) v in
  (add_glob s globinst, globaddr).

Definition alloc_globs s m_gs vs :=
  alloc_Xs alloc_glob s (List.combine m_gs vs).

Definition add_elem (s : store_record) (m_e : eleminst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
  s_elems := List.app s.(s_elems) [::m_e];
  s_datas := s.(s_datas);
|}.

Definition alloc_elem (s: store_record) (m_e_v: module_element * list value_ref) : store_record * elemaddr :=
  let '(m_e, refs) := m_e_v in
  let reftype := m_e.(modelem_type) in
  let elemaddr := N.of_nat (List.length s.(s_elems)) in
  let eleminst := Build_eleminst reftype refs in
  (add_elem s eleminst, elemaddr).

Definition alloc_elems (s : store_record) (m_es : list module_element) (elem_inits: list (list value_ref)) : store_record * list elemaddr :=
  alloc_Xs alloc_elem s (List.combine m_es elem_inits).

Definition add_data (s : store_record) (m_d : datainst) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
  s_globals := s.(s_globals);
  s_elems := s.(s_elems);
  s_datas := List.app s.(s_datas) [::m_d];
|}.

Definition alloc_data (s: store_record) (m_d: list byte) : store_record * dataaddr :=
  let dataaddr := N.of_nat (List.length s.(s_datas)) in
  let datainst := Build_datainst m_d in
  (add_data s datainst, dataaddr).

Definition alloc_datas (s : store_record) (m_d: list module_data) : store_record * list dataaddr :=
  alloc_Xs alloc_data s (map moddata_init m_d).

(* TODO: lemmas *)

Definition export_get_v_ext (inst : moduleinst) (exp : module_export_desc) : extern_value :=
  (* we circumvent partiality by providing 0 as a default *)
  match exp with
  | MED_func i => EV_func ( (List.nth i inst.(inst_funcs) N0))
  | MED_table i => EV_table ( (List.nth i inst.(inst_tables) N0))
  | MED_mem i => EV_mem ( (List.nth i inst.(inst_mems) N0))
  | MED_global i => EV_global ( (List.nth i inst.(inst_globals) N0))
  end.

Definition ext_funcs :=
  seq.pmap
    (fun x =>
      match x with
      | EV_func i => Some i
      | _ => None
      end).

Definition ext_tabs :=
  seq.pmap
    (fun x =>
      match x with
      | EV_table i => Some i
      | _ => None
      end).

Definition ext_mems :=
  seq.pmap
    (fun x =>
      match x with
      | EV_mem i => Some i
      | _ => None
      end).

Definition ext_globs :=
  seq.pmap
    (fun x =>
      match x with
      | EV_global i => Some i
      | _ => None
      end).

Definition ext_t_funcs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_func tf => Some tf
      | _ => None
      end).

Definition ext_t_tabs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_table i => Some i
      | _ => None
      end).

Definition ext_t_mems :=
  seq.pmap
    (fun x =>
      match x with
      | ET_mem i => Some i
      | _ => None
      end).

Definition ext_t_globs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_global i => Some i
      | _ => None
      end).

Definition get_exportinst (inst: moduleinst) (m_exp: module_export) : exportinst :=
  let extern_value := export_get_v_ext inst m_exp.(modexp_desc) in
  Build_exportinst m_exp.(modexp_name) extern_value.

Definition alloc_module (s : store_record) (m : module) (imps : list extern_value) (gvs : list value) (rvs: list (list value_ref))
    (s'_inst : store_record * moduleinst) : bool :=
  let '(s'_goal, inst) := s'_inst in
  let '(s1, i_fs) := alloc_funcs s m.(mod_funcs) inst in
  let '(s2, i_ts) := alloc_tabs s1 (List.map (fun t => t.(modtab_type)) m.(mod_tables)) in
  let '(s3, i_ms) := alloc_mems s2 m.(mod_mems) in
  let '(s4, i_gs) := alloc_globs s3 m.(mod_globals) gvs in
  let '(s5, i_es) := alloc_elems s4 m.(mod_elems) rvs in
  let '(s', i_ds) := alloc_datas s5 m.(mod_datas) in
  (s'_goal == s') &&
  (inst.(inst_types) == m.(mod_types)) &&
  (inst.(inst_funcs) == (List.app (ext_funcs imps) i_fs)) &&
  (inst.(inst_tables) == (List.app (ext_tabs imps) i_ts)) &&
  (inst.(inst_mems) == (List.app (ext_mems imps) i_ms)) &&
  (inst.(inst_globals) == (List.app (ext_globs imps) i_gs)) &&
  (inst.(inst_elems) == i_es) &&
  (inst.(inst_datas) == i_ds) &&
  (inst.(inst_exports) == (List.map (get_exportinst
                                         (Build_moduleinst nil i_fs i_ts i_ms i_gs nil nil nil))
                               m.(mod_exports))).

Definition dummy_table : tableinst := {| tableinst_elem := nil; tableinst_type := Build_table_type (Build_limits N0 None) T_funcref |}.

(*
Definition init_tab (s : store_record) (inst : instance) (e_ind : nat) (e : module_element) : store_record :=
  let t_ind := List.nth (match e.(modelem_table) with Mk_tableidx i => i end) inst.(inst_tables) 0 in
  let '{|table_data := tab_e; table_max_opt := maxo |} := List.nth t_ind s.(s_tables) dummy_table in
  let e_pay := List.map (fun i => List.nth_error inst.(inst_funcs) (match i with Mk_funcidx j => j end)) e.(modelem_init) in
  let tab'_e := List.app (List.firstn e_ind tab_e) (List.app e_pay (List.skipn (e_ind + length e_pay) tab_e)) in
  {| s_funcs := s.(s_funcs);
     s_tables := insert_at {| table_data := tab'_e; table_max_opt := maxo |} t_ind s.(s_tables);
     s_mems := s.(s_mems);
     s_globals := s.(s_globals) |}.

Definition init_tabs (s : store_record) (inst : instance) (e_inds : list nat) (es : list module_element) : store_record :=
  List.fold_left (fun s' '(e_ind, e) => init_tab s' inst e_ind e) (List.combine e_inds es) s.

Definition dummy_data_vec :=
  mem_make Integers.Byte.zero (N.zero).

Definition dummy_mem := {|
  mem_data := dummy_data_vec;
  mem_max_opt := None
|}.

Definition init_mem (s : store_record) (inst : instance) (d_ind : N) (d : module_data) : store_record :=
  let m_ind := List.nth (match d.(moddata_data) with Mk_memidx i => i end) inst.(inst_memory) 0 in
  let mem := List.nth m_ind s.(s_mems) dummy_mem in
  let d_pay := List.map bytes.compcert_byte_of_byte d.(moddata_init) in
  let mem'_e := List.app (List.firstn d_ind mem.(mem_data).(ml_data)) (List.app d_pay (List.skipn (d_ind + length d_pay) mem.(mem_data).(ml_data))) in
  let mems' := insert_at {| mem_data := {| ml_data := mem'_e; ml_init := #00 |}; mem_max_opt := mem.(mem_max_opt) |} m_ind s.(s_mems) in
  {| s_funcs := s.(s_funcs);
     s_tables := s.(s_tables);
     s_mems := mems';
     s_globals := s.(s_globals); |}.

Definition init_mems (s : store_record) (inst : instance) (d_inds : list N) (ds : list module_data) : store_record :=
  List.fold_left (fun s' '(d_ind, d) => init_mem s' inst d_ind d) (List.combine d_inds ds) s.
 *)

Definition function_type_valid (tf: function_type) : bool := true.

Definition table_type_valid (t: table_type) : bool :=
  limit_valid_range t.(tt_limits) (N.sub (N.pow 2 32) 1%N).

Definition memory_type_valid (t: memory_type) : bool :=
  limit_valid_range t (N.pow 2 16).

Definition global_type_valid (g: global_type) : bool := true.


Definition module_func_typing (c : t_context) (mf : module_func) (tf : function_type) : Prop :=
  let '{| modfunc_type := x; modfunc_locals := t_locs; modfunc_body := b_es |} := mf in
  let '(Tf tn tm) := tf in
  x < N.of_nat (List.length c.(tc_types)) /\
  lookup_N c.(tc_types) x == Some (Tf tn tm) /\
  let c' := {|
    tc_types := c.(tc_types);
    tc_funcs := c.(tc_funcs);
    tc_tables := c.(tc_tables);
    tc_mems := c.(tc_mems);
    tc_globals := c.(tc_globals);
    tc_elems := c.(tc_elems);
    tc_datas := c.(tc_datas);
    tc_locals := tn ++ t_locs;
    tc_labels := [::tm];
    tc_return := Some tm;
    tc_refs := c.(tc_refs);
  |} in
  typing.be_typing c' b_es (Tf [::] tm).

Definition module_tab_typing (c: t_context) (t : module_table) : bool :=
  table_type_valid t.(modtab_type).

Definition module_mem_typing (c: t_context) (m : module_mem) : bool :=
  memory_type_valid m.(modmem_type).

Definition const_expr (c : t_context) (b_e : basic_instruction) : bool :=
  match b_e with
  | BI_const_num _ => true
  | BI_const_vec _ => true
  | BI_ref_null _ => true
  | BI_ref_func _ => true
  | BI_global_get k =>
    (k < N.of_nat (length c.(tc_globals))) &&
    match lookup_N c.(tc_globals) k with
    | None => false
    | Some t => t.(tg_mut) == MUT_const
    end
  | _ => false
  end.

Definition const_exprs (c : t_context) (es : list basic_instruction) : bool :=
  seq.all (const_expr c) es.

Definition module_glob_typing (c : t_context) (g : module_global) (tg : global_type) : Prop :=
  let '{| modglob_type := tg'; modglob_init := es |} := g in
  const_exprs c es /\
  tg = tg' /\
    typing.be_typing c es (Tf nil [::tg.(tg_t)]).

Definition elemmode_valid (c: t_context) (emode: module_elemmode) (t: reference_type) : Prop :=
  match emode with
  | ME_passive => True
  | ME_active tidx es =>
      exists tabtype,
      tidx < N.of_nat (length c.(tc_tables)) /\
      lookup_N c.(tc_tables) tidx = Some tabtype /\
      let '{| tt_limits := t_lim; tt_elem_type := rt |} := tabtype in
      rt = t /\
      typing.be_typing c es (Tf nil [::T_num T_i32]) /\
      const_exprs c es
  | ME_declarative => True
  end.

Definition module_elem_typing (c : t_context) (e : module_element) (t: reference_type) : Prop :=
  let '{| modelem_type := t'; modelem_init := e_inits; modelem_mode := emode |} := e in
  t = t' /\
  List.Forall (fun es => const_exprs c es /\ typing.be_typing c es (Tf nil [::T_ref t])) e_inits /\
  elemmode_valid c emode t.  

Definition datamode_valid (c: t_context) (dmode: module_datamode) : Prop :=
  match dmode with
  | MD_passive => True
  | MD_active midx es =>
      exists memtype,
      midx < N.of_nat (length c.(tc_mems)) /\
      lookup_N c.(tc_mems) midx = Some memtype /\
      typing.be_typing c es (Tf nil [::T_num T_i32]) /\
      const_exprs c es
  end.

Definition module_data_typing (c : t_context) (m_d : module_data) : Prop :=
  let '{| moddata_init := bs; moddata_mode := dmode |} := m_d in
  datamode_valid c dmode.

Definition module_start_typing (c : t_context) (ms : module_start) : bool :=
  let x := ms.(modstart_func) in
  (x < N.of_nat (length c.(tc_funcs))) &&
  match lookup_N c.(tc_funcs) x with
  | None => false
  | Some tf => tf == (Tf nil nil)
  end.

Definition module_import_desc_typing (c : t_context) (d : module_import_desc) (e : extern_type) : bool :=
  match (d, e) with
  | (MID_func i, ET_func tf) =>
    (i < N.of_nat (List.length c.(tc_types))) &&
    match lookup_N c.(tc_types) i with
    | None => false
    | Some tf' => tf == tf'
    end
  | (MID_table t_t, ET_table t_t') =>
    (t_t == t_t') && module_tab_typing c {| modtab_type := t_t |}
  | (MID_mem mt, ET_mem mt') =>
    (mt == mt') && module_mem_typing c {| modmem_type := mt |}
  | (MID_global gt, ET_global gt') => gt == gt'
  | _ => false
  end.

Definition module_import_typing (c: t_context) (imp: module_import) (e: extern_type) :=
  module_import_desc_typing c imp.(imp_desc) e.

Definition module_export_desc_typing (c : t_context) (d : module_export_desc) (e : extern_type) : bool :=
  match (d, e) with
  | (MED_func i, ET_func tf) =>
    (i < N.of_nat (List.length c.(tc_funcs))) &&
    match lookup_N c.(tc_funcs) i with
    | None => false
    | Some tf' => tf == tf'
    end
  | (MED_table i, ET_table t_t) =>
    (i < N.of_nat (List.length c.(tc_tables))) &&
    match lookup_N c.(tc_tables) i with
    | None => false
    | Some lim' => t_t == lim'
    end
  | (MED_mem i, ET_mem t_m) =>
    (i < N.of_nat (List.length c.(tc_mems))) &&
    match lookup_N c.(tc_mems) i with
    | None => false
    | Some lim' => t_m == lim' 
    end
  | (MED_global i, ET_global gt) =>
    (i < N.of_nat (List.length c.(tc_globals))) &&
    match lookup_N c.(tc_globals) i with
    | None => false
    | Some gt' => gt == gt'
    end
  | (_, _) => false
  end.

Definition pred_option {A} (p : A -> bool) (a_opt : option A) : bool :=
  match a_opt with
  | None => true
  | Some a => p a
  end.

Definition module_export_typing (c: t_context) (exp: module_export) (e: extern_type) :=
  module_export_desc_typing c exp.(modexp_desc) e.

(* TODO: ??? *)
Definition module_funcidx (m: module) : list funcidx := nil.

Definition export_name_unique (exps: list module_export) :=
  List.NoDup (map modexp_name exps).

(* We deliberately omit the artificial restriction on the length of memory here. *)
Definition module_typing (m : module) (impts : list extern_type) (expts : list extern_type) : Prop :=
  exists fts tts mts gts rts,
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
  let ifts := ext_t_funcs impts in
  let its := ext_t_tabs impts in
  let ims := ext_t_mems impts in
  let igs := ext_t_globs impts in
  let xs := module_funcidx m in
  let c := {|
    tc_types := tfs;
    tc_funcs := List.app ifts fts;
    tc_tables := List.app its tts;
    tc_mems := List.app ims mts;
    tc_globals := List.app igs gts;
    tc_elems := rts;
    tc_datas := List.repeat tt (length ds);
    tc_locals := nil;
    tc_labels := nil;
    tc_return := None;
    tc_refs := xs;
  |} in
  let c' := {|
    tc_types := nil;
    tc_funcs := c.(tc_funcs);
    tc_tables := nil;
    tc_mems := nil;
    tc_globals := igs;
    tc_elems := c.(tc_elems);
    tc_datas := c.(tc_datas);
    tc_locals := nil;
    tc_labels := nil;
    tc_return := None;
    tc_refs := xs;
  |} in
  List.Forall function_type_valid tfs /\
  List.Forall2 (module_func_typing c) fs fts /\
  pred_option (module_start_typing c) i_opt /\
  List.Forall2 (module_import_typing c) imps impts /\
  List.Forall2 (module_export_typing c) exps expts /\
  seq.all (module_tab_typing c') ts /\
  seq.all (module_mem_typing c') ms /\
  List.Forall2 (module_glob_typing c') gs gts /\
  List.Forall2 (module_elem_typing c') els rts /\
  List.Forall (module_data_typing c') ds /\
  export_name_unique exps. 



(** std-doc:
For the purpose of checking external values against imports, such values are classified by external types. The following auxiliary typing rules specify this typing relation relative to a store S in which the referenced instances live.
*)
Inductive external_typing : store_record -> extern_value -> extern_type -> Prop :=
| ETY_func :
  forall (s : store_record) (i : N) cl,
  i < N.of_nat (List.length s.(s_funcs)) ->
  lookup_N s.(s_funcs) i = Some cl ->
  external_typing s (EV_func i) (ET_func (cl_type cl))
| ETY_tab :
  forall (s : store_record) (i : N) (ti : tableinst),
  i < N.of_nat (List.length s.(s_tables)) ->
  lookup_N s.(s_tables) i = Some ti ->
  external_typing s (EV_table i) (ET_table ti.(tableinst_type))
| ETY_mem :
  forall (s : store_record) (i : N) (m : meminst),
  i < N.of_nat (List.length s.(s_mems)) ->
  lookup_N s.(s_mems) i = Some m ->
  external_typing s (EV_mem i) (ET_mem m.(meminst_type))
| ETY_glob :
  forall (s : store_record) (i : N) (g : globalinst),
  i < N.of_nat (List.length s.(s_globals)) ->
  lookup_N s.(s_globals) i = Some g ->
  external_typing s (EV_global i) (ET_global g.(g_type)).


Definition instantiate_globals f (hs : host_state) (s' : store_record) m (g_inits: list value) : Prop :=
  List.Forall2 (fun g v =>
      opsem.reduce_trans (hs, s', f, to_e_list g.(modglob_init))
                         (hs, s', f, [::v_to_e v]))
    m.(mod_globals) g_inits.

Definition instantiate_elems f (hs : host_state) (s' : store_record) m (r_inits: list (list value_ref)) : Prop :=
  List.Forall2
    (fun e rs => List.Forall2
                   (fun bes r =>
                      opsem.reduce_trans
                        (hs, s', f, to_e_list bes)
                        (hs, s', f, [::v_to_e (VAL_ref r)]))
                   e.(modelem_init) rs)
    m.(mod_elems)
    r_inits.

(*
Definition nat_of_int (i : i32) : nat :=
  BinInt.Z.to_nat i.(Wasm_int.Int32.intval).

Definition N_of_int (i : i32) : N :=
  BinInt.Z.to_N i.(Wasm_int.Int32.intval).

Definition check_bounds_elem (inst : instance) (s : store_record) (m : module) (e_offs : seq i32) : bool :=
  seq.all2
    (fun e_off e =>
      match List.nth_error inst.(inst_tab) (match e.(modelem_table) with Mk_tableidx i => i end) with
      | None => false
      | Some i =>
        match List.nth_error s.(s_tables) i with
        | None => false
        | Some ti =>
          N.leb (N.add (N_of_int e_off) (N.of_nat (List.length e.(modelem_init)))) (N.of_nat (List.length ti.(table_data)))
        end
      end)
      e_offs
      m.(mod_elem).

Definition mem_length (m : memory) : N :=
  mem_length m.(mem_data).

Definition check_bounds_data (inst : instance) (s : store_record) (m : module) (d_offs : seq i32) : bool :=
  seq.all2
    (fun d_off d =>
      match List.nth_error inst.(inst_memory) (match d.(moddata_data) with Mk_memidx i => i end) with
      | None => false
      | Some i =>
        match List.nth_error s.(s_mems) i with
        | None => false
        | Some mem =>
          N.leb (N.add (N_of_int d_off) (N.of_nat (List.length d.(moddata_init)))) (mem_length mem)
        end
      end)
      d_offs
      m.(mod_data).

Definition check_start m inst start : bool :=
  let start' :=
    operations.option_bind
    (fun i_s =>
      List.nth_error inst.(inst_funcs) (match i_s.(modstart_func) with Mk_funcidx i => i end))
    m.(mod_start) in
  start' == start.
*)

Definition limit_subtyping (l1 l2: limits) : Prop :=
  l1.(lim_min) >= l2.(lim_min) /\
    match l1.(lim_max), l2.(lim_max) with
    | _, None => True
    | Some max1, Some max2 => N.leb max1 max2
    | _, _ => False
    end.

Definition import_subtyping (t1 t2: extern_type) : Prop :=
  match t1, t2 with
  | ET_func tf1, ET_func tf2 =>
      tf1 = tf2
  | ET_table tt1, ET_table tt2 =>
      tt1.(tt_elem_type) = tt2.(tt_elem_type) /\
      limit_subtyping tt1.(tt_limits) tt2.(tt_limits)
  | ET_mem tm1, ET_mem tm2 =>
      limit_subtyping tm1 tm2
  | ET_global tg1, ET_global tg2 =>
      tg1 = tg2
  | _, _ => False
  end.

Definition list_concat {T: Type} (l: list (list T)): list T :=
  List.fold_left (fun l1 l2 => l1 ++ l2) l nil.

Definition get_init_expr_elem (i: nat) (elem: module_element) : list basic_instruction :=
  match elem.(modelem_mode) with
  | ME_passive => nil
  | ME_active tidx bes =>
      bes ++ [::BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m Z0)); BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m (BinInt.Z.of_nat (length elem.(modelem_init))))); BI_table_init tidx (N.of_nat i); BI_elem_drop (N.of_nat i)]
  | ME_declarative => [::BI_elem_drop (N.of_nat i)]
  end.

Definition get_init_expr_elems (elems: list module_element) : list basic_instruction :=
  list_concat (mapi (fun n => get_init_expr_elem n) elems).

Definition get_init_expr_data (i: nat) (data: module_data) : list basic_instruction :=
  match data.(moddata_mode) with
  | MD_passive => nil
  | MD_active midx bes =>
      bes ++ [::BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m Z0)); BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m (BinInt.Z.of_nat (length data.(moddata_init))))); BI_memory_init (N.of_nat i); BI_data_drop (N.of_nat i)]
  end.

Definition get_init_expr_datas (datas: list module_data) : list basic_instruction :=
  list_concat (mapi (fun n => get_init_expr_data n) datas).

Definition get_init_expr_start (mstart: option module_start) : list basic_instruction :=
  match mstart with
  | Some (Build_module_start n) => [::BI_call n]
  | _ => nil
  end.

Definition instantiate (s : store_record) (m : module) (v_imps : list extern_value)
                       (z : (store_record * frame * list basic_instruction)) : Prop :=
  let '(s_end, f, bes) := z in
  exists t_imps_mod t_imps t_exps hs' s' inst g_inits r_inits,
    module_typing m t_imps_mod t_exps /\
    List.Forall2 (external_typing s) v_imps t_imps /\
    List.Forall2 import_subtyping t_imps t_imps_mod /\
    alloc_module s m v_imps g_inits r_inits (s', inst) /\
    let inst_init := Build_moduleinst nil inst.(inst_funcs) nil nil inst.(inst_globals) nil nil nil in
    let f_init := Build_frame nil inst_init in
    instantiate_globals f hs' s' m g_inits /\
    instantiate_elems f hs' s' m r_inits /\
    f = Build_frame nil inst /\
      bes = get_init_expr_elems m.(mod_elems) ++ get_init_expr_datas m.(mod_datas) ++ get_init_expr_start m.(mod_start).

Definition interp_alloc_module (s : store_record) (m : module) (imps : list extern_value) (gvs : list value) (rvs: list (list value_ref)) : (store_record * moduleinst) :=
  let i_fs := List.map N.of_nat (seq.iota (List.length s.(s_funcs)) (List.length m.(mod_funcs))) in
  let i_ts := List.map N.of_nat (seq.iota (List.length s.(s_tables)) (List.length m.(mod_tables))) in
  let i_ms := List.map N.of_nat (seq.iota (List.length s.(s_mems)) (List.length m.(mod_mems))) in
  let i_gs := List.map N.of_nat (seq.iota (List.length s.(s_globals)) (min (List.length m.(mod_globals)) (List.length gvs))) in
  let i_es := List.map N.of_nat (seq.iota (List.length s.(s_elems)) (List.length m.(mod_elems))) in
  let i_ds := List.map N.of_nat (seq.iota (List.length s.(s_datas)) (List.length m.(mod_datas))) in
  let inst := {|
    inst_types := m.(mod_types);
    inst_funcs := (List.app (ext_funcs imps) i_fs);
    inst_tables := (List.app (ext_tabs imps) i_ts);
    inst_mems := (List.app (ext_mems imps) i_ms);
    inst_globals := (List.app (ext_globs imps) i_gs);
    inst_elems := (i_es);
    inst_datas := (i_ds);
                inst_exports := (List.map (get_exportinst
                                             (Build_moduleinst nil i_fs i_ts i_ms i_gs nil nil nil)) m.(mod_exports))
  |} in
  let '(s1, _) := alloc_funcs s m.(mod_funcs) inst in
  let '(s2, _) := alloc_tabs s1 (List.map (fun t => t.(modtab_type)) m.(mod_tables)) in
  let '(s3, _) := alloc_mems s2 m.(mod_mems) in
  let '(s4, i_gs) := alloc_globs s3 m.(mod_globals) gvs in
  let '(s5, i_es) := alloc_elems s4 m.(mod_elems) rvs in
  let '(s', i_ds) := alloc_datas s5 m.(mod_datas) in
  (s', inst).

End Instantiation_spec.

