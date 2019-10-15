Require Import Coq.Lists.List.
Require Import Coq.Arith.Minus.
Import ListNotations.

Require Import AST.
Require Import Names.
Require Import BodyTypeDefs.
Require Import GenericLemmas.
Require Import GenericTactics.
Require Import Eval.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import UtilsProgram.
Require Import UtilsTypechecker.

(**************************************************************************************************)
(** * Main proofs                                                                                 *)
(**************************************************************************************************)

Theorem preservation : forall (p : program) (e1 e2 : expr) (t : TypeName),
    ((program_skeleton p) / [] |- e1 : t) ->
    [ p |- e1 ==> e2 ] ->
    (program_skeleton p) / [] |- e2 : t.
Proof.
  intros p e1 e2 t tc onestep.
  generalize dependent e2. generalize dependent t.
  induction e1 using expr_strong_ind; intros;
    inversion tc as [ sk ctx v' t'
                          | sk ctx args sn' cargs tn' HIn Ht_args tn_eq
                          | sk ctx args ex sn' dargs rtype Hin Ht_ex Ht_args
                          | sk ctx args n' argts rtype Hin Ht_args
                          | sk ctx args ex qn argts rtype Hin Ht_ex Ht_args (* E_ConsFunCallG *)
                           | sk ctx args ex qn argts rtype Hin Ht_ex Ht_args (* E_ConsFunCallL *)
                           | sk ctx args qn argts Hin Ht_args (* E_GenFunCallG *)
                           | sk ctx args qn argts Hin Ht_args (* E_GenFunCallL *)
                           | sk ctx qn ex b_exs b_ts bs cs rtype ctorlist Ht_ex bs_comb Ht_bs HlookupConstr Hexhaustive Ht_cs
                          | sk ctx qn dtors b_exs b_ts bs cs bs_comb Ht_bs HlookupDestr Hexhaustive Ht_cs
                          | sk ctx e1' e2' t1 t2
                    ];
    inversion onestep as [ prog left right argsStep args' e e' snStep HValLeft HStepInd Eargs Eargs' (* STEP_ConstrCongr *)
                         | prog argsStep e e' snStep HStepInd (* STEP_DestrCongr1 *)
                         | prog left right argsStep args' exStep e e' snStep HValLeft HValEx HStepInd Eargs Eargs' (* STEP_DestrCongr2 *)
                         | prog left right argsStep args' e e' name HValLeft HStepInd Eargs Eargs' (* STEP_FunCallCongr *)
                         | prog left right argsStep args' e e' qnStep HValLeft HStepInd Eargs Eargs' (* STEP_GenFunCallCongr *)
                         | prog argsStep e e' qnStep HStepInd (* STEP_ConsFunCallCongr1 *)
                         | prog left right argsStep args' exStep e e' qnStep HValLeft HValEx HStepInd Eargs Eargs' (* STEP_ConsFunCallCongr2 *)
                         | prog qnStep e e' rtypeStep numStep bsStep cases HStepInd (* STEP_MatchCongr1 *)
                         | prog rtypeStep e e' exStep left right bsStep bs' cases qnStep
                             HValLeft HValEx HStepInd Ebs Ebs' Ebs_snd (* STEP_MatchCongr2 *)
                         | prog qnStep e e' left right bsStep bs' cocases
                             HValLeft HStepInd Ebs Ebs' Ebs_snd (* STEP_CoMatchCongr *)
                         | prog e e' exStep HStepInd (* STEP_LetCongr *)
                         | prog var e HValV (* STEP_Let *)
                         | prog name argsStep fbody HValArgs HisFirst En_body (* STEP_FunCall *)
                         | prog matchname snStep argsStep bsStep cases body tnStep HValArgs HValBs HinStep (* STEP_Match *)
                         | prog snStep qnStep argsStep cargsStep e cfunBody H_isFirst_cfun_bods E_cfun_body H_isFirst_cfun_bod HValArgs HValCargs (* STEP_ConsFunCallG *)
                         | prog snStep qnStep argsStep cargsStep e cfunBody H_isFirst_cfun_bods E_cfun_body H_isFirst_cfun_bod HValArgs HValCargs (* STEP_ConsFunCallL *)
                         | prog argsStep bsStep cocases body matchname snStep HValArgs HValBs HinStep (* STEP_DestrComatch *)
                         | prog fargs dargsStep cocases body snStep qnStep HValFargs HValDargs HisFirstCcs HisFirstCbds (* STEP_DestrGenFunCallG *)
                         | prog fargs dargsStep cocases body snStep qnStep HValFargs HValDargs HisFirstCcs HisFirstCbds (* STEP_DestrGenFunCallL *)
                         ];
    let rec destr_gen_solve :=
         match goal with
    | [ _: E_GenFunCall (?scope _) _ = _|- _ ] =>
      subst; inversion Ht_ex; subst; clear Ht_ex; rename H5 into Hin_cmfsigs; rename H4 into Eqn; rename H6 into Ht_fargs;
        apply multisubst_typing with (argts := dargs ++ argts);
        [> clear - Ht_args Ht_fargs; generalize dependent ls; induction dargs; intros; destruct ls; try solve [inversion Ht_args];
         [> simpl; assumption
         | inversion Ht_args; subst; apply ListTypeDeriv_Cons; try assumption;
           apply IHdargs with (ls := ls); try assumption
         ]
        | match scope with
          | local =>
            pose proof (program_has_all_gfun_bods_l p) as Hwf
          | global =>
            pose proof (program_has_all_gfun_bods_g p) as Hwf
          end; unfold has_all_gfun_bods in Hwf;
          rename n into sn_destr; rename qnStep into qn_fun;
          match scope with
          | local =>
            pose proof (program_gfun_bods_typecheck_l p) as Ht_fun; unfold gfun_bods_l_typecheck in Ht_fun
          | global =>
            pose proof (program_gfun_bods_typecheck_g p) as Ht_fun; unfold gfun_bods_g_typecheck in Ht_fun
          end;
          clear H IHe1 HValDargs HValFargs;
          match scope with
          | local =>
            assert (Hlookup : lookup_gfun_bods_l p qn_fun = Some (qn_fun, cocases));
            [> apply lookup_gfun_bods_is_first_l; split; try assumption; try reflexivity |];
            assert (Hlookup_sig : lookup_gfun_sig_l (program_skeleton p) qn_fun = Some (qn_fun, argts));
            [> apply In_gfun_sig_lookup_gfun_sig_l; assumption |]
          | global =>
            assert (Hlookup : lookup_gfun_bods_g p qn_fun = Some (qn_fun, cocases));
            [> apply lookup_gfun_bods_is_first_g; split; try assumption; try reflexivity |];
            assert (Hlookup_sig : lookup_gfun_sig_g (program_skeleton p) qn_fun = Some (qn_fun, argts));
            [> apply In_gfun_sig_lookup_gfun_sig_g; assumption |]
          end;
          assert (Ht_gfun: program_skeleton p / argts |- (E_CoMatch qn_fun (index_list 0 argts) cocases) : (fst qn_fun));
          [> clear - HisFirstCbds Ht_fun Hlookup Hlookup_sig;
           match goal with
           | [ H_isfirst: is_first (?qn, ?ccs) ?bods _,
                          H_t : Forall _ ?bods |- _ ] =>
             induction bods; inversion H_isfirst; subst;
             [> inversion H_t; subst;
              match goal with
              | [ H': exists qn args, _ |- _ ] =>
                inversion H'; clear H';
                match goal with
                | [ H': exists args, _ |- _ ] => inversion H'; clear H'
                end
              end;
              match goal with
              | [ H: _ /\ _ |- _ ] => inversion_clear H
              end; simpl in *;
              match goal with
              | [ E1 : ?lookup ?sk qn  = Some (_, _), E2 : ?lookup ?sk qn = Some (_, _) |- _ ] =>
                rewrite E1 in E2; inversion E2; subst; assumption
              end
             | IH_tac Forall_tail_tac
             ]
           end
          |];
          inversion Ht_gfun; subst;
          assert (E_len: length bindings_exprs = length bindings_types);
          [> clear - H3; gen_induction bindings_exprs bindings_types; destruct bindings_exprs; try solve [inversion H3]; try reflexivity;
           simpl; f_equal; specialize (IHbindings_types bindings_exprs); IH_tac (inversion H3; assumption)
          |];
          assert (E: argts = bindings_types);
          [> clear - H2 E_len; gen_induction (0, bindings_exprs, bindings_types) argts;
           [> simpl in H2; destruct bindings_types; try reflexivity;
            destruct bindings_exprs; try solve [inversion E_len]; inversion H2
           | destruct bindings_exprs; destruct bindings_types; try solve [inversion E_len]; try solve [inversion H2];
             simpl in H2; f_equal;
             [> inversion H2; auto
             | inversion H2; specialize (IHargts bindings_types bindings_exprs);
               specialize IHargts with (n := S n); IH_tac (inversion E_len; reflexivity)
             ]
           ]
          |];
          subst argts;
          pose proof (skeleton_cdts_dtor_names_unique (program_skeleton p)) as Hx; unfold cdts_dtor_names_unique in Hx;
          clear - Hin HisFirstCcs Eqn H6 H7 H8 E_len Hx;
          apply lookup_dtors_in_dtors in H6;
          gen_induction dtorlist cocases; destruct dtorlist as [|dtor_h dtor_t]; try solve [inversion H8];
          [> inversion HisFirstCcs
          | simpl in *; inversion HisFirstCcs; subst;
            [> assert ((sn_destr, dargs, t) = dtor_h);
             [> clear - HisFirstCcs Hin Hx H7 H6; inversion H6; subst; clear H6 H2;
              destruct dtor_h as [[d_sn d_args] d_t];
              inversion H7; subst; clear - Hin Hx H1;
              induction (skeleton_dtors (program_skeleton p)); inversion H1; subst; inversion Hin; auto; subst;
              [> simpl in Hx; inversion Hx; subst; do 2 (apply In_fst in H);
               rewrite map_map in H; exfalso; apply H3; assumption
                                                          ..
              | inversion Hx; subst; IH_tac]
             |];
             inversion H7; subst; clear H2; simpl in H8; inversion H8; subst; clear H11; assumption
            | simpl in H2;
              apply IHcocases with (dtorlist := dtor_t); try assumption; try Forall_tail_tac;
              inversion H8; assumption
            ]
          ]
        ]
         end
          in let rec cons_constr_solve :=
                   subst;
      match goal with
      | [ _: _ / [] |- (E_ConsFunCall (?scope _) _ _) : _ |- _ ] =>
        match scope with
        | local =>
          pose proof (program_cfun_bods_typecheck_l p) as Ht_body; unfold cfun_bods_l_typecheck in Ht_body
        | global =>
          pose proof (program_cfun_bods_typecheck_g p) as Ht_body; unfold cfun_bods_g_typecheck in Ht_body
        end;
          inversion Ht_ex; subst;
            apply multisubst_typing with (argts := cargs ++ argts); try eassumption;
              [> subst; clear - H5 Ht_args; generalize dependent cargs; induction cargsStep; intros;
               [> destruct cargs; try solve [inversion H5]; simpl; assumption
               | destruct cargs; try solve [inversion H5]; simpl;
                 apply ListTypeDeriv_Cons; inversion H5; try assumption;
                 apply IHcargsStep; try assumption
               ]
              | destruct cfunBody as [qn' body]; inversion H7; subst qn';
                match scope with
                | local =>
                  assert (Hlookup : lookup_cfun_sig_l (program_skeleton p) qn = Some (qn, argts, t));
                  [> apply In_cfun_sig_lookup_cfun_sig_l ; try assumption |];
                  induction (program_cfun_bods_l p); try solve [inversion H_isFirst_cfun_bods]
                | global =>
                  assert (Hlookup : lookup_cfun_sig_g (program_skeleton p) qn = Some (qn, argts, t));
                  [> apply In_cfun_sig_lookup_cfun_sig_g ; try assumption |];
                  induction (program_cfun_bods_g p); try solve [inversion H_isFirst_cfun_bods]
                end;
                inversion H_isFirst_cfun_bods; subst;
                [> clear H_isFirst_cfun_bods IHc; inversion Ht_body as [| _x _y Hhead Htail]; subst;
                 inversion Hhead as [qn' [argts' [t' Hhead1]]]; clear Hhead;
                 inversion Hhead1 as [Hhead_lookup Hhead_t]; clear Hhead1;
                 inversion Hhead_t; subst; clear Hhead_t;
                 simpl fst in *; simpl snd in *; rewrite Hhead_lookup in Hlookup; inversion Hlookup; subst;
                 clear Htail Ht_body;
                 rename H17 into Ht_bodies, H2 into Hin_ctors, H5 into Ht_cargs, H7 into Eqn, H14 into Ht_bindings;
                 rename H12 into Ecombine, H8 into Ht_e, H15 into Hlookup_constr, H16 into Hnames_match; clear H13 H9 Eqn;
                 let H_Ecargs := fresh in
                 assert (H_Ecargs : forall cargs', In (snStep, cargs') ctorlist -> cargs = cargs');
                 [> intros cargs' Hin_ctorlist; apply constructor_type_unique with (sk := program_skeleton p) (sn := snStep) (ctorlist := ctorlist); try rewrite <- Ht_e; assumption |];
                 clear Hlookup_constr;
                 generalize dependent argts; generalize dependent ctorlist; induction body; intros; try solve [inversion H_isFirst_cfun_bod]; subst;
                 inversion H_isFirst_cfun_bod; subst;
                 [> destruct ctorlist as [|ctor ctorlist]; try solve [inversion Ht_bodies];
                  inversion Hnames_match as [|_x _xx Ector _]; destruct ctor as [ctor_sn ctor_ts]; subst;
                  simpl snd in *;
                  let Ecargs := fresh in
                  assert (Ecargs : cargs = ctor_ts);
                  [> apply H_Ecargs; simpl; auto |];
                  remember (index_list 1 argts) as comb;
                  assert (E_len: length bindings_exprs = length bindings_types);
                  [> clear - Ht_bindings;
                   gen_induction bindings_exprs bindings_types; destruct bindings_exprs; inversion Ht_bindings; try reflexivity; subst;
                   simpl; f_equal; IH_auto_tac |];
                  assert (Eargts : argts = bindings_types);
                  [> clear - Ecombine Heqcomb E_len; rewrite Heqcomb in Ecombine; clear Heqcomb;
                   gen_induction (bindings_exprs, bindings_types, 1) argts; destruct bindings_exprs; destruct bindings_types; try solve [inversion E_len]; try solve [inversion Ecombine]; try reflexivity;
                   simpl in Ecombine; f_equal;
                   [> inversion Ecombine; auto
                   | remember (S n) as m; inversion Ecombine; inversion E_len; IH_auto_tac
                   ]
                  |];
                  inversion Ht_bodies; subst; assumption
                 | destruct ctorlist as [|ctor ctorlist]; try solve [inversion Ht_bodies];
                   apply IHbody with (ctorlist := ctorlist); try assumption;
                   [> inversion Hnames_match; assumption
                   | inversion Ht_bodies; subst; assumption
                   | intros; apply H_Ecargs; simpl; auto
                   ]
                 ]
                | apply IHc; clear IHc; try assumption;
                  inversion Ht_body as [| _x _y Hhead Htail]; assumption
                ]
              ]
      end
           in [> | | | | destr_gen_solve | destr_gen_solve | | | | | cons_constr_solve | | | | | cons_constr_solve | .. ]
  .

  (* STEP_ConstrCongr *)
  - subst. apply preservation_in_list with (e' := e') in Ht_args; try assumption.
   apply T_Constr with (cargs := cargs); try assumption; try reflexivity.
   (* STEP_DestrCongr1 *)
  - subst. apply T_DestrCall with (dargs := dargs); try assumption.
   apply IHe1; try assumption.
   (* STEP_DestrCongr2 *)
  - subst. apply preservation_in_list with (e' := e') in Ht_args; try assumption.
   apply T_DestrCall with (dargs := dargs); try assumption; try reflexivity.
   (* STEP_DestrComatch *)
  - subst. inversion Ht_ex; subst; clear Ht_ex.
    rename H7 into Ht_bs; rename H8 into Hlookup; rename H9 into Hnames_match;
      rename H10 into Ht_ccs; rename H3 into Esn.
    assert (Elen : List.length bindings_exprs = List.length bindings_types).
    clear - Ht_bs; generalize dependent bindings_exprs; induction bindings_types; intros;
      try solve [inversion Ht_bs; reflexivity];
      inversion Ht_bs; subst; simpl; f_equal; apply IHbindings_types; assumption.
    rewrite map_fst_combine; try assumption; clear Elen.
    apply multisubst_typing with (argts := dargs ++ bindings_types).
    + clear - Ht_bs Ht_args. generalize dependent dargs; induction ls; intros.
       * destruct dargs; try solve [inversion Ht_args]. simpl. assumption.
       * destruct dargs; try solve [inversion Ht_args]. simpl.
         apply ListTypeDeriv_Cons; inversion Ht_args; try assumption.
         apply IHls; try assumption.
    + assert (H_Edargs : forall dargs' t', In (n, dargs', t') dtorlist -> dargs = dargs' /\ t = t').
      intros dargs' t' Hin'; rewrite Esn in Hlookup;
        apply destructor_type_unique with (sk := program_skeleton p) (sn := n) (t' := t') (t := t) (dtorlist := dtorlist);
        try assumption.
      clear Hlookup tc onestep IHe1.
      generalize dependent dtorlist; induction cocases; intros; try solve [inversion HinStep]; subst.
      inversion HinStep; subst;
        destruct dtorlist as [|dtor dtorlist]; try solve [inversion Ht_ccs].
      * inversion Hnames_match as [|_x _xx Edtor _]; destruct dtor as [[dtor_sn dtor_ts] dtor_t]; subst.
        assert (Edargs : dargs = dtor_ts /\ t = dtor_t).
        apply H_Edargs; left; reflexivity.
        inversion Edargs.
        inversion Ht_ccs; subst; assumption.
      * apply IHcocases with (dtorlist := dtorlist); try assumption.
        -- inversion Hnames_match; assumption.
        -- inversion Ht_ccs; assumption.
        -- intros; apply H_Edargs with (t' := t'); right; assumption.
   (* STEP_FunCallCongr *)
  - subst. apply preservation_in_list with (e' := e') in Ht_args; try assumption.
   apply T_FunCall with (argts := argts); try assumption; try reflexivity.
  (* STEP_FunCall *)
  - subst. pose proof (program_fun_bods_typecheck p) as Ht_body. unfold fun_bods_typecheck in Ht_body.
   eapply multisubst_typing; try eassumption.
   assert (Hlookup : lookup_fun_sig (program_skeleton p) (fst (fst (n, argts, t))) = Some (n, argts, t));
     [> apply in_fun_sigs_lookup_fun_sig; try assumption | simpl in Hlookup].
   induction (program_fun_bods p); try solve [inversion HisFirst].
   inversion HisFirst; subst.
   +inversion Ht_body as [| _x _y Hhead Htail]; subst.
    inversion Hhead as [n' [argts' [t' Hhead1]]]; clear Hhead; rename Hhead1 into Hhead.
    inversion Hhead as [Hhead_lookup Hhead_t].
    simpl in Hhead_lookup; rewrite Hhead_lookup in Hlookup. inversion Hlookup. subst. assumption.
   +apply IHf; clear IHf; try assumption.
    inversion Ht_body as [| _x _y Hhead Htail]. assumption.
  (* STEP_MatchFunCallCongr1 global *)
  -  subst; apply T_GlobalConsFunCall with (argts := argts); try assumption; try reflexivity;
     apply IHe1; try assumption.
  (* STEP_MatchFunCallCongr2 global *)
  - subst; apply preservation_in_list with (e' := e') in Ht_args; try assumption;
   apply T_GlobalConsFunCall with (argts := argts); try assumption; try reflexivity.
  (* STEP_ComatchFunCallCongr *)
  - subst. match goal with
           | [ E: _ = _  |- _ ] => inversion E
           end.
  (* STEP_MatchFunCallCongr1 local *)
  -  subst; apply T_LocalConsFunCall with (argts := argts); try assumption; try reflexivity;
     apply IHe1; try assumption.
  (* STEP_MatchFunCallCongr2 local *)
  - subst; apply preservation_in_list with (e' := e') in Ht_args; try assumption;
      apply T_LocalConsFunCall with (argts := argts); try assumption; try reflexivity.
    (* __ local *)
  - subst; match goal with
           | [ E: _ = _ |- _ ] => inversion E
           end.
  - subst; apply preservation_in_list with (e' := e') in Ht_args; try assumption;
      apply T_GlobalGenFunCall with (argts := argts); try assumption; try reflexivity.
  - subst. apply preservation_in_list with (e' := e') in Ht_args; try assumption;
    apply T_LocalGenFunCall with (argts := argts); try assumption; try reflexivity.
  (* STEP_MatchCongr1 *)
  - subst. apply T_Match with (bindings_exprs := b_exs) (bindings_types := b_ts) (ctorlist := ctorlist); try assumption; try reflexivity.
   apply IHe1; try assumption.
  (* STEP_MatchCongr2 *)
  - subst. assert (Elen : List.length b_exs = List.length b_ts). apply typeDerivList_lenghts_eq in Ht_bs; assumption.
   assert (Ebex : b_exs = left ++ [e] ++ right).
   +apply map_fst_combine in Elen. rewrite Elen in *. assumption.
   +rewrite <- map_fst_as_patternmatch in H0. rewrite Ebex in *.
    rewrite map_fst_combine in H0; try assumption.
    apply preservation_in_list with (e' := e') in Ht_bs; try assumption.
    rewrite map_snd_combine in Ebs_snd; try assumption. rewrite Ebs_snd in *.
    apply T_Match with (bindings_exprs := map fst bs') (bindings_types := map snd bs') (ctorlist := ctorlist); try assumption; try reflexivity.
    *apply combine_fst_snd.
    *rewrite <- Ebs' in Ht_bs. assumption.
  (* STEP_Match *)
  - subst. assert (Elen_bindings : List.length b_exs = List.length b_ts).
    clear - Ht_bs; generalize dependent b_ts; induction b_exs; intros;
      try solve [inversion Ht_bs; subst; reflexivity];
      inversion Ht_bs; simpl; f_equal. apply IHb_exs; try assumption.
    rewrite map_fst_combine; try assumption; clear Elen_bindings.
    inversion Ht_ex; subst.
    apply multisubst_typing with (argts := cargs ++ b_ts).
    + rename H6 into Ht. clear - Ht Ht_bs. generalize dependent cargs; induction argsStep; intros.
      * destruct cargs; try solve [inversion Ht]. simpl. assumption.
      * destruct cargs; try solve [inversion Ht]. simpl.
        apply ListTypeDeriv_Cons; inversion Ht; try assumption.
        apply IHargsStep; try assumption.
    + rename H3 into Hin; rename H6 into Ht_sim; rename H8 into Esn.
      assert (H_Ecargs : forall cargs', In (snStep, cargs') ctorlist -> cargs = cargs').
      intros cargs' Hin'; rewrite Esn in HlookupConstr;
        apply constructor_type_unique with (sk := program_skeleton p) (sn := snStep) (ctorlist := ctorlist);
        try assumption.
      clear HlookupConstr tc Ht_ex onestep.
      generalize dependent ctorlist; induction ls; intros; try solve [inversion HinStep]; subst.
      inversion HinStep; subst;
        destruct ctorlist as [|ctor ctorlist]; try solve [inversion Ht_cs].
      * inversion Hexhaustive as [|_x _xx Ector _]; destruct ctor as [ctor_sn ctor_ts]; subst.
        assert (Ecargs : cargs = ctor_ts).
        apply H_Ecargs; left; reflexivity.
        inversion Ht_cs; subst; assumption.
      * apply IHls with (ctorlist := ctorlist); try assumption.
        ++ inversion H; assumption.
        ++ inversion Hexhaustive; assumption.
        ++ inversion Ht_cs; assumption.
        ++ intros; apply H_Ecargs. right; assumption.
  (* STEP_CoMatchCongr *)
  - subst. assert (Elen : List.length b_exs = List.length b_ts). apply typeDerivList_lenghts_eq in Ht_bs; assumption.
   assert (Ebex : b_exs = left ++ [e] ++ right).
   +apply map_fst_combine in Elen. rewrite Elen in *. assumption.
   +rewrite <- map_fst_as_patternmatch in H0. rewrite Ebex in *.
    rewrite map_fst_combine in H0; try assumption.
    apply preservation_in_list with (e' := e') in Ht_bs; try assumption.
    rewrite map_snd_combine in Ebs_snd; try assumption. rewrite Ebs_snd in *.
    apply T_CoMatch with (bindings_exprs := map fst bs') (bindings_types := map snd bs') (dtorlist := dtors); try assumption; try reflexivity.
    *apply combine_fst_snd.
    *rewrite <- Ebs' in Ht_bs. assumption.
  (* STEP_LetCongr *)
  - subst.
   apply T_Let with (t1 := t1); try assumption.
   apply IHe1_1; try assumption.
  (* STEP_Let *)
  - subst. apply subst_typing with (t' := t1); try assumption.
Qed.
