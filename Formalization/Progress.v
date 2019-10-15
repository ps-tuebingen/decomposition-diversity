(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: Progress.v                                                                               *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Require Import GenericLemmas.
Require Import GenericTactics.
Require Import AST.
Require Import Names.
Require Import BodyTypeDefs.
Require Import Eval.
Require Import OptionMonad.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import UtilsProgram.
Require Import Typechecker.

(**************************************************************************************************)
(** * Main proofs                                                                                 *)
(**************************************************************************************************)

Proposition progress_right : forall (e : expr) (p : program) (tc : exists t, (program_skeleton p) / [] |- e : t),
    one_step_eval p e = None -> value_b e = true.
Proof.
  intros.
    let consfun_tac :=
 clear tc'; subst; simpl; simpl in H; destruct (value_b e) eqn:Ee;
      [> destruct e; try (simpl in Ee; assumption);
       [> (* e = E_Constr *)
        destruct (forallb value_b ls) eqn:Efb;
        [> (* Efb: forallb value_b ls = true *)
         rewrite <- monad_law3 in H; repeat (apply eta_always_something in H);
         inversion Ht_ex; subst;
         (* either lookupMatchFunctionBody or lookupCase must produce None, but this is impossible *)
         match goal with
         | [ _:?lookup ?p ?sn >>= _ = _ |- _ ] =>
           assert (HlookupMFSome : exists body, lookup p sn = Some body)
         end;
         [>  match goal with
             | [ H: In _ (skeleton_cfun_sigs_l _) |- _ ] =>
               pose proof (program_has_all_cfun_bods_l p) as H_all_cfuns; pose proof (cfun_bods_unique_l p) as H_unique
             | [ H: In _ (skeleton_cfun_sigs_g _) |- _ ] =>
               pose proof (program_has_all_cfun_bods_g p) as H_all_cfuns; pose proof (cfun_bods_unique_g p) as H_unique
             end;
          unfold has_all_cfun_bods in H_all_cfuns;
          apply fst_fst_eq_translates_In with (a := qn) (b := argts) (d := t) in H_all_cfuns; [> | assumption];
          clear Hin; inversion H_all_cfuns as [body Hin]; clear H_all_cfuns;
          clear - H_unique Hin;
          exists (qn, body); apply lookup_cfun_bods_scoped_is_first; eexists; split; eauto;
          match type of Hin with
          | In _ ?bods =>
            match bods with
            | program_cfun_bods_l _ => right
            | program_cfun_bods_g _ => left
            end;
            induction bods
          end; inversion Hin;
          [> subst; split; eauto; eapply is_first_head
          | simpl; split; auto; apply is_first_tail; try assumption;
            [> simpl; destruct (eq_QName qn (fst a)) eqn:E; try reflexivity;
             apply eq_QName_eq in E; subst qn; inversion H_unique; subst;
             apply In_fst in H; contradiction
            | inversion H_unique; apply IHc; try assumption
            ]
          ]
         |];
         inversion HlookupMFSome as [body E]; rewrite E in H; simpl in H;
         assert (H_lookup : exists case, lookup_case (snd body) s = Some case);
         [> match goal with
            | [ _: lookup_cfun_bods_scoped _ ?sn = Some _ |- _ ] =>
              apply lookup_cfun_case_succeeds with (p := p) (sn_cfun := sn); try assumption;
              exists []; map_tac ltac:(fun x => exists x) (ls, l, t);
              match sn with
              | local _ => apply T_LocalConsFunCall with (argts := argts)
              | global _ => apply T_GlobalConsFunCall with (argts := argts)
              end; try assumption
            end
         |];
         inversion H_lookup as [case E']; rewrite E' in H; inversion H
        | (* Efb: forallb value_b ls = false *)
        apply eta_always_something in H;
        clear Hin; generalize dependent argts;
        induction ls; try solve [inversion Efb];
        simpl in *; intros; destruct argts as [|argt argts]; try solve [inversion Ht_args]; destruct (value_b a) eqn:Ea;
        [> apply IHls with (argts := argts); try assumption;
         [> inversion H0; assumption
         | apply eta_always_something in H; assumption
         | inversion Ht_args; assumption]
        | inversion H0; rewrite Ea in H3; apply eta_always_something in H; apply H3; try assumption;
          inversion Ht_args; exists argt; assumption
        ]
        ]
       | (* e = E_ComatchFunCall *)
       rename qn into qn_cfun; inversion Ht_ex; subst; rename qn into qn_gfun;
       (* this cannot be well-typed, a Match- and Comatch-function cannot have the same type *)
       pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Hunique; unfold dts_cdts_disjoint in Hunique;
       match goal with
       | [ H: _ / _ |- (E_GenFunCall ?sn _) : _ |- _ ] =>
         match sn with
         | local _ =>
           pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as Hcmf_in_cds; unfold gfun_sigs_in_cdts in Hcmf_in_cds
         | global _ =>
           pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as Hcmf_in_cds; unfold gfun_sigs_in_cdts in Hcmf_in_cds
         end
       end;
       match goal with
       | [ H: (if _ then _ else _ >>= fun _ => Some (E_ConsFunCall ?sn _ _)) = _ |- _ ] =>
         match sn with
         | local _ => pose proof (skeleton_cfun_sigs_in_dts_l  (program_skeleton p)) as Hmf_in_cds
         | global _ => pose proof (skeleton_cfun_sigs_in_dts_g  (program_skeleton p)) as Hmf_in_cds
         end; unfold cfun_sigs_in_dts in Hmf_in_cds
       end;
       clear IHe; destruct qn_cfun as [t_cfun n_cfun]; destruct qn_gfun as [t_gfun n_gfun]; simpl in *;
       subst t_gfun;
       exfalso; specialize Hunique with t_cfun; apply Hunique; split;
       match goal with
       | [ H_forall: Forall (fun x => In _ ?dts) ?sigs |- In ?t ?dts ] =>
         match goal with
         | [ H_in: In _ sigs |- _ ] =>
           induction sigs; inversion H_in;
           [> subst; inversion H_forall; subst; assumption
           | IH_tac (inversion H_forall; assumption)
           ]
         end
       end
       | (* e = E_CoMatch *)
       inversion Ht_ex; subst;
       (* this is not well-typed, since MatchFunctions and CoMatches cannot have the same type
        we show this by proving that there cannot be constructors and destructors of the same type *)
       match goal with
       | [ H: context [E_ConsFunCall ?sn _ _] |- _ ] =>
         match sn with
         | global _ =>
           pose proof (program_cfun_bods_typecheck_g p) as Ht_cfun;
           unfold cfun_bods_g_typecheck in Ht_cfun;
           assert (exists body, lookup_cfun_bods_g p qn = Some body);
           [> let H := fresh in
              pose proof (program_has_all_cfun_bods_g p) as H; unfold has_all_cfun_bods in H;
              apply in_cfun_bods_lookup_cfun_g; fst_eq_translates_In_tac |]
         | local _ =>
           pose proof (program_cfun_bods_typecheck_l p) as Ht_cfun;
           unfold cfun_bods_l_typecheck in Ht_cfun;
           assert (exists body, lookup_cfun_bods_l p qn = Some body);
           [> let H := fresh in
              pose proof (program_has_all_cfun_bods_l p) as H; unfold has_all_cfun_bods in H;
              apply in_cfun_bods_lookup_cfun_l; fst_eq_translates_In_tac |]
         end
       end;
       assert (HlookupConstr : exists ctorlist, lookup_ctors (program_skeleton p) (fst qn) = Some ctorlist);
       [> match goal with
          | [ H: exists body, ?lookup p _ = Some body |- _ ] =>
            let body := fresh "body" in
            let H' := fresh H in
            inversion H as [body H']; clear H; rename H' into H;
            match lookup with
            | lookup_cfun_bods_g => rewrite lookup_cfun_bods_g_scoped in H
            | lookup_cfun_bods_l => rewrite lookup_cfun_bods_l_scoped in H
            end
          end;
        destruct body0;
        match goal with
        | [ _: lookup_cfun_bods_scoped _ ?sn = Some _ |- _ ] =>
          match sn with
          | local _ => assert (In (qn, c) (program_cfun_bods_l p))
          | global _ => assert (In (qn, c) (program_cfun_bods_g p))
          end;
          [> match sn with
             | local _ => apply lookup_cfun_bods_scoped_in_cfun_bods_l
             | global _ => apply lookup_cfun_bods_scoped_in_cfun_bods_g
             end; try assumption;
           assert (E: qn = q0);
           [> match goal with
              | [ H: lookup_cfun_bods_scoped ?p (?scope ?qn) = Some (?q, ?c) |- _ ] =>
                apply lookup_cfun_bods_scoped_fst in H; inversion H;
                match goal with
                | [ E: (q, _) = (unscope (scope qn), _) |- _ ] => inversion E; reflexivity
                end
              end |];
           rewrite <- E in *; assumption
          |]
        end;
        match goal with
        | [ H: Forall (fun body => exists y x z, _ /\ _) ?cfun_bods |- _ ] =>
          induction cfun_bods; inversion H2;
          [> let H'' := fresh in
             inversion H; subst;
             match goal with
             | [ H': exists qn args t, _ /\ _ / _ |- _ : _ |- _ ] =>
               let qn := fresh "qn" in
               let args := fresh "args" in
               let t := fresh "t" in
               inversion H' as [qn [args [t H'']]];
               apply proj2 in H''; inversion H''; eauto
             end
          | IH_tac ltac:(Forall_tail_tac; assumption)
          ]
        end
       |];
       (*apply matchbody_has_constructors with (body := body); try assumption.*)
       assert (HlookupDestr : exists dtorlist, lookup_dtors (program_skeleton p) (fst qn) = Some dtorlist);
       [> exists dtorlist; rewrite <- H4; assumption |];
       pose proof (conj HlookupConstr HlookupDestr) as Hpair; apply no_simultaneous_xtors in Hpair; contradiction
       ]
      | apply eta_always_something in H; IH_tac ltac:(try assumption; eauto)
      ] in
                                       let genfun_tac :=
                                             subst; simpl; simpl in H; clear Hin tc'; generalize dependent argts; induction ls; try reflexivity;
   simpl in *; destruct (value_b a) eqn:Ea;
   [> simpl in *; destruct (forallb value_b ls) eqn:Efb; try reflexivity;
    intros; destruct argts as [| argt argts]; try solve [inversion Ht_args]; apply IHls with (argts := argts); try assumption;
    [> inversion H0; assumption
    | repeat (apply eta_always_something in H); apply eta_always_something; assumption
    | inversion Ht_args; assumption
    ]
   | intros; simpl; simpl in H; repeat (apply eta_always_something in H);
    inversion H0; rewrite Ea in H3; apply H3; try assumption;
      inversion Ht_args; exists t; assumption
   ] in

  induction e using expr_strong_ind;
    inversion_clear tc as [ t tc' ];
    inversion tc' as [ sk ctx v' t' (* E_Var *)
                           | sk ctx args sn' cargs tn' HIn Ht_args tn_eq (* E_Constr *)
                           | sk ctx args ex sn' dargs rtype Hin Ht_ex Ht_args (* E_DestrCall *)
                           | sk ctx args n' argts rtype Hin Ht_args (* E_FunCall *)
                           | sk ctx args ex qn argts rtype Hin Ht_ex Ht_args (* E_ConsFunCallG *)
                           | sk ctx args ex qn argts rtype Hin Ht_ex Ht_args (* E_ConsFunCallL *)
                           | sk ctx args qn argts Hin Ht_args (* E_GenFunCallG *)
                           | sk ctx args qn argts Hin Ht_args (* E_GenFunCallL *)
                           | sk ctx qn ex b_exs b_ts bs cs tn' ctorlist Ht_ex bs_comb Ht_bs HlookupConstr H_comb Ht_cs (* E_Match *)
                           | sk ctx qn dtors b_exs b_ts bs cs bs_comb Ht_bs HlookupDestr  Ht_cs (* E_Comatch *)
                           | sk ctx e1' e2' t1 t2 (* E_Let *)
                     ]; [> | | | | consfun_tac | consfun_tac | genfun_tac | genfun_tac | | | ].
  (* E_Var *)
  - destruct v; simpl in H0; inversion H0.
  (* E_Constr *)
  - clear tc'; subst. simpl in H. intros. apply eta_always_something in H. clear HIn. generalize dependent cargs. induction ls; try reflexivity.
    + simpl. inversion H0; subst. clear H0. destruct (value_b a).
      * intros cargs Hderiv. simpl. induction cargs.
        -- inversion Hderiv.
        -- apply IHls with (cargs := cargs); clear IHls; try assumption.
           ++ apply eta_always_something in H. apply H.
           ++ inversion Hderiv. assumption.
      * intros. simpl. apply H3; try assumption.
        -- inversion Ht_args. exists t. assumption.
        -- apply eta_always_something in H. assumption.
  (* E_DestrCall *)
  - clear tc'; subst. simpl. simpl in H. destruct (value_b e) eqn:Ee.
    + clear IHe. destruct (forallb value_b ls) eqn:Evls.
    (* forallb value_b ls = true *)
      * destruct e; try (simpl in Ee; assumption).
     (* e = E_Constr *)
      -- clear H. inversion Ht_ex as [ | _x _xx tn _yy ts _z HinCtor _ E_qn | | | | | | | | | ]; subst.
       assert (HlkConstr : exists ctors, lookup_ctors (program_skeleton p) (fst (unscope s)) = Some ctors).
       { apply in_ctors_lookup_ctors in HinCtor; assumption. }
       assert (HlkDestr : exists dtors, lookup_dtors (program_skeleton p) (fst (unscope n)) = Some dtors).
       { apply in_dtors_lookup_dtors in Hin; assumption. }
       pose proof (conj HlkConstr HlkDestr) as Hpair. rewrite E_qn in *.
       apply no_simultaneous_xtors in Hpair. contradiction.
     (* e = E_ComatchFunCall *)
      -- inversion Ht_ex; subst;
         let rec solve_tac :=
             pose proof H6 as HinCmfsig; clear H6; pose proof H7 as Ht_l; clear H7; pose proof H5 as E_q_n; clear H5;
               match goal with
               | [ H: context [lookup_gfun_bods_scoped p ?sn] |- _ ] =>
                 destruct (lookup_gfun_bods_scoped p sn) eqn:HlookupCMFBody;
                   [> simpl in H; apply eta_always_something in H; pose proof H as HlookupCocase; clear H;
                    (* lookupCocase l0 n = None is impossible *)
                    assert (Hdiff : exists x, lookup_cocase (snd g) n = Some x);
                    [> apply lookup_gfun_cocase_succeeds with (p := p) (sn_gfun := sn); try assumption;
                     exists []; exists l; exists ls; exists t; apply T_DestrCall with (dargs := dargs); try assumption
                    | inversion Hdiff; rewrite H in HlookupCocase; inversion HlookupCocase ]
                   | clear - HlookupCMFBody HinCmfsig;
                     (* lookupComatchFunctionBody p q = None is impossible *)
                     match goal with
                     | [ _: lookup_gfun_bods_scoped ?p ?sn = _ |- _ ] =>
                       assert (HlookupSome : exists body, lookup_gfun_bods_scoped p sn = Some body)
                     end;
                     [> simpl in HlookupCMFBody;
                      simpl; match sn with
                             | local _ =>
                               pose proof (program_has_all_gfun_bods_l p)
                             | global _ =>
                               pose proof (program_has_all_gfun_bods_g p)
                             end;
                      inversion H; clear H;
                      match goal with
                      | [ Hin: In (?a1, ?b1) ?ls |- _ ] =>
                        match goal with
                        | [ E: map fst ls = map fst ?rs |- exists body, _ _ _ = Some body ] =>
                          progress (apply fst_eq_translates_In with (a := a1) (b := b1) in E; try assumption)
                        end
                      end;
                      match goal with
                      | [ Hin: exists x, In _ _ |- _ ] =>  let H := fresh "Hin" in inversion Hin as [body H]
                      end;
                      eexists; apply lookup_gfun_bods_scoped_is_first;
                      eexists; split; eauto;
                      instantiate (1 := (qn, body)); clear H1;
                      match goal with
                      | [ H: In _ (skeleton_gfun_sigs_g _) |- _ ] =>
                        left; pose proof (gfun_bods_unique_g p) as H_unique;
                        induction (program_gfun_bods_g p)
                      | [ H: In _ (skeleton_gfun_sigs_l _) |- _ ] =>
                        right; pose proof (gfun_bods_unique_l p) as H_unique;
                        induction (program_gfun_bods_l p)
                      end; try solve [inversion Hin]; split; try reflexivity;
                      simpl; inversion Hin;
                      [> subst; apply is_first_head
                      | apply is_first_tail;
                        [> simpl; destruct (eq_QName qn (fst a)) eqn:E; try reflexivity;
                         apply eq_QName_eq in E; subst qn; inversion H_unique; subst;
                         apply In_fst in H; contradiction
                        | simpl in H_unique; inversion H_unique; subst;
                          specialize (IHg H H3); inversion IHg; assumption ]
                      ]
                     | inversion HlookupSome; rewrite HlookupCMFBody in H; inversion H]
                   ]
               end
         in [> solve_tac | solve_tac].
     (* e = E_CoMatch *)
      -- assert (Ht : program_skeleton p / [] |- (E_DestrCall n (E_CoMatch q l l0) ls) : t);
         [> apply T_DestrCall with (dargs := dargs); assumption |].
        assert (HlookupSome : exists c, lookup_cocase l0 n = Some c);
         [> clear - Ht; apply lookup_comatch_cocase_succeeds with (p := p) (qn := q); repeat eexists; eassumption |].
       inversion HlookupSome. rewrite H1 in H. inversion H.
    (* forallb value_b ls = false *)
    *apply eta_always_something in H. clear - H Evls Ee H0 Ht_args.
     generalize dependent dargs.
     induction ls; try solve [inversion Evls].
     intros. destruct (value_b a) eqn:Ea.
     **induction dargs; try inversion Ht_args; subst.
       apply IHls with (dargs := dargs); try assumption.
       ***inversion H0. assumption.
       ***simpl in Evls. rewrite Ea in Evls. auto.
       ***apply eta_always_something in H. assumption.
     **apply eta_always_something in H.
       inversion H0 as [| _x _xx Ht _ _y]; subst. rewrite Ea in Ht. apply Ht; try assumption.
       ***inversion Ht_args. exists t. assumption.
   +apply eta_always_something in H. apply IHe; try assumption. eauto.
  (* E_FunCall *)
  -clear tc'; subst. simpl in H; simpl.
   assert (HlookupSome : exists body, lookup_fun_bods p n = Some body);
   [> clear - Hin;
     pose proof (program_has_all_fun_bods p) as E; unfold has_all_fun_bods in E;
     apply fst_fst_eq_translates_In with (a := n) (b := argts) (d := t) in E; try assumption; clear Hin; inversion_clear E as [c Hin];
     eexists; apply lookup_fun_bods_is_first;
     pose proof (fun_bods_unique p) as H_unique; induction (program_fun_bods p); inversion Hin;
       [> subst; apply is_first_head
       | apply is_first_tail; simpl;
         [> destruct (eq_Name n (fst a)) eqn:E; try assumption;
          apply eq_Name_eq in E; subst n; inversion H_unique; subst;
          apply In_fst in H; contradiction
         | inversion H_unique; apply IHf; try assumption]
       ]
   |]; inversion_clear HlookupSome as [body E_lookup]; rewrite E_lookup in H.
   clear Hin. generalize dependent argts; induction ls.
   +simpl in H.  inversion H.
   +simpl in H. destruct (value_b a) eqn:Ea; simpl in *.
    *intros. destruct argts as [|argt argts]; try solve [inversion Ht_args].
     apply IHls with (argts := argts); try assumption.
     **inversion H0. assumption.
     **destruct (forallb value_b ls).
       *** inversion H.
       *** repeat (apply eta_always_something in H). apply eta_always_something. assumption.
     **inversion Ht_args. assumption.
    *intros. repeat (apply eta_always_something in H). inversion H0. rewrite Ea in H3. apply H3; try assumption.
     destruct argts as [|argt argts]; try inversion Ht_args.  exists argt. assumption.
  (* E_Match *)
  - subst. simpl. simpl in H. destruct_with_eqn (value_b e).
   +rewrite <- forallb_compose in H.
    simpl in H. destruct e eqn:Ee; try (simpl in Heqb; assumption).
    (* e = E_Constr *)
    *remember (combine b_exs b_ts) as es.
     destruct (forallb (compose value_b fst) es) eqn:HeqAllBs.
     **rewrite eta_always_something in H. clear IHe HeqAllBs H1 H0 Heqb.
       inversion Ht_ex; subst.
       assert (Hctorlist : In (s,cargs) ctorlist);
         [> rewrite H7 in *; apply lookup_ctors_In_propagates with (sk := program_skeleton p); try assumption |].
       assert (E: map fst ls = map fst ctorlist).
       { clear - H_comb Ht_cs.
         gen_induction ls ctorlist;
           destruct ls; try reflexivity; inversion Ht_cs; subst.
         simpl. f_equal.
         - inversion H_comb; subst. destruct p0; destruct a; auto.
         - apply IHctorlist; try assumption.
           simpl in H_comb. Forall_tail_tac.
       }
       assert (Hx: exists case, In (s, case) ls).
       {
         clear - E Hctorlist. gen_induction ctorlist ls; destruct ctorlist; try solve [inversion E].
         - inversion Hctorlist.
         - simpl in E. inversion E. inversion Hctorlist.
           + subst p. destruct a; simpl in H0. eexists. left. rewrite H0. eauto.
           + specialize (IHls ctorlist H H1). inversion IHls. eexists. right. eassumption.
       }
       assert (Hls : exists c, lookup_case ls s = Some c);
       [> apply in_cases_lookup_case; eauto |].
       inversion Hls. rewrite H0 in H. inversion H.
     **clear Ht_cs tc'. rename Heqes into bs_comb. generalize dependent b_exs. generalize dependent b_ts. induction es.
       ***intros. auto.
       ***intros. destruct a as [a_e a_t]. unfold compose in HeqAllBs. simpl in HeqAllBs. destruct (value_b a_e) eqn:Heqe.
          ****repeat (apply eta_always_something in H). destruct b_exs as [| bex bexs]; simpl in bs_comb; destruct b_ts as [| bt bts]; try inversion bs_comb. apply IHes with (b_ts := bts) (b_exs := bexs); try assumption.
              *****clear - H0 H1 H. rewrite H. reflexivity.
              *****clear - H1. simpl in H1. Forall_tail_tac.
              *****inversion Ht_bs; subst. assumption.
          ****repeat (apply eta_always_something in H). destruct b_exs as [| bex bexs]; simpl in bs_comb; destruct b_ts as [| bt bts]; try inversion bs_comb. inversion_clear H1. subst a_e. rewrite <- Heqe. apply H2; auto.
              *****exists bt. inversion Ht_bs. assumption.
    (* e = E_ComatchFunCall *)
    * let solve_tac :=
     (* this cannot be well-typed. We show this by proving that the type of match and genfuncall cannot be
        a datatype and a codatatype at the same time *)
          pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Hunique;
            unfold dts_cdts_disjoint in Hunique;
            match goal with
            | [ _: _ / [] |- (E_GenFunCall ?sn _) : _ |- _ ] =>
              match sn with
              | local _ =>
                pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as Hcmf_in_cds
              | global _ =>
                pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as Hcmf_in_cds
              end
            end;
            unfold gfun_sigs_in_cdts in Hcmf_in_cds;
            rewrite <- H6 in HlookupConstr; destruct qn as [ q1 q2 ]; simpl in *;
       exfalso; specialize Hunique with q1; apply Hunique; clear Hunique H IHe;
         split;
         [> (* show that q1 is a datatype *)
          apply lookup_ctors_in_dts in HlookupConstr; assumption
         | (* show that q1 is a codatatype *)
         match goal with
         | [ H_in: In (?qn,_,_) ?sigs |- In ?qn ?cdts ] =>
           match goal with
           | [ H_forall: Forall _ sigs |- _ ] =>
             clear - H_in H_forall; induction sigs;
             inversion H_in;
             [> inversion H_forall; subst; assumption
             | IH_tac ltac:(try assumption; Forall_tail_tac)
             ]
           end
         end
         ]
           in inversion Ht_ex; subst; [> solve_tac | solve_tac ].
    (* e = E_CoMatch *)
    *inversion Ht_ex; subst. rewrite <- H5 in HlookupConstr.
     (* again, this cannot be well-typed. Since both lookupXtors produce a result, this is immediate with the given lemma *)
     assert (Hlc : exists ctors, lookup_ctors (program_skeleton p) (fst q) = Some ctors).  exists ctorlist; assumption.
     assert (Hld : exists dtors, lookup_dtors (program_skeleton p) (fst q) = Some dtors). exists dtorlist; assumption.
     assert (Hpair := conj Hlc Hld). apply no_simultaneous_xtors in Hpair. inversion Hpair.
   +apply eta_always_something in H. apply IHe; try assumption.
    exists (fst n). assumption.
  (* E_CoMatch *)
  -clear tc'; subst. remember (combine b_exs b_ts) as es. rename Heqes into bs_comb.
   simpl. simpl in H. rewrite forallb_compose.
   repeat (apply eta_always_something in H). clear Ht_cs H2.
   generalize dependent b_ts. generalize dependent b_exs.
   induction es; try reflexivity.
   intros. destruct a as [b_t b_ex]. simpl in *. destruct (value_b b_t) eqn:Eb_t.
   +simpl in *.
    destruct b_exs as [|b_ex0 b_exs]; try solve [inversion bs_comb].
    destruct b_ts as [|b_t0 b_ts]; try solve [inversion bs_comb]. inversion bs_comb. rewrite <- H3 in *. rewrite <- H4 in *. rewrite H5 in *.
    apply IHes with (b_ts0 := b_ts) (b_exs0 := b_exs); try (assumption + auto).
    *destruct (forallb value_b (map fst (combine b_exs b_ts))); try reflexivity.
     apply eta_always_something. repeat (apply eta_always_something in H). assumption.
    *inversion H1. assumption.
    *inversion Ht_bs. assumption.
   +simpl. simpl in H. repeat (apply eta_always_something in H).
    inversion H1; subst. rewrite Eb_t in H4. apply H4; try assumption.
    exists b_ex. destruct b_exs; try inversion bs_comb. destruct b_ts; try inversion bs_comb. inversion Ht_bs. assumption.
  (* E_Let *)
  -simpl in H. destruct_with_eqn (value_b e1).
   +inversion H.
   +simpl. apply eta_always_something in H. apply IHe1.
    *exists t1. assumption.
    *assumption.
Qed.

Proposition progress_left : forall (e : expr) (p : program) (tc : exists t, (program_skeleton p) / [] |- e : t),
    value_b e = true -> one_step_eval p e = None.
Proof.
  intros.
  induction e using expr_strong_ind; try simpl in H; try discriminate H.
   (* E_Constr *)
  -intros. inversion tc; subst. inversion H1; subst. clear tc. clear H1. clear H4. generalize dependent cargs. induction ls.
   +intros. reflexivity.
   +simpl. case_eq (value_b a).
    *intros. repeat (apply none_propagates). apply eta_always_something with (f := fun args' => E_Constr n args'). induction cargs.
     **inversion H7.
     **apply IHls with (cargs := cargs); clear IHls.
       ***inversion H0; subst. assumption.
       ***simpl in H. apply andb_true_iff in H. apply proj2 in H. assumption.
       ***inversion H7. assumption.
    *clear IHls. intros. simpl in H. apply andb_true_iff in H. apply proj1 in H. rewrite H1 in H. discriminate H.
  (* E_ComatchFunCall *)
  -inversion tc; inversion H1; subst; simpl; rewrite H; reflexivity.
  (* E_CoMatch *)
  -inversion tc. inversion H2; subst. simpl. rewrite forallb_compose in H. rewrite H. reflexivity.
Qed.

Theorem progress : forall (e : expr) (p : program) (tc : exists t, (program_skeleton p) / [] |- e : t),
    value_b e = true <-> one_step_eval p e = None.
Proof.
  intros.
  unfold iff. split.
  -apply progress_left; try assumption.
  -apply progress_right; try assumption.
Qed.
