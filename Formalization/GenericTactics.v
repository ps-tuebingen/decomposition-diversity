Require Import Coq.Lists.List.
Import ListNotations.

Ltac Forall_tail_tac := simpl in *;
    match goal with
    | [ H: Forall ?P (?x :: ?xs) |- Forall ?P ?xs ] => inversion H; assumption
    end.

Ltac IH_tac' tac :=
    match goal with
    | [ IH: _ -> ?x |- ?x ] => apply IH; try assumption; tac
    | [ IH: _ -> _ -> ?x |- ?x ] => apply IH; try assumption; tac
    | [ IH: _ -> _ -> _ -> ?x |- ?x ] => apply IH; try assumption; tac
    | [ IH: _ -> _ -> _ -> _ -> ?x |- ?x ] => apply IH; try assumption; tac
    | [ IH: _ -> _ -> _ -> _ -> _ -> ?x |- ?x ] => apply IH; try assumption; tac
    | [ IH: _ -> _ -> _ -> _ -> _ -> _ -> ?x |- ?x ] => apply IH; try assumption; tac
    | [ IH: _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?x |- ?x ] => apply IH; try assumption; tac
    | [ IH: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?x |- ?x ] => apply IH; try assumption; tac
    | [ IH: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?x |- ?x ] => apply IH; try assumption; tac
    | [ IH: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?x |- ?x ] => apply IH; try assumption; tac
    end.

Tactic Notation "IH_tac" := IH_tac' idtac.
Tactic Notation "IH_tac" tactic(tac) := IH_tac' tac.

Ltac subst_in x y H :=
    match goal with
    | [ E: x = y |- _ ] => rewrite E in H || rewrite <- E in H
    | [ E: y = x |- _ ] => rewrite <- E in H || rewrite E in H
    end.

Ltac map_tac tac ls :=
    match ls with
    | (?LS, ?X) => map_tac tac LS; tac X
    | ?X => tac X
    end.

Ltac gen_dep to_gen :=
    map_tac ltac:(fun id => generalize dependent id) to_gen.

Ltac gen_induction to_gen to_ind :=
    gen_dep to_gen; induction to_ind; intros.

Ltac IH_auto_tac :=
      match goal with
      | [ H: ?g |- ?g ] => assumption
      | [ H: forall x : ?t, ?b, H1 : ?t |- _ ] => specialize (H H1); IH_auto_tac
      | [ H: forall x : ?t, ?b, f: ?r -> ?t, x: ?r |- _ ] => specialize (H (f x)); IH_auto_tac
      end.

Ltac match_destruct_tac :=
  match goal with
  | [ H: match ?x with _ => _ end |- _ ] => let E := fresh "E_" H "_match" in
                                         destruct x eqn:E
  | [ H: context [match ?x with _ => _ end] |- _ ] => let E := fresh "E_" H "_match" in
                                                   destruct x eqn:E
  | [  |- context [match ?x with _ => _ end] ] => let E := fresh "E_match" in
                                               destruct x eqn:E
  end.


Ltac IH_adapter H aux_tac :=
  match type of H with
  | ?t =>
    let rec find_ret ty :=
        match ty with
        | ?a -> ?b => find_ret b
        | ?x =>
          match goal with
          | [  |- ?gl ] =>
            let Hf := fresh
            in assert (Hf: x -> gl);
               [> | apply Hf; apply H; aux_tac]
          end
        end
    in find_ret t
  end.

Ltac double_exists H :=
  match goal with
  | [ H': exists x, _ |- exists x, _ ] =>
    match H with
    | H' =>
      let y := fresh "term"
      in let Hf := fresh "Hyp"
         in inversion H' as [y Hf];
            clear H'; rename Hf into H';
            exists y; double_exists H'
    end
  | [  |- _ ] => idtac
  end.

Ltac context_replace x y :=
  match goal with
  | [  |- ?gl ] =>
    match gl with
    | context c [x] =>
      let bar := context c [y]
      in assert (bar -> gl)
    end
  end.

Ltac exists_context_replace Q :=
  let Hnew := fresh
  in match goal with
     | [  |- exists x, @?P x ] =>
       assert ( Hnew : (exists x, Q x) -> exists x, P x);
       [> let Hx := fresh
          in intro Hx; double_exists Hx
       | apply Hnew ]
     | [  |- exists x y, @?P x y ] =>
       assert ( Hnew : (exists x y, Q x y) -> exists x y, P x y);
       [> let Hx := fresh
          in intro Hx; double_exists Hx
       | apply Hnew ]
     | [  |- exists x y z, @?P x y z ] =>
       assert ( Hnew : (exists x y z, Q x y z) -> exists x y z, P x y z);
       [> let Hx := fresh
          in intro Hx; double_exists Hx
       | apply Hnew ]
     | [  |- exists x y z z1, @?P x y z z1 ] =>
       assert ( Hnew : (exists x y z z1, Q x y z z1) -> exists x y z z1, P x y z z1);
       [> let Hx := fresh
          in intro Hx; double_exists Hx
       | apply Hnew ]
     | [  |- exists x y z z1, @?P x y z z1 ] =>
       assert ( Hnew : (exists x y z z1 z2, Q x y z z1 z2) -> exists x y z z1 z2, P x y z z1 z2);
       [> let Hx := fresh
          in intro Hx; double_exists Hx
       | apply Hnew ]
     end.

Ltac Forall_head_tac H H_out :=
  match type of H with
  | Forall (fun x => @?P x) (?xx :: ?xs) =>
    assert (H_out: P xx); [> inversion H; auto |]
  end.

Tactic Notation "Forall_head" hyp(H) "as" ident(H_out) :=
  Forall_head_tac H H_out.
Tactic Notation "Forall_head" hyp(H) :=
  let H_out := fresh H "_head" in Forall_head_tac H H_out.

Ltac in_map_tac :=
   match goal with
   | [ |- In _ (map ?ff _) ] => apply in_map with (f := ff)
   end.

(******************************)
(** reassociate lists        **)
(******************************)

Ltac reassoc_list_to_right_hyp H :=
  repeat rewrite app_nil_l in H;
  repeat rewrite app_nil_r in H;
  repeat rewrite <- app_assoc in H.

Ltac reassoc_list_to_right_all :=
  repeat rewrite app_nil_l;
  repeat rewrite app_nil_r;
  repeat rewrite <- app_assoc in *.

Ltac reassoc_list_to_right :=
  repeat rewrite app_nil_l;
  repeat rewrite app_nil_r;
  repeat rewrite <- app_assoc.

Ltac reassoc_lists_helper xs ys E :=
assert (E : xs = ys);
  [> reassoc_list_to_right; solve [auto]
  |].

Ltac reassoc_lists_hyp xs ys H :=
  let E := fresh in
  reassoc_lists_helper xs ys E;
  rewrite E in H; clear E.

Ltac reassoc_lists_all xs ys :=
  let E := fresh in
  reassoc_lists_helper xs ys E;
  rewrite E in *; clear E.

Ltac reassoc_lists xs ys :=
  let E := fresh in
  reassoc_lists_helper xs ys E;
  rewrite E; clear E.

Tactic Notation "reassoc" constr(xs) constr(ys) "in" hyp_list(J) := reassoc_lists_hyp xs ys J.
Tactic Notation "reassoc" constr(xs) constr(ys) "in" "*" := reassoc_lists_all xs ys.
Tactic Notation "reassoc" constr(xs) constr(ys) := reassoc_lists xs ys.
Tactic Notation "reassoc_to_right" "in" hyp_list(J) := reassoc_list_to_right_hyp J.
Tactic Notation "reassoc_to_right" "in" "*" := reassoc_list_to_right_all.
Tactic Notation "reassoc_to_right" := reassoc_list_to_right.
Tactic Notation "reassoc" :=
  match goal with
  | [  |- context [?l = ?r] ] =>
    reassoc_lists l r
  end.
Tactic Notation "reassoc" "in" hyp_list(J) :=
  match goal with
  | [  |- context [?l = ?r] ] =>
    reassoc_lists_hyp l r J
  end.
Tactic Notation "reassoc" "in" "*" :=
  match goal with
  | [  |- context [?l = ?r] ] =>
    reassoc_lists_all l r
  end.


(********************************************)
(** rewrite let (_,y)... to snd (resp fst) **)
(********************************************)

Ltac unfold_to_prod_tac t H :=
  repeat match t with
         | _ * _ => fail 1
         | ?p => unfold p in H
         end.

Ltac replace_with_snd_tac H :=
  progress
    match type of H with
    | context [let (_,y) := ?x in y] =>
      change (let (_,y) := x in y) with (snd x) in H
    | context [(fun x => (let (_,y) := @?g x in y))] =>
      (let t := match type of g with
                | _ -> ?t => t
                end
       in unfold_to_prod_tac t H);
      match type of H with
      | context [?orig] =>
        match orig with
        | (fun x => (let (_,y) := @?g x in y)) =>
          match type of g with
          | _ -> (?l' * ?r') =>
            change orig with (fun x => (@snd l' r' (g x))) in H;
            simpl in H
          end
        end
      end
    | context [(fun x => ?f (let (_,y) := @?g x in y))] =>
      (let t := match type of g with
                | _ -> ?t => t
                end
       in unfold_to_prod_tac t H);
      match type of H with
      | context [?orig] =>
        match orig with
        | (fun x => ?f (let (_,y) := @?g x in y)) =>
          match type of g with
          | _ -> (?l' * ?r') =>
            change orig with (fun x => f (@snd l' r' (g x))) in H;
            simpl in H
          end
        end
      end
    end.

Tactic Notation "replace_with_snd" "in" hyp(H) := repeat replace_with_snd_tac H.
Tactic Notation "replace_with_snd" "in" "*" :=
  repeat
    match goal with
    | [ H: _ |- _ ] =>
      replace_with_snd_tac H
    end.


Ltac replace_with_fst_tac H :=
  progress
    match type of H with
    | context [let (y,_) := ?x in y] =>
      change (let (y,_) := x in y) with (fst x) in H
    | context [(fun x => (let (y,_) := @?g x in y))] =>
      (let t := match type of g with
                | _ -> ?t => t
                end
       in unfold_to_prod_tac t H);
      match type of H with
      | context [?orig] =>
        match orig with
        | (fun x => (let (y,_) := @?g x in y)) =>
          match type of g with
          | _ -> (?l' * ?r') =>
            change orig with (fun x => (@fst l' r' (g x))) in H;
            simpl in H
          end
        end
      end
    | context [(fun x => ?f (let (y,_) := @?g x in y))] =>
      (let t := match type of g with
                | _ -> ?t => t
                end
       in unfold_to_prod_tac t H);
      match type of H with
      | context [?orig] =>
        match orig with
        | (fun x => ?f (let (y,_) := @?g x in y)) =>
          match type of g with
          | _ -> (?l' * ?r') =>
            change orig with (fun x => f (@fst l' r' (g x))) in H;
            simpl in H
          end
        end
      end
    end.

Tactic Notation "replace_with_fst" "in" hyp(H) := repeat replace_with_fst_tac H.
Tactic Notation "replace_with_fst" "in" "*" :=
  repeat
    match goal with
    | [ H: _ |- _ ] =>
      replace_with_fst_tac H
    end.


(**************************************************************)
(** commutativity solver **************************************)
(**************************************************************)


Inductive is_comm {A : Type} : (list A -> Prop) -> Prop :=
| is_comm_proof: forall {P : list A -> Prop}, (forall (l m r : list A), P (l ++ m ++ r) -> P (m ++ l ++ r)) -> is_comm P.

Ltac insert_right outer inner :=
  match outer with
  | [] => inner
  | (?l ++ ?r) =>
    (let rest := insert_right r inner in
     constr:(l ++ rest))
  | ?l => constr:(l ++ inner)
  end.

Ltac reassoc_in_ltac ls :=
  match ls with
  | ?l ++ [] => (reassoc_in_ltac l)
  | [] ++ ?l => (reassoc_in_ltac l)
  | ?l ++ ?r =>
    (let l' := reassoc_in_ltac l in
     let r' := reassoc_in_ltac r in
     match r' with
     | [] => l'
     | _ => insert_right l' r'
     end)
  | ?l => l
  end.

Ltac fold_app ls fcons acc :=
  match ls with
  | ?l ++ ?r =>
    let acc' := fcons acc l in
    fold_app r fcons acc'
  | [] => acc
  | _ => fcons acc ls
  end.

Ltac rev_app_app ls rs :=
  fold_app ls
             ltac:(fun acc l => match acc with
                             | [] => l
                             | _ => match l with
                                   | [] => acc
                                   | _ => constr:(l ++ acc)
                                   end
                             end)
                    rs.

Ltac rev_app_list ls :=
  match ls with
  | ?l ++ ?r => rev_app_app r l
  | _ => ls
  end.

Ltac split_at_tac x xs :=
  match xs with
  | x ++ ?r =>
    match type of x with
    | list ?t =>
      constr:((@nil t,x,r))
    end
  | x =>
    match type of x with
    | list ?t =>
      constr:((@nil t,x,@nil t))
    end
  | ?l ++ ?r =>
    let res := split_at_tac x r in
    match res with
    | (?c,?y,?r') =>
      match c with
      | [] => constr:((l,y,r'))
      | _ => constr:((l++c,y,r'))
      end
    end
  end.

(** use commutativity of a property on lists.
 ** usage: given a property P: list a -> Prop,
 ** comm has type (is_comm P), i.e. a packaged proof of this commutativity.
 ** src and trg are the desired source and target lists, respectively.
 ** They should be equivalent up to commutativity (and associativity + empty lists)
 ** Finally, H is the name of the resulting new hypothesis, which will be of type
 ** P src -> P trg
 **)
Ltac apply_is_comm_tac H comm src trg :=
  match type of comm with
  | is_comm ?P =>
    let H_comm :=
        match comm with
        | ?f _ =>
          (match eval unfold f in comm with
           | is_comm_proof ?p => p
           end)
        | _ =>
          (match eval lazy in comm with
           | is_comm_proof ?p => p
           end)
        end in
    first
      [ match src with
        | trg => assert (H: P src -> P trg); [> intro; assumption |]
        end
      | assert (H : P src -> P trg);
        [> let src' := reassoc_in_ltac src in
           let H' := fresh in
           intro H'; cut (P src'); [> | reassoc_list_to_right_hyp H'; apply H' ];
           let trg' := reassoc_in_ltac trg in
           clear H'; intro H'; cut (P trg'); [> intro; reassoc_list_to_right; assumption |];
           (let rec go ctx rst tgt :=
                (match rst with
                 | ?l ++ ?r =>
                   let tup := split_at_tac l tgt in
                   let tgt_ctx := match tup with
                                  | (?l,_,_) => l
                                  end in
                   let tgt_rst := match tup with
                                  | (_,_,?r) => r
                                  end in
                   let tgt'' := insert_right tgt_ctx tgt_rst in
                   let tgt' := rev_app_app ctx (l ++ tgt'') in
                   cut (P tgt');
                   [ let Htmp := fresh in
                     intro Htmp;
                     let rev_ctx := rev_app_list ctx in
                     let tgt_tmp := constr:((rev_ctx ++ tgt_ctx) ++ (l ++ tgt_rst)) in
                     let tgt_full := rev_app_app ctx tgt in
                     reassoc_lists tgt_full tgt_tmp;
                     apply (H_comm l (rev_ctx ++ tgt_ctx) tgt_rst);
                     reassoc_lists (l ++ (rev_ctx ++ tgt_ctx) ++ tgt_rst)
                                   (l ++ rev_ctx ++ (tgt_ctx ++ tgt_rst));
                     apply (H_comm rev_ctx l (tgt_ctx ++ tgt_rst));
                     reassoc_list_to_right;
                     repeat rewrite app_nil_r in *; repeat rewrite app_nil_l in *;
                     assumption
                   | ];
                   repeat (rewrite app_nil_r in * );
                   repeat (rewrite app_nil_l in * );
                   let ctx' := match ctx with
                               | [] => l
                               | _ => constr:(l ++ ctx)
                               end in
                   go ctx' r tgt''
                 | _ => easy
                 (*
                   | _ => idtac "ctx" ctx;
                         idtac "rst" rst;
                         idtac "tgt" tgt;
                         repeat match goal with
                                | [ H: P _ |- _ ] => let t := type of H in idtac H t; clear H
                                end
                  *)
                 end) in
            match type of src' with
            | list ?t =>
              go (@nil t) src' trg'
            end)
        |]
      ]
  end.






