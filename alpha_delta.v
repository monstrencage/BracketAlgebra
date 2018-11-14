Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp systems.
Require Import factors aeq_facts.
Require Import alpha_regexp closed_languages binding_finite alphaKA.
Require Import filters splits strict_split tri_split alpha_derivatives.

Opaque filter_binding lower_squares splitAct TriSplitAct.

Section s.

  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.
  Ltac non_zero e :=
    let T:=fresh "T" in
    case_eq (test0 e);intro T;
    [etransitivity;[|apply zero_minimal];
     try apply KA_αKA_inf;
     apply ax_eq_inf,test0_spec;
     repeat (simpl;rewrite T||rewrite test0_act||rewrite orb_true_r);
     try reflexivity|].
  
  
  Notation Regexp := (@regexp letter).

  Definition 𝛅 (x : letter) c d (e : Regexp) :=
    match x with
    | open a => δ1 a e ∪ TriSplitAct c d 0 a 0 (δ3 d e)
    | x => δ x e
    end.

  Lemma 𝛅_αKA x c d e f :
    is_binding_finite f -> c # (⟪x⟫·e·f) -> d # (⟪x⟫·e·f) -> c<>d ->
    e =α f -> 𝛅 x c d e =α 𝛅 x c d f.
  Proof.
    intros Bf Fc Fd N1 eq.
    pose proof Bf as Be.
    apply (is_binding_finite_ax_eq eq) in Be.
    destruct x;simpl.
    - assert (c # e /\ c # f /\ d # e /\ d # f /\ a<>c /\ a <>d)
        as (Fce&Fcf&Fde&Fdf&N2&N3)
        by (repeat rewrite support_prod in Fc,Fd;simpl_In in *;simpl in *;tauto).
      apply proper_join.
      + apply δ1_αKA,eq;assumption.
      + apply TriSplitAct_αKA. 
        * apply δ3_is_binding_finite,Bf.
        * intros ->;apply N3;reflexivity.
        * intros ->;apply N1;reflexivity.
        * assumption.
        * rewrite δ3_support.
          intros [<-|Ic].
          -- apply N1;reflexivity.
          -- apply Fce,Ic.
        * rewrite δ3_support.
          intros [<-|Ic].
          -- apply N1;reflexivity.
          -- apply Fcf,Ic.
        * apply δ3_αKA;tauto.
    - apply δ_proper_αKA_not_open,eq.
      intros ?;discriminate.
    - apply δ_proper_αKA_not_open,eq.
      intros ?;discriminate.
  Qed.

  Lemma 𝛅_αKA_inf x c d e f :
    is_binding_finite f -> c # (⟪x⟫·e·f) -> d # (⟪x⟫·e·f) -> c<>d ->
    e <=α f -> 𝛅 x c d e <=α 𝛅 x c d f.
  Proof.
    intros Bf Fc Fd N1 eq.
    pose proof Bf as Be.
    apply (is_binding_finite_ax_eq eq) in Be.
    destruct x;simpl.
    - assert (c # e /\ c # f /\ d # e /\ d # f /\ a<>c /\ a <>d)
        as (Fce&Fcf&Fde&Fdf&N2&N3)
          by (repeat rewrite support_prod in Fc,Fd;simpl_In in *;simpl in *;tauto).
      apply proper_join_inf.
      + apply δ1_αKA_inf,eq;assumption.
      + apply TriSplitAct_αKA_inf. 
        * apply δ3_is_binding_finite,Bf.
        * intros ->;apply N3;reflexivity.
        * intros ->;apply N1;reflexivity.
        * assumption.
        * rewrite δ3_support.
          intros [<-|Ic].
          -- apply N1;reflexivity.
          -- apply Fce,Ic.
        * rewrite δ3_support.
          intros [<-|Ic].
          -- apply N1;reflexivity.
          -- apply Fcf,Ic.
        * apply δ3_αKA_inf;tauto.
    - apply δ_proper_αKA_not_open_inf,eq.
      intros ?;discriminate.
    - apply δ_proper_αKA_not_open_inf,eq.
      intros ?;discriminate.
  Qed.
 
  Lemma 𝛅_inf x c d e :
    is_binding_finite e -> c # (⟪x⟫·e) -> d # (⟪x⟫·e) -> c<>d ->
    ⟪x⟫ · 𝛅 x c d e <=α e.
  Proof.
    intros Be Fc Fd N.
    destruct x;simpl.
    - assert (c # e /\ d # e /\ a<>c /\ a <>d)
        as (Fce&Fde&N2&N3)
          by (repeat rewrite support_prod in Fc,Fd;simpl_In in *;simpl in *;tauto).
      rewrite semiring_left_distr.
      apply inf_join_inf.
      + apply KA_αKA_inf.
        etransitivity.
        * apply proper_prod_inf;[reflexivity|].
          apply δ1_δ,Be.
        * apply δ_inf_e.
      + etransitivity;[apply proper_prod_inf;
                       [reflexivity|apply ax_eq_inf,KA_αKA,TriSplitAct_TriSplit_list]|].
        * apply δ3_is_binding_finite,Be.
        * intros ->;apply N3;reflexivity.
        * intros ->;apply N;reflexivity.
        * intros ->;apply N2;reflexivity.
        * rewrite Σ_distr_l,map_map.
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as (((f1,f2),f3)&<-&If).
          simpl.
          replace (cons (d,a)) with (app[(d,a)]) by reflexivity.
          rewrite <- action_compose.
          apply TriSplit_list_facts in If as (Bf1&Bf2&Bf3&hLang&Ea&Eb&Sup);
            [|apply δ3_is_binding_finite,Be].
          rewrite <- (δ3_open Be Fde).
          etransitivity;[|apply proper_prod_inf;
                          [reflexivity|apply KA_αKA_inf,CompletenessKA_inf,hLang]].
          repeat rewrite (mon_assoc _ _ _).
          apply proper_prod_inf;[|reflexivity].
          replace ⟪open a⟫ with ([(d,a)]∙⟪open d⟫)
            by (repeat (unfold act;simpl);simpl_eqX;reflexivity).
          rewrite <- act_prod.
          etransitivity.
          -- apply proper_prod_inf;[|reflexivity].
             apply ax_eq_inf;symmetry.
             apply ax_eq_ax,αKA_αα.
             intros ? (?&u&->&->&Iu).
             split.
             ++ apply act_lang in Iu.
                apply Ea in Iu as (Eu&_).
                unfold fresh__α;simpl_binding.
                revert Eu;rewrite 𝗙_perm;unfold act;simpl;simpl_eqX.
                intros ->.
                reflexivity.
             ++ apply αfresh_support.
                simpl.
                rewrite (support_list_cons (open d) u).
                intros [<-|Ia];[apply N3;reflexivity|].
                simpl in Ia.
                apply support_lang in Iu;rewrite Iu,support_action,In_act_lists in Ia.
                revert Ia;unfold act;simpl;simpl_eqX.
                rewrite δ3_support in Sup;intros Ic.
                cut (c ∈ (d::⌊e⌋)).
                ** intros [<-|Ic'];[apply N;reflexivity|apply Fce,Ic'].
                ** apply Sup;repeat rewrite support_prod;simpl_In;tauto.
          -- repeat rewrite <- (mon_assoc _ _ _).
             apply proper_prod_inf;[reflexivity|].
             rewrite <- act_prod.
             apply ax_eq_inf;symmetry;apply ax_eq_ax,αKA_αα.
             intros ? Iu.
             split.
             ++ apply Eb,Iu. 
             ++ apply αfresh_support;intros Ic.
                apply support_lang in Iu;rewrite Iu in Ic.
                rewrite δ3_support in Sup.
                cut (c ∈ (d::⌊e⌋)).
                ** intros [<-|Ic'];[apply N;reflexivity|apply Fce,Ic'].
                ** apply Sup;rewrite support_prod;simpl_In;tauto.
    - apply KA_αKA_inf,δ_inf_e.
    - apply KA_αKA_inf,δ_inf_e.
  Qed.

  Opaque TriSplitAct δ3 δ1.
    Transparent splitActStrict.
  Lemma splitActStrict_fresh_test0 a b N e :
    b # e -> test0 (splitActStrict a b N e) = true.
  Proof.
    revert N;induction e;intros N;simpl;try reflexivity.
    - replace e_add with join by reflexivity.
      rewrite support_join.
      simpl_In;intros;rewrite IHe1,IHe2 by tauto;reflexivity.
    - destruct (_||_);[reflexivity|].
      replace e_prod with prod by reflexivity.
      rewrite support_prod;simpl_In.
      simpl;intros.
      rewrite IHe1 by tauto;simpl.
      rewrite test0_Σ,forallb_forall;intros g Ig.
      apply in_map_iff in Ig as ((?&?)&<-&_).
      simpl;rewrite IHe2 by tauto.
      apply orb_true_r.
    - rewrite orb_false_r;apply IHe.
    - intro Fb.
      assert (E: b # [x])
        by (intro Ib;apply Fb;apply support_list_cons in Ib;rewrite app_nil_r in Ib;apply Ib).
      apply αfresh_support in E;unfold fresh__α in E;simpl_binding in E;rewrite E.
      replace (_=?=_) with false by(symmetry;apply eqX_false;discriminate).
      reflexivity.
  Qed.
  Opaque splitActStrict.
  Transparent TriSplitAct.
  Lemma TriSplitAct_fresh_test0 a b c N M e :
    b # e -> test0 (TriSplitAct a b N c M e) = true.
  Proof.
    revert N M;induction e;intros N M;simpl;try reflexivity.
    - replace e_add with join by reflexivity.
      rewrite support_join.
      simpl_In;intros;rewrite IHe1,IHe2 by tauto;reflexivity.
    - destruct (_||_);[reflexivity|].
      replace e_prod with prod by reflexivity.
      rewrite support_prod;simpl_In.
      simpl;intros.
      rewrite IHe1 by tauto;simpl.
      apply andb_true_iff;split;rewrite test0_Σ,forallb_forall;intros g Ig;
        apply in_map_iff in Ig as ((?&?)&<-&_).
      + simpl;apply orb_true_iff;left.
        rewrite test0_act;apply splitActStrict_fresh_test0.
        intros Ib;apply H;left.
        apply filter_binding_support in Ib;tauto.
      + destruct p as (α,n),p0 as (β,m);simpl.
        rewrite IHe2 by tauto.
        apply orb_true_r.
    - repeat rewrite orb_false_r.
      intros F;rewrite IHe by tauto;simpl.
      simpl;apply orb_true_iff;left.
      rewrite test0_act.
      apply LowerExpr_test0.
      apply splitActStrict_fresh_test0,F.
    - intro Fb.
      assert (E: b # [x])
        by (intro Ib;apply Fb;apply support_list_cons in Ib;rewrite app_nil_r in Ib;apply Ib).
      apply αfresh_support in E;unfold fresh__α in E;simpl_binding in E;rewrite E.
      replace (_=?=_) with false by(symmetry;apply eqX_false;discriminate);simpl.
      reflexivity.
  Qed.
  Opaque TriSplitAct.
  
  Lemma 𝛅_open_lang a c d e :
    is_binding_finite e -> c # e -> d # e -> c<>d -> a<>c -> a<>d ->
    ⟦𝛅 (open a) c d e⟧ ≃ ⟦δ1 a e⟧ ∪ (fun u => exists b u1 u2 u3, u = [(a,c);(b,c)]∙u1++close a::[(a,c)]∙u2++u3
                                                         /\ ⟦e⟧(open b::u1++close b::u2++u3)
                                                         /\ b ⋄ u1
                                                         /\ a #α (open b::u1++close b::u2)).
  Proof.
    intros Be Nc Nd N1 N2 N3.
    simpl;apply proper_join;[reflexivity|].
    intros u;split;intros Iu.
    - apply TriSplitAct_lang in Iu;try intros -> || apply δ3_is_binding_finite;try tauto.
      destruct Iu as (u1&u2&u3&->&Iu&Eu1&Eu2&Min__u).
      apply δ3_lang in Iu;[| assumption].
      destruct Iu as (v1&v2&b&EE&Ev1&Iu&Min__v).
      pose proof (support_lang Iu) as Sup.
      assert (N4: b<>d) by (intros ->;apply Nd,Sup,support_list_cons;left;reflexivity).
      assert (N5: b<>c) by (intros ->;apply Nc,Sup,support_list_cons;left;reflexivity).
      rewrite support_list_cons,support_list_app in Sup.
      levi EE;clear EE;subst.
      + clear Min__u;destruct (@αfresh_open_split _ _ _ _ v1 b) as (w1&w2&->&Bal);
          [unfold close_balanced;rewrite Ev1;discriminate|].
        destruct w2;[|exfalso;apply (Min__v (w1++[close b])(l::w2));
                      [rewrite app_ass;reflexivity|solve_length
                       |simpl_binding;revert Bal;unfold balanced;destruct (𝗙 b w1) as ((?&ff)&?);
                        unfold d_binding;simpl;intros (->&->);reflexivity]].
        exists b,w1,u2,u3;repeat rewrite app_ass in *.
        repeat assumption||split.
        * repeat rewrite act_lists_app||rewrite act_lists_cons||rewrite app_ass;simpl.
          f_equal;[|f_equal].
          -- repeat rewrite action_compose;apply support_eq_action_eq.
             intros k Ik.
             unfold act;simpl;simpl_eqX.
             destruct_eqX k b;subst.
             ++ simpl_eqX;reflexivity.
             ++ destruct_eqX k d;subst.
                ** exfalso;apply Nd,Sup;rewrite support_list_app.
                   repeat simpl_In;tauto.
                ** destruct_eqX k c.
                   --- exfalso;apply Nc,Sup;rewrite support_list_app.
                       repeat simpl_In;tauto.
                   --- destruct_eqX k a;simpl_eqX;reflexivity.
          -- repeat (unfold act;simpl);simpl_eqX.
             reflexivity.
        * unfold fresh__α;revert Eu2.
          simpl_binding.
          rewrite 𝗙_perm.
          unfold act;simpl.
          destruct_eqX a b;simpl_eqX.
          -- simpl_binding;simpl.
             rewrite prod_unit_r.
             assert (Fd: d # w1)
               by(intro;apply Nd,Sup;rewrite support_list_app;repeat simpl_In;tauto).
             apply αfresh_support in Fd as ->.
             rewrite prod_unit_l;intros ->.
             rewrite prod_unit_r.
             revert Bal;unfold balanced;destruct (𝗙 b w1) as ((?&ff)&?).
             unfold d_binding;simpl;intros (->&->);reflexivity.
          -- simpl_binding;simpl.
             rewrite prod_unit_r.
             repeat rewrite prod_unit_l.
             tauto.
      + exfalso;apply (Min__u ([(b,d)]∙v1) (a0::w)).
        * reflexivity.
        * solve_length.
        * rewrite 𝗙_perm.
          unfold act at 1;simpl;unfold_eqX;apply Ev1.
      + apply (act_bij ([(b,d)]∗)) in E;rewrite act_pinv_p in E;subst.
        repeat rewrite act_lists_app in Min__v||rewrite app_ass in Min__v.
        exfalso.
        apply (Min__v ([(b,d)]∗∙u1)(([(b, d)] ∗) ∙ (a0 :: w))).
        * reflexivity.
        * solve_length.
        * rewrite 𝗙_perm.
          unfold act at 1;simpl;unfold_eqX;apply Eu1.
    - destruct Iu as (b&u1&u2&u3&->&Iu&Eb&Ea).
      apply TriSplitAct_lang;try intros -> || apply δ3_is_binding_finite;try tauto.
      assert (N4: b<>d)
        by (intros ->;apply Nd;apply support_lang in Iu;apply Iu,support_list_cons;left;reflexivity).
      assert (N5: b<>c)
        by (intros ->;apply Nc;apply support_lang in Iu;apply Iu,support_list_cons;left;reflexivity).
      exists ([(b,d)]∙(u1++[close b])),u2,u3.
      repeat split.
      + repeat rewrite act_lists_app||rewrite action_compose||rewrite app_ass;simpl.
        f_equal;[|f_equal].
        * apply support_eq_action_eq.
          intros k Ik.
          assert (N6: k<>d)
            by (intros ->;apply Nd;apply support_lang in Iu;apply Iu,support_list_cons;
                rewrite support_list_app;simpl_In;tauto).
          assert (N7: k<>c)
            by (intros ->;apply Nc;apply support_lang in Iu;apply Iu,support_list_cons;
                rewrite support_list_app;simpl_In;tauto).
          unfold act;simpl.
          simpl_eqX.
          destruct_eqX k b.
          -- simpl_eqX;reflexivity.
          -- destruct_eqX k a;simpl_eqX;reflexivity.
        * repeat (unfold act;simpl).
          simpl_eqX;reflexivity.
      + apply δ3_lang;[assumption|].
        exists (u1++[close b]),(u2++u3),b.
        repeat split.
        * simpl_binding.
          apply destr_bind_prod_full;split;[reflexivity|].
          left; destruct Eb as (->&->);split;unfold d_binding;simpl;lia.
        * repeat rewrite app_ass in *;simpl;assumption.
        * intros w1 w2 E Len.
          levi E;subst;clear E.
          -- destruct Eb as (_&Eb).
             intros E;rewrite E in Eb;discriminate.
          -- destruct Eb as (_&Eb);simpl_binding in Eb.
             intros E;rewrite E in Eb;unfold d_binding in Eb;simpl in Eb;lia.
          -- inversion E1 as [[EE E1']];subst.
             symmetry in E1';apply app_eq_nil in E1' as (?&?);subst.
             solve_length.
      + rewrite 𝗙_perm;unfold act;simpl;simpl_eqX.
        simpl_binding.
        revert Eb;unfold balanced;destruct (𝗙 b u1) as ((?&ff)&?);unfold d_binding;simpl.
        intros (->&->);reflexivity.
      + rewrite 𝗙_app,𝗙_perm.
        unfold act;simpl;simpl_eqX.
        assert (Fd: d # u1)
          by (intro;apply Nd;apply support_lang in Iu;apply Iu,support_list_cons;
              rewrite support_list_app;simpl_In;tauto).
        unfold_eqX;subst.
        * simpl_binding.
          rewrite prod_unit_r.
          apply αfresh_support in Fd as ->.
          rewrite prod_unit_l.
          revert Ea;unfold fresh__α.
          simpl_binding.
          repeat rewrite prod_assoc.
          revert Eb;unfold balanced;destruct (𝗙 b u1) as ((?&ff)&?);unfold d_binding;simpl.
          intros (->&->).
          rewrite prod_unit_l;tauto.
        * revert Ea;unfold fresh__α.
          simpl_binding.
          repeat rewrite prod_assoc.
          repeat rewrite prod_unit_r||rewrite prod_unit_l.
          tauto.
      + intros w1 w2 EE Len Ew1.
        rewrite act_lists_app in EE.
        revert EE;(unfold act at 2;simpl);(unfold act at 2;simpl);(unfold act at 2;simpl);simpl_eqX.
        intros EE;levi EE;subst;clear EE.
        * revert Eb Ew1;rewrite 𝗙_perm.
          unfold act,balanced,d_binding;simpl;simpl_eqX.
          destruct (𝗙 b u1) as ((?&?)&?);simpl;intros (->&->);discriminate.
        * rewrite <-(act_bij ([(b,d)]∗)),act_pinv_p in E;subst.
          revert Eb;unfold balanced;rewrite 𝗙_perm.
          unfold act;simpl;simpl_eqX;simpl_binding.
          rewrite Ew1;simpl;lia.
        * inversion E0 as [[e1 e2]].
          symmetry in e2;apply app_eq_nil in e2 as (e2&e3);subst.
          rewrite act_lists_app in Len;solve_length.
  Qed.
  
  Corollary 𝛅_support_lang x c d e u :
    is_binding_finite e -> c # ⟪x⟫·e -> d # ⟪x⟫·e -> c<>d ->
    ⟦𝛅 x c d e⟧ u -> d # u.
  Proof.
    intros Be Nc Nd N1 Iu.
    rewrite support_prod in Nc,Nd;simpl_In in *.
    destruct x as [a|a|x].
    - apply 𝛅_open_lang in Iu;try assumption.
      + destruct Iu as [Iu|(b&u1&u2&u3&->&Iu&_)].
        * apply support_lang in Iu as ->.
          rewrite support_δ1;tauto.
        * apply support_lang in Iu.
          revert Iu.
          repeat rewrite support_list_app||rewrite support_list_cons.
          intros I;rewrite <- I in Nc,Nd;clear I.
          simpl_In in *;repeat rewrite support_action,In_act_lists.
          simpl in *;unfold act;simpl.
          simpl_eqX.
          destruct_eqX d a;[tauto|].
          destruct_eqX d b;[tauto|].
          simpl_eqX;tauto.
      + tauto.
      + tauto.
      + simpl in Nc;tauto.
      + simpl in Nd;tauto.
    - apply support_lang in Iu as ->.
      simpl;rewrite δ_support;tauto.
    - apply support_lang in Iu as ->.
      simpl;rewrite δ_support;tauto.
  Qed.

  Lemma 𝛅_bnd x c d e : is_binding_finite e -> c # (⟪x⟫·e) -> d # (⟪x⟫·e) -> c<>d -> e <=α 𝛅 x c d (⟪x⟫ · e).
  Proof.
    intros Be Fc Fd N.
    destruct x.
    - assert (Be' : is_binding_finite (⟪ open a ⟫ · e))
          by(apply binding_finite_spec;simpl;apply orb_true_iff;right;apply binding_finite_spec,Be).
      destruct_eqX a c;[subst;exfalso;apply Fc;rewrite support_prod;simpl_In;simpl;tauto|].
      destruct_eqX a d;[subst;exfalso;apply Fd;rewrite support_prod;simpl_In;simpl;tauto|].
      apply KA_αKA_inf,CompletenessKA_inf.
      rewrite 𝛅_open_lang by tauto.
      intros u Iu.
      destruct_eqX (d_binding (𝗙 a u)) 0.
      + left.
        apply δ1_lang.
        * assumption.
        * split.
          -- exists [open a],u;simpl;tauto.
          -- apply E.
      + right;exists a.
        apply αfresh_open_split in N2 as (u1&u2&->&Bal).
        exists u1,[],u2;repeat assumption||split.
        * rewrite <- (act_p_pinv ([(a,c)]) u1),action_compose at 1.
          simpl;reflexivity.
        * exists [open a],(u1++close a::u2);repeat reflexivity||assumption||split.
        * unfold fresh__α;simpl_binding.
          revert Bal;unfold balanced,d_binding;destruct (𝗙 a u1) as ((?&?)&?);simpl.
          intros (->&->);reflexivity.
    - simpl;replace (eq_letter (close a) (close a)) with (close a =?= close a) by reflexivity.
      simpl_eqX.
      replace e_un with un by reflexivity.
      rewrite left_unit;reflexivity.
    - simpl;replace (eq_letter (var x) (var x)) with (var x =?= var x) by reflexivity.
      simpl_eqX.
      replace e_un with un by reflexivity.
      rewrite left_unit;reflexivity.
  Qed.


  Theorem 𝛅_residual c d x e f :
    is_binding_finite e -> is_binding_finite f ->
    c # (⟪x⟫·e·f) -> d # (⟪x⟫·e·f) -> c<>d ->
    ⟪x⟫·e<=αf <-> e <=α 𝛅 x c d f.
  Proof.
    intros Be Bf Fc Fd N.
    split.
    - intros E.
      assert (h : c#(⟪x⟫·e)) by (rewrite support_prod in Fc;simpl_In in *;tauto).
      assert (h' : d#(⟪x⟫·e)) by (rewrite support_prod in Fd;simpl_In in *;tauto).
      rewrite (𝛅_bnd Be h h' N);clear h h'.
      apply 𝛅_αKA_inf,E.
      + assumption.
      + repeat rewrite support_prod in *;simpl_In in *;tauto.
      + repeat rewrite support_prod in *;simpl_In in *;tauto.
      + assumption.
    - intros ->.
      apply 𝛅_inf.
      + assumption.
      + repeat rewrite support_prod in Fc;repeat rewrite support_prod.
        simpl_In in *;tauto.
      + repeat rewrite support_prod in Fd;repeat rewrite support_prod.
        simpl_In in *;tauto.
      + assumption.
  Qed.

  Lemma 𝛅_support c d x e : ⌊𝛅 x c d e⌋ ⊆ c::d::⌊x⌋++⌊e⌋.
  Proof.
    destruct x;simpl.
    - rewrite support_join;apply incl_app.
      + rewrite support_δ1;intro;simpl;tauto.
      + rewrite TriSplitAct_support,δ3_support.
        intro;simpl;tauto.
    - rewrite δ_support;intro;simpl;tauto.
    - rewrite δ_support;intro;simpl;simpl_In;tauto.
  Qed.

  Lemma 𝛅_is_binding_finite c d x e :
    is_binding_finite e -> c # (⟪x⟫·e) -> d # (⟪x⟫·e) -> c<>d ->
    is_binding_finite (𝛅 x c d e).
  Proof.
    intros Be Fc Fd N.
    destruct x;simpl;[|apply δ_binFin,Be|apply δ_binFin,Be].
    apply binding_finite_spec;simpl;apply andb_true_iff;split;apply binding_finite_spec.
    - apply is_binding_finite_δ1,Be.
    - apply TriSplitAct_is_binding_finite,δ3_is_binding_finite,Be.
  Qed.

  Lemma 𝛅_test0 c d x e : test0 e = true -> test0 (𝛅 x c d e) = true.
  Proof.
    intro T.
    destruct x;simpl.
    - rewrite test0_δ1 by assumption.
      simpl.
      apply TriSplitAct_test0.
      apply test0_spec,δ3_test0,T.
    - apply test0_δ,T.
    - apply test0_δ,T.
  Qed.

  
  Lemma 𝛅_switch_aux c1 c2 d1 d2 x e :
    is_binding_finite e -> c1 # (⟪x⟫·e) -> c2 # (⟪x⟫·e) -> d1 # (⟪x⟫·e) ->
    d2 # (⟪x⟫·e) -> NoDup [c1;c2;d1;d2] ->
    𝛅 x c1 d1 e <=α 𝛅 x c2 d2 e.
  Proof.
    intros Be Fc1 Fc2 Fd1 Fd2 N.
    apply NoDup_cons_iff in N as (h1&N).
    apply NoDup_cons_iff in N as (h2&N).
    apply NoDup_cons_iff in N as (h3&_).
    assert (c1<>c2 /\ c1<>d1 /\ c1<>d2 /\ c2 <> d1 /\ c2 <> d2 /\ d1 <> d2)
      as (N1&N2&N3&N4&N5&N6)
      by (simpl in *;repeat split;intros ->;tauto);clear h1 h2 h3.
    apply 𝛅_residual.
    - apply 𝛅_is_binding_finite;try tauto.
    - assumption.
    - repeat rewrite support_prod in *.
      rewrite 𝛅_support.
      unfold support at 1;simpl.
      unfold support at 1 in Fc2;simpl in Fc2.
      revert Fc2;simpl_In.
      assert (N7 : d1<>c2) by (intros ->;tauto).
      tauto.
    - repeat rewrite support_prod in *.
      rewrite 𝛅_support.
      unfold support at 1;simpl.
      unfold support at 1 in Fd2;simpl in Fd2.
      revert Fd2;simpl_In.
      tauto.
    - assumption.
    - apply 𝛅_inf;tauto.
  Qed.

  Lemma 𝛅_switch c1 c2 d1 d2 x e :
    is_binding_finite e -> c1 # (⟪x⟫·e) -> c2 # (⟪x⟫·e) -> d1 # (⟪x⟫·e) -> d2 # (⟪x⟫·e) ->
    c1 <> d1 -> c2 <> d2 ->
    𝛅 x c1 d1 e =α 𝛅 x c2 d2 e.
  Proof.
    destruct (exists_fresh (c1::c2::d1::d2::⌊⟪x⟫·e⌋)) as (c3&Fc3).
    destruct (exists_fresh (c3::c1::c2::d1::d2::⌊⟪x⟫·e⌋)) as (d3&Fd3).
    intros Be Fc1 Fc2 Fd1 Fd2 N1 N2.
    rewrite support_prod in Fc3,Fd3,Fc1,Fc2,Fd1,Fd2;simpl in *;simpl_In in *.
    apply ax_inf_PartialOrder;unfold Basics.flip;split;
      transitivity (𝛅 x c3 d3 e);apply 𝛅_switch_aux;
        try rewrite support_prod;simpl_In;try tauto.
    - repeat rewrite NoDup_cons_iff;simpl.
      repeat split;try tauto.
      + intros [->|[->|[->|FF]]];tauto.
      + intros [->|[->|FF]];tauto.
      + intros [->|FF];tauto.
      + apply NoDup_nil.
    - repeat rewrite NoDup_cons_iff;simpl.
      repeat split;try tauto.
      + intros [->|[->|[->|FF]]];tauto.
      + intros [->|[->|FF]];tauto.
      + apply NoDup_nil.
    - repeat rewrite NoDup_cons_iff;simpl.
      repeat split;try tauto.
      + intros [->|[->|[->|FF]]];tauto.
      + intros [->|[->|FF]];tauto.
      + intros [->|FF];tauto.
      + apply NoDup_nil.
    - repeat rewrite NoDup_cons_iff;simpl.
      repeat split;try tauto.
      + intros [->|[->|[->|FF]]];tauto.
      + intros [->|[->|FF]];tauto.
      + apply NoDup_nil.
  Qed.
    

  Lemma δ_inf_𝛅 x c d e :
    is_binding_finite e -> c # (⟪x⟫·e) -> d # (⟪x⟫·e) -> c<>d ->
    δ x e <=α 𝛅 x c d e.
  Proof.
    intros Be Fc Fd N.
    apply 𝛅_residual,KA_αKA_inf,δ_inf_e;try tauto.
    - apply δ_binFin,Be.
    - rewrite support_prod in Fc; repeat rewrite support_prod.
      rewrite δ_support.
      simpl_In in *;try tauto.
    - rewrite support_prod in Fd; repeat rewrite support_prod.
      rewrite δ_support.
      simpl_In in *;try tauto.
  Qed.
  

End s.

    