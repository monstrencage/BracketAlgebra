Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp systems.
Require Import aeq_facts alpha_regexp closed_languages binding_finite alphaKA factors.


Section s.

  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.

  Notation Regexp := (@regexp letter).

  Fixpoint filter_binding a β e :=
    match e with
    | e_zero => zero
    | e_un => if β =?= ε then un else zero
    | ⟪x⟫ => if 𝗳 a x =?= β then ⟪x⟫ else zero
    | e_add e f => filter_binding a β e ∪ filter_binding a β f
    | e_prod e f => Σ (map (fun p => filter_binding a (fst p) e · filter_binding a (snd p) f)
                          (factors β (sizeExpr e)))
    | e_star e =>
      if is_square β
      then
        if β =?= ε
        then (filter_binding a ε e)⋆
        else ((Σ (map (fun α => filter_binding a α e) (lower_squares β)))⋆)
               · (filter_binding a β e)
               · (Σ (map (fun α => filter_binding a α e) (lower_squares β)))⋆
      else zero
    end.

  Lemma filter_binding_test0 e :
   test0 e = true -> forall a β, test0 (filter_binding a β e) = true.
  Proof.
    intros h1 a β;revert β h1;induction e;intro β;try reflexivity||discriminate.
    - simpl;repeat rewrite andb_true_iff.
      intros (I1&I2);rewrite IHe1,IHe2 by assumption;split;reflexivity.
    - simpl;rewrite orb_true_iff;intros [I|I].
      + induction (factors β (sizeExpr e1));simpl;[reflexivity|].
        rewrite IHl,IHe1 by assumption;reflexivity.
      + induction (factors β (sizeExpr e1));simpl;[reflexivity|].
        rewrite IHl,IHe2,orb_true_r by assumption;reflexivity.
  Qed.

  Lemma filter_binding_ϵ a β e :
    ϵ e = zero -> ϵ (filter_binding a β e) = zero.
  Proof.
    revert β;induction e;simpl;try discriminate||tauto.
    - revert IHe1 IHe2;destruct (ϵ_zero_or_un e1) as [-> | ->].
      + discriminate.
      + destruct (ϵ_zero_or_un e2) as [-> | ->].
        * discriminate.
        * intros I1 I2 β _.
          rewrite I1,I2 by reflexivity.
          reflexivity.
    - revert IHe1 IHe2;destruct (ϵ_zero_or_un e1) as [-> | ->].
      + destruct (ϵ_zero_or_un e2) as [-> | ->].
        * discriminate.
        * intros _ I2 β _.
          induction (factors _ _) as [|(b1,b2) L];simpl;[reflexivity|].
          rewrite IHL,I2 by reflexivity.
          destruct (ϵ_zero_or_un (filter_binding a b1 e1)) as [-> | ->];simpl;reflexivity.
      + intros I1 _ β _.
          induction (factors _ _) as [|(b1,b2) L];simpl;[reflexivity|].
          rewrite IHL,I1 by reflexivity;simpl;reflexivity.
    - intros;unfold_eqX;reflexivity.
  Qed.
     

  Lemma filter_binding_Σ a β L : filter_binding a β (Σ L) = Σ (map (filter_binding a β) L).
  Proof. induction L;simpl;congruence. Qed.

  Lemma binding_finite_bound_size a u e :
    is_binding_finite e -> ⟦e⟧ u -> size (𝗙 a u) <= sizeExpr e.
  Proof.
    intros Be Iu.
    rewrite <- bounded_weightExpr.
    rewrite <- bindFind_weight_weightExpr by eassumption.
    clear;unfold weight.
    case_in a ⌊u⌋.
    - transitivity (sum (fun a0 : atom => size (𝗙 a0 u)) [a]).
      + simpl;simpl_nat;reflexivity.
      + apply sum_incl_ND.
        * intro;simpl;simpl_In;firstorder (now subst).
        * apply NoDup_cons,NoDup_nil;simpl;tauto.
    - rewrite (αfresh_support I).
      unfold size at 1;simpl;lia.
  Qed.
  
  Lemma filter_binding_lang a β e :
    is_binding_finite e -> 
    forall u, ⟦filter_binding a β e⟧ u <-> ⟦e⟧ u /\ 𝗙 a u = β.
  Proof.
    intro B;revert β;induction_bin_fin e B;intros β u;simpl.
    - replace (zero u) with False by reflexivity;tauto.
    - unfold_eqX;split.
      + intros ->;split;reflexivity.
      + intros (->&_);reflexivity.
      + intro F;exfalso;apply F.
      + intros (->&<-);apply N;reflexivity.
    - unfold_eqX;split.
      + intros ->;split;[reflexivity|].
        simpl_binding;assumption.
      + intros (->&_);reflexivity.
      + intro F;exfalso;apply F.
      + intros (->&<-);apply N;simpl_binding;reflexivity.
    - unfold join,joinLang.
      rewrite IHe1,IHe2.
      tauto.
    - rewrite Σ_lang;setoid_rewrite in_map_iff;split.
      + intros (?&((b1&b2)&<-&Ix)&(u1&u2&->&Iu1&Iu2));simpl in *.
        rewrite IHe1 in Iu1.
        rewrite IHe2 in Iu2.
        split.
        * exists u1,u2;tauto.
        * simpl_binding;eapply factors_prod.
          destruct Iu1 as (_&->);destruct Iu2 as (_&->);eassumption.
      + intros ((u1&u2&->&Iu1&Iu2)&E).
        revert E;simpl_binding;intro E.
        exists (filter_binding a (𝗙 a u1) e1 · filter_binding a (𝗙 a u2) e2);split.
        * exists (𝗙 a u1 , 𝗙 a u2);split;[reflexivity|].
          apply factors_In;[|assumption].
          apply binding_finite_bound_size;assumption.
        * exists u1,u2;split;[reflexivity|split;[apply IHe1|apply IHe2];tauto].
    - rewrite Σ_lang;setoid_rewrite in_map_iff.
      apply orb_true_iff in T as [T|T];pose proof (filter_binding_test0 T) as T';
        apply test0_spec,soundness in T;(split;[|intros ((u1&u2&->&I1&I2)&_)]).
      + intros (?&((b1&b2)&<-&Ix)&(u1&u2&->&I1&I2)).
        exfalso;cut (⟦zero⟧ u1);[intro h;apply h|].
        eapply soundness;[|apply I1].
        symmetry;apply test0_spec,T'.
      + exfalso;apply (T u1),I1.
      + intros (?&((b1&b2)&<-&Ix)&(u1&u2&->&I1&I2)).
        exfalso;cut (⟦zero⟧ u2);[intro h;apply h|].
        eapply soundness;[|apply I2].
        symmetry;apply test0_spec,T'.
      + exfalso;apply (T u2),I2.
    - case_eq (is_square β);intro hβ;[unfold_eqX;subst|];split.
      + intros (n&In);cut (iter_lang n ⟦e⟧ u /\ 𝗙 a u = ε);[intros h;split;[exists n|];tauto|].
        pose proof (IHe ε) as IH.
        revert IH u In;clear;intros IH;induction n.
        * intros u ->;split;reflexivity.
        * intros ? (u&w&->&Iu&Iw);simpl_binding.
          apply IHn in Iw as (Iw&->).
          apply IH in Iu as (Iu &->).
          split;[|reflexivity].
          exists u,w;split;[reflexivity|split;assumption].
      + intros ((n&In)&E);exists n.
        pose proof (IHe ε) as IH.
        revert Sq IH u E In;clear;intros Sq IH;induction n.
        * intros u E ->;split;reflexivity.
        * intros ? E (u&w&->&Iu&Iw);simpl_binding.
          exists u,w;split;[reflexivity|].
          cut (𝗙 a u = ε /\ 𝗙 a w = ε);[intro;split;[apply IH|apply IHn];tauto|].
          cut (square (𝗙 a u) /\ square (𝗙 a w));[|split].
          -- revert E;clear;simpl_binding.
             destruct (𝗙 a u) as ((?&?)&?),(𝗙 a w) as ((?,?),?);
               unfold prod_binding,square,d_binding;simpl.
             intros E (s1&s2);revert E;subst.
             destruct_ltb n n1;[destruct_ltb n1 n;[replace n with n1 in * by lia|]|];simpl;simpl_nat.
             ++ destruct b;intro E;inversion E;subst;tauto.
             ++ intro E;inversion E;subst;lia.
             ++ intro E;inversion E;subst;lia.
          -- destruct Sq as (h1&h2);eapply h2,is_binding_finite_bindings,Iu;
               assumption.
          -- apply sqExpr_star in Sq as (h1&h2);
               eapply h2,is_binding_finite_bindings;
               [assumption|exists n;apply Iw].
      + intros (?&u3&->&(u1&u2&->&I1&I2)&I3).
        apply IHe in I2 as (I2&E2).
        cut (forall w, ⟦ Σ (map (fun α => filter_binding a α e) (lower_squares β)) ⋆ ⟧ w ->
                  ⟦ e ⟧ ⋆ w /\ 𝗙 a w ⋅ β = β).
        * intros hyp;apply hyp in I1 as (I1&E1);apply hyp in I3 as (I3&E3).
          split.
          -- destruct I1 as (n1&I1).
             destruct I3 as (n3&I3).
             exists (n1+S n3);revert I1 I2 I3;clear.
             intros I1 I2 I3;revert u1 I1;induction n1.
             ++ intros u1 -> ;exists u2,u3;split;[reflexivity|tauto].
             ++ intros ? (w&u1&->&I&I1);simpl.
                exists w,((u1++u2)++u3);simpl;split;[repeat rewrite app_ass;reflexivity|firstorder].
          -- simpl_binding.
             rewrite E2,E1.
             apply sqExpr_star in Sq as (Bf&hE).
             eapply (is_binding_finite_bindings Bf),hE in I3.
             rewrite <-prod_binding_maxBind by (eassumption||(apply eqX_correct,hβ)).
             rewrite maxBind_comm.
             rewrite prod_binding_maxBind by (eassumption||(apply eqX_correct,hβ)).
             apply E3.
        * clear I1 I2 I3 E2 u1 u2 u3.
          intros w (n&In);revert w In;induction n.
          -- intros w ->;split.
             ++ exists 0;reflexivity.
             ++ apply prod_unit_l.
          -- intros ? (u&w&->&Iu&Iw).
             apply Σ_lang in Iu as (f&If&Iu).
             apply in_map_iff in If as (β'&<-&Iβ').
             apply IHn in Iw as (Iw&Ew).
             apply IHe in Iu as (Iu&Eu).
             split.
             ++ destruct Iw as (m&Im);exists (S m),u,w;tauto.
             ++ simpl_binding.
                rewrite <- prod_assoc,Ew,Eu.
                apply lower_squares_spec in Iβ' as (_&->).
                ** reflexivity.
                ** apply eqX_correct,hβ.
      + intros ((n&In)&E);revert u In E;induction n;simpl.
        * intros ? -> <-;exfalso;apply N;reflexivity.
        * intros ? (u&w&->&Iu&Iw);simpl_binding;intro E.
          assert (Squ : square (𝗙 a u))
            by (destruct Sq as (h1&h2);eapply h2,is_binding_finite_bindings,Iu;assumption).
          assert (Sqw : square (𝗙 a w))
            by (apply sqExpr_star in Sq as (h1&h2);eapply h2,is_binding_finite_bindings;
                [assumption|exists n;apply Iw]).
          cut ((𝗙 a u = β /\ 𝗙 a w ∈ (lower_squares β))\/(𝗙 a w = β /\ 𝗙 a u ∈ (lower_squares β))).
          -- intros [(E1&E2)|(E1&E2)].
             ++ exists u,w;split;[reflexivity|];split.
                ** exists [],u;split;[reflexivity|].
                   split;[exists 0;reflexivity|].
                   apply IHe;tauto.
                ** exists n;revert hβ Sq IHe Iw E2;clear;intros hβ Sq IHe;revert w.
                     induction n;simpl.
                   --- intros w -> _;reflexivity.
                   --- intros ? (u&w&->&Iu&Iw).
                       intros I.
                       cut (𝗙 a u ∈ lower_squares β /\ 𝗙 a w ∈ lower_squares β).
                       +++ intros (I1&I2).
                           exists u,w;split;[reflexivity|];split.
                           *** apply Σ_lang;eexists;split.
                               ---- apply in_map_iff;eexists;split;[reflexivity|apply I1].
                               ---- apply IHe;tauto.
                           *** apply IHn;assumption.
                       +++ apply lower_squares_prod.
                           *** destruct Sq as (h1&h2);eapply h2,is_binding_finite_bindings,Iu;
                                 assumption.
                           *** apply sqExpr_star in Sq as (h1&h2);
                                 eapply h2,is_binding_finite_bindings;
                                 [assumption|exists n;apply Iw].
                           *** apply eqX_correct,hβ.
                           *** revert I;clear;simpl_binding;tauto.
             ++ apply IHn in Iw as (?&w3&->&(w1&w2&->&(n1&I1)&I2)&I3);[|assumption].
                exists ((u++w1)++w2),w3;split;[repeat rewrite app_ass;reflexivity|].
                split;[|assumption].
                exists (u++w1),w2;split;[reflexivity|].
                split;[|assumption].
                exists (S n1),u,w1;split;[reflexivity|].
                split;[|assumption].
                apply Σ_lang;eexists;split.
                ** eapply in_map_iff;eexists;split;[reflexivity|eassumption].
                ** apply IHe;tauto.
          -- assert (Sq' : square β) by (apply eqX_correct,hβ);revert Sq' Squ Sqw E;clear.
             intros s1 s2 s3 E;repeat rewrite lower_squares_spec by assumption.
             cut ( 𝗙 a u = β \/ 𝗙 a w = β).
             ++ intros [E'|E'];rewrite E' in *;[|tauto].
                left;split;[reflexivity|split;[assumption|]].
                rewrite <- E at 2.
                revert s1 s3 E;clear;unfold square,prod_binding,d_binding;simpl.
                destruct β as ((?&?)&?),(𝗙 a w) as ((?,?),?);simpl.
                intros -> ->.
                destruct_ltb n n1;destruct_ltb n1 n;simpl;simpl_nat;try lia||tauto.
                replace n1 with n by lia.
                rewrite orb_comm;reflexivity.
             ++ revert s2 s3 E;clear;unfold square,prod_binding,d_binding;simpl.
                destruct (𝗙 a u) as ((?&?)&?),(𝗙 a w) as ((?,?),?);simpl.
                intros -> ->.
                destruct_ltb n n1;[destruct_ltb n1 n|];simpl;simpl_nat;[|tauto|tauto].
                replace n with n1 in * by lia.
                destruct b;simpl;tauto.
      + intro h;exfalso;apply h.
      + intros (Iu&<-);apply not_true_iff_false in hβ;apply hβ.
        apply sqExpr_star in Sq as (Bf&hE).
        eapply (is_binding_finite_bindings Bf),hE in Iu.
        apply eqX_correct,Iu.
  Qed.

  Lemma filter_binding_inf a β e : is_binding_finite e -> filter_binding a β e <=KA e.
  Proof.
    intros Be;apply CompletenessKA_inf;intros u Iu.
    apply (filter_binding_lang _ _ Be) in Iu;tauto.
  Qed.
  
  Lemma is_binding_finite_filter_binding a β e :
    is_binding_finite e -> is_binding_finite (filter_binding a β e).
  Proof.
    intros Be;pose proof Be as (B&IB);exists B;intros b u Iu;
      rewrite filter_binding_lang in Iu by assumption.
    apply IB;tauto.
  Qed.
    
    
  Lemma filter_binding_act p a β e :
    p ∙ filter_binding a β e = filter_binding (p∙a) β (p∙e).
  Proof.
    revert β;induction e;intro β;simpl.
    - reflexivity.
    - unfold_eqX;reflexivity.
    - unfold act in *;simpl.
      rewrite IHe1,IHe2;reflexivity.
    - replace actReg with act by reflexivity.
      rewrite sizeExpr_act.
      setoid_rewrite Σ_act.
      f_equal.
      unfold act,act_lists at 1;simpl;rewrite map_map.
      unfold act;simpl.
      apply map_ext;intro;replace actReg with act by reflexivity.
      rewrite IHe1,IHe2;reflexivity.
    - unfold is_square;unfold_eqX;simpl.
      + rewrite <- IHe;reflexivity.
      + unfold act at 1;simpl;replace actReg with act by reflexivity.
        replace e_prod with prod by reflexivity.
        replace e_star with star by reflexivity.
        repeat rewrite Σ_act.
        f_equal;[f_equal|].
        * f_equal;f_equal.
          unfold act at 1,act_lists at 1;simpl;rewrite map_map.
          apply map_ext;intro;replace actReg with act by reflexivity.
          rewrite IHe;reflexivity.
        * apply IHe.
        * f_equal;f_equal.
          unfold act at 1,act_lists at 1;simpl;rewrite map_map.
          apply map_ext;intro;replace actReg with act by reflexivity.
          rewrite IHe;reflexivity.
      + reflexivity.  
    - rewrite 𝗳_perm,act_pinv_p.
      unfold_eqX;reflexivity.
  Qed.
    
  Lemma filter_binding_KA a β e f :
    is_binding_finite e -> 
    e =KA f -> filter_binding a β e =KA filter_binding a β f.
  Proof.
    intros Be E.
    assert (Bf : is_binding_finite f)
      by (eapply is_binding_finite_ax_eq;[|apply Be];apply KA_αKA;symmetry;assumption).
    apply CompletenessKA;intro u;repeat rewrite filter_binding_lang by assumption.
    rewrite (soundness E u);tauto.
  Qed.

  Lemma filter_binding_prod_max e e' L a β:
    is_binding_finite e -> is_binding_finite e' ->
    filter_binding a β (e·e')
    =KA Σ (map (fun p  => filter_binding a (fst p) e · filter_binding a (snd p) e')
               (factors β (sizeExpr e) ++ (factors β L))).
  Proof.
    rewrite map_app,<- (@algebra.Σ_app _ _ _ _ _ _ _ _ _ KA_regexp).
    symmetry;rewrite (@semiring_comm _ _ _ _ _ _ (@ka_semiring _ _ _ _ _ _ _ _ KA_regexp) _ _).
    apply CompletenessKA_inf.
    intro u;repeat rewrite Σ_lang.
    intros (g&Ig&Iu);apply in_map_iff in Ig as ((b1,b2)&<-&Ib).
    destruct Iu as (u1&u2&->&I1&I2).
    apply filter_binding_lang in I1 as (I1&E1);[|assumption].
    apply filter_binding_lang in I2 as (I2&E2);[|assumption].
    apply filter_binding_lang.
    - apply binding_finite_spec;simpl;apply orb_true_intro;right;apply andb_true_iff;split;
        apply binding_finite_spec;assumption.
    - split;[exists u1,u2;tauto|].
      apply factors_prod in  Ib.
      simpl_binding;simpl in *;subst;tauto.
  Qed.
    
  Lemma filter_binding_αKA a β e f :
    is_binding_finite e -> 
    {|αKA,KA'|} ⊢ e == f ->
    {|αKA,KA'|} ⊢ filter_binding a β e == filter_binding a β f.
  Proof.
    intros B E;revert β;induction E;intro β.
    - reflexivity.
    - symmetry;apply IHE,(is_binding_finite_ax_eq E),B.
    - etransitivity;[apply IHE1|apply IHE2].
      + assumption.
      + apply (is_binding_finite_ax_eq E1),B.
    - case_eq (test0 (e·e')).
      + intro E;transitivity zero;[|symmetry];apply KA_αKA,test0_spec.
        * case_eq (test0 (filter_binding a β (e · e')));[tauto|].
          intro F;apply test0_false in F as (u&Iu).
          apply (filter_binding_lang a β B) in Iu as ((u1&u2&->&Iu1&Iu2)&_).
          simpl in E;apply orb_true_iff in E as [T|T];apply test0_spec,soundness in T.
          -- apply T in Iu1;exfalso;apply Iu1.
          -- apply T in Iu2;exfalso;apply Iu2.
        * case_eq (test0 (filter_binding a β (f · f')));[tauto|].
          intro F;apply test0_false in F as (u&Iu).
          apply (filter_binding_lang a β) in Iu as (Iu&_);
            [|eapply is_binding_finite_ax_eq;[|apply B];rewrite E1,E2;reflexivity].
          cut (cl_α⟦e·e'⟧ u);[|eapply αKA_lang;[|exists u;split;[eassumption|reflexivity]];
                               rewrite E1,E2;reflexivity].
          intros (v&Iv&_).
          apply test0_spec,soundness in E.
          apply E in Iv;exfalso;apply Iv.
      + intro T0;pose proof B as B0;revert B;simpl;rewrite <- binding_finite_spec;simpl in *;
          rewrite T0;simpl;rewrite andb_true_iff;intros (B1&B2).
        rewrite binding_finite_spec in B1,B2.
        transitivity
          (Σ (map (fun p => filter_binding a (fst p) e · filter_binding a (snd p) e')
                  (factors β (sizeExpr e) ++ factors β (sizeExpr f))));
          [|transitivity
              (Σ (map (fun p => filter_binding a (fst p) f · filter_binding a (snd p) f')
                      (factors β (sizeExpr e) ++ factors β (sizeExpr f))))].
        * apply KA_αKA,filter_binding_prod_max;tauto.
        * apply Σ_map_equiv_α.
          intros;rewrite IHE1,IHE2.
          -- reflexivity.
          -- assumption.
          -- assumption.
        * symmetry.
          apply is_binding_finite_ax_eq in E1.
          apply is_binding_finite_ax_eq in E2.
          etransitivity;[apply KA_αKA,filter_binding_prod_max;tauto|].
          apply algebra.Σ_equivalent.
          apply map_equivalent_Proper.
          apply app_comm.
    - apply binding_finite_spec in B;simpl in B;apply andb_true_iff in B as (B1&B2);
        rewrite binding_finite_spec in B1,B2.
      simpl;rewrite IHE1,IHE2 by assumption.
      reflexivity.
    - apply binding_finite_spec in B;simpl in B;apply andb_true_iff in B as (B&Sq);
        rewrite binding_finite_spec in B.
      simpl;unfold is_square;unfold_eqX;[| |reflexivity].
      + rewrite IHE;[reflexivity|assumption].
      + pose proof (IHE B) as h;clear Sq B IHE E N E0.
        repeat apply ax_eq_prod.
        * apply ax_eq_star,Σ_map_equiv_α;intros;apply h.
        * apply h.
        * apply ax_eq_star,Σ_map_equiv_α;intros;apply h.
    - destruct H.
      + rewrite <- (act_p_pinv [(a0,b)] a) at 2.
        rewrite <- filter_binding_act.
        simpl;unfold act at 2;simpl;unfold_eqX.
        * transitivity (filter_binding b β e).
          -- apply KA_αKA,CompletenessKA.
             intro u;repeat rewrite filter_binding_lang by assumption;split;
               intros (Iu&<-);(split;[tauto|apply H in Iu as (->&->);reflexivity]).
          -- apply ax_eq_ax,αKA_αα.
             intros u Iu;apply filter_binding_lang in Iu as (Iu&_);[|assumption].
             apply H,Iu.
        * transitivity (filter_binding a0 β e).
          -- apply KA_αKA,CompletenessKA.
             intro u;repeat rewrite filter_binding_lang by assumption;split;
               intros (Iu&<-);(split;[tauto|apply H in Iu as (->&->);reflexivity]).
          -- apply ax_eq_ax,αKA_αα.
             intros u Iu;apply filter_binding_lang in Iu as (Iu&_);[|assumption].
             apply H,Iu.
        * apply ax_eq_ax,αKA_αα.
          intros u Iu;apply filter_binding_lang in Iu as (Iu&_);[|assumption].
          apply H,Iu.
      + apply KA_αKA,filter_binding_KA;[assumption|apply ax_eq_ax,H].
    - destruct H;simpl.
      + case_eq (test0 f).
        * intro T;pose proof (filter_binding_test0 T) as T'.
          pose proof (T' a β) as h.
          apply test0_spec,KA_αKA in h as ->.
          rewrite (semiring_comm _ _),(ax_eq_ax _ (αKA_KA (KA_zero _))).
          transitivity zero;[|reflexivity].
          apply ax_inf_PartialOrder;unfold Basics.flip;split;[|apply zero_minimal].
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((b1&b2)&<-&_);simpl.
          pose proof (T' a b2) as h.
          apply test0_spec,KA_αKA in h as ->.
          rewrite (ax_eq_ax _ (αKA_KA (KA_right_zero _)));reflexivity.
        * intro T;assert (is_binding_finite e /\ is_binding_finite f) as (Be&Bf)
            by (revert B;repeat rewrite <- binding_finite_spec;simpl;
                repeat rewrite orb_true_iff||rewrite andb_true_iff;simpl;rewrite T;
                firstorder discriminate).
          cut ({|αKA, KA'|} ⊢ (filter_binding a β (e⋆· f))
                            =<= (filter_binding a β f));[intro h;apply h|].
          assert (IH: forall β, {|αKA, KA'|} ⊢ filter_binding a β (e·f) =<= filter_binding a β f)
            by (apply IHE;revert Be Bf;repeat rewrite <- binding_finite_spec;simpl;
                repeat rewrite orb_true_iff||rewrite andb_true_iff;simpl;intros -> ->;tauto).
          clear IHE.
          simpl;apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((b1&b2)&<-&Ib);simpl.
          unfold is_square;unfold_eqX;[| |rewrite left_absorbing;apply zero_minimal].
          -- subst.
             pose proof (factors_prod Ib) as Eb;rewrite prod_unit_l in Eb;subst.
             apply ka_star_left_ind.
             etransitivity;[|apply IH].
             simpl;apply Σ_bigger,in_map_iff;eexists;split;[|eassumption];reflexivity.
          -- set (E1:= Σ (map (fun α : nat * bool * nat => filter_binding a α e) (lower_squares b1))).
             set (L := (fun b => (b1⋅b) =?= β) :> prj2 (factors β (sizeExpr e))).
             set (F := Σ (map (fun α : nat * bool * nat => filter_binding a α f) L)).
             assert (case_b : forall b, ({|αKA, KA'|}⊢ filter_binding a b e == zero)
                                   \/ size b <= sizeExpr e).
             ++ revert Be;clear;intros Be b.
                case_eq (test0 (filter_binding a b e)).
                ** rewrite test0_spec;intro T';apply KA_αKA in T' as -> .
                   left;reflexivity.
                ** intro Iu;apply test0_false in Iu as (u&Iu).
                   apply (filter_binding_lang _ _ Be) in Iu as (Iu&<-).
                   right;apply binding_finite_bound_size;assumption.
             ++ destruct (case_b b1) as [->|hb1];
                  [repeat rewrite left_absorbing||rewrite right_absorbing;apply zero_minimal|].
                assert ({|αKA, KA'|}⊢ filter_binding a b2 f =<= F
                        /\  {|αKA, KA'|}⊢ E1⋆ · F =<= F
                        /\  {|αKA, KA'|}⊢ filter_binding a b1 e · F =<= filter_binding a β f)
                  as (e1&e2&e3).
                ** split;[|split].
                   --- apply Σ_bigger,in_map_iff;exists b2.
                       split;[reflexivity|].
                       unfold L;simpl_In;rewrite eqX_correct;split.
                       +++ apply in_map_iff;exists (b1,b2);simpl;tauto.
                       +++ apply factors_prod in Ib as ->;reflexivity.
                   --- apply ka_star_left_ind.
                       unfold E1,F;rewrite Σ_distr_l,map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (b'&<-&Ib').
                       rewrite Σ_distr_r,map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (b''&<-&Ib'').
                       transitivity (filter_binding a (b''⋅b') f).
                       +++ etransitivity;[|apply (IH (b''⋅b'))].
                           destruct (case_b b'') as [-> |hb].
                           *** rewrite left_absorbing;apply zero_minimal.
                           *** simpl;apply Σ_bigger,in_map_iff.
                               exists (b'',b');split;[reflexivity|].
                               apply factors_In;[assumption|reflexivity].
                       +++ apply Σ_bigger,in_map_iff.
                           eexists;split;[reflexivity|].
                           unfold L;unfold L in Ib';simpl_In;simpl_In in Ib';rewrite eqX_correct;
                             rewrite eqX_correct in Ib'.
                           destruct Ib' as (Ib'&Eb').
                           pose proof Ib'' as EE.
                           apply (lower_squares_spec _ E0) in EE as (Sq&Eb'').
                           rewrite <- (prod_binding_maxBind Sq E0),maxBind_comm,
                           (prod_binding_maxBind E0 Sq) in Eb''.
                           rewrite prod_assoc,Eb'',Eb';split;[|reflexivity].
                           apply in_map_iff;exists (b1,(b''⋅b'));split;[reflexivity|].
                           apply factors_In;[assumption|].
                           rewrite prod_assoc,Eb'',Eb';reflexivity.
                   --- unfold F;rewrite Σ_distr_l,map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (b'&<-&Ib').
                       etransitivity;[|apply (IH β)].
                       simpl;apply Σ_bigger,in_map_iff.
                       exists (b1,b');split;[reflexivity|].
                       apply factors_In;[assumption|].
                       unfold L in Ib';simpl_In in Ib';rewrite eqX_correct in Ib';tauto.
                ** rewrite e1.
                   repeat rewrite <- (mon_assoc _ _ _).
                   rewrite e2.
                   rewrite e3.
                   apply ka_star_left_ind.
                   unfold E1;rewrite Σ_distr_r,map_map.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as (b'&<-&Ib').
                   destruct (case_b b') as [-> |hb];[rewrite left_absorbing;apply zero_minimal|].
                   etransitivity;[|apply (IH β)].
                   simpl;apply Σ_bigger,in_map_iff.
                   exists (b',β);split;[reflexivity|].
                   apply factors_In;[assumption|].
                   apply (lower_squares_spec _ E0) in Ib' as (Sb'&Eb').
                   apply factors_prod in Ib.
                   rewrite <- Ib,prod_assoc,Eb',Ib at 1;reflexivity.
      + case_eq (test0 e).
        * intro T;pose proof (filter_binding_test0 T) as T'.
          pose proof (T' a β) as h.
          apply test0_spec,KA_αKA in h as ->.
          rewrite (semiring_comm _ _),(ax_eq_ax _ (αKA_KA (KA_zero _))).
          transitivity zero;[|reflexivity].
          apply ax_inf_PartialOrder;unfold Basics.flip;split;[|apply zero_minimal].
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((b1&b2)&<-&_);simpl.
          pose proof (T' a b1) as h.
          apply test0_spec,KA_αKA in h as ->.
          rewrite (ax_eq_ax _ (αKA_KA (KA_left_zero _)));reflexivity.
        * intro T;assert (is_binding_finite e /\ is_binding_finite f) as (Be&Bf)
            by (revert B;repeat rewrite <- binding_finite_spec;simpl;
                repeat rewrite orb_true_iff||rewrite andb_true_iff;simpl;rewrite T;
                firstorder discriminate).
          cut ({|αKA, KA'|} ⊢ (filter_binding a β (e· f⋆))
                            =<= (filter_binding a β e));[intro h;apply h|].
          assert (IH: forall β, {|αKA, KA'|} ⊢ filter_binding a β (e·f) =<= filter_binding a β e)
            by (apply IHE;revert Be Bf;repeat rewrite <- binding_finite_spec;simpl;
                repeat rewrite orb_true_iff||rewrite andb_true_iff;simpl;intros -> ->;tauto).
          clear IHE.
          simpl;apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((b1&b2)&<-&Ib);simpl.
          unfold is_square;unfold_eqX;[| |rewrite right_absorbing;apply zero_minimal].
          -- subst.
             pose proof (factors_prod Ib) as Eb;rewrite prod_unit_r in Eb;subst.
             apply ka_star_right_ind.
             etransitivity;[|apply IH].
             simpl;apply Σ_bigger,in_map_iff;eexists;split;[|eassumption];reflexivity.
          -- set (E1:= Σ (map (fun α : nat * bool * nat => filter_binding a α f) (lower_squares b2))).
             set (L := (fun b => (b⋅b2) =?= β) :> prj1 (factors β (sizeExpr e))).
             set (F := Σ (map (fun α : nat * bool * nat => filter_binding a α e) L)).
             assert (case_b : forall e, is_binding_finite e ->
                                   forall b, ({|αKA, KA'|}⊢ filter_binding a b e == zero)
                                        \/ size b <= sizeExpr e).
             ++ clear;intros e Be b.
                case_eq (test0 (filter_binding a b e)).
                ** rewrite test0_spec;intro T';apply KA_αKA in T' as -> .
                   left;reflexivity.
                ** intro Iu;apply test0_false in Iu as (u&Iu).
                   apply (filter_binding_lang _ _ Be) in Iu as (Iu&<-).
                   right;apply binding_finite_bound_size;assumption.
             ++ pose proof (case_b _ Be) as case_e.
                pose proof (case_b _ Bf) as case_f.
                clear case_b.
                destruct (case_e b1) as [->|hb1];
                  [repeat rewrite left_absorbing||rewrite right_absorbing;apply zero_minimal|].
                destruct (case_f b2) as [->|hb2];
                  [repeat rewrite left_absorbing||rewrite right_absorbing;apply zero_minimal|].
                assert ({|αKA, KA'|}⊢ filter_binding a b1 e =<= F
                        /\  {|αKA, KA'|}⊢ F · E1⋆ =<= F
                        /\  {|αKA, KA'|}⊢ F · filter_binding a b2 f =<= filter_binding a β e)
                  as (e1&e2&e3).
                ** split;[|split].
                   --- apply Σ_bigger,in_map_iff;exists b1.
                       split;[reflexivity|].
                       unfold L;simpl_In;rewrite eqX_correct;split.
                       +++ apply in_map_iff;exists (b1,b2);simpl;tauto.
                       +++ apply factors_prod in Ib as ->;reflexivity.
                   --- apply ka_star_right_ind.
                       unfold E1,F;rewrite Σ_distr_l,map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (b'&<-&Ib').
                       rewrite Σ_distr_r,map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (b''&<-&Ib'').
                       transitivity (filter_binding a (b''⋅b') e).
                       +++ etransitivity;[|apply (IH (b''⋅b'))].
                           destruct (case_e b'') as [-> |hb];
                             [rewrite left_absorbing;apply zero_minimal|].
                           simpl;apply Σ_bigger,in_map_iff.
                           exists (b'',b');split;[reflexivity|].
                           apply factors_In;[assumption|reflexivity].
                       +++ destruct (case_e (b''⋅b')) as [-> |hb];[apply zero_minimal|].
                           apply Σ_bigger,in_map_iff.
                           eexists;split;[reflexivity|].
                           unfold L;unfold L in Ib'';simpl_In;simpl_In in Ib'';rewrite eqX_correct;
                             rewrite eqX_correct in Ib''.
                           destruct Ib'' as (Ib''&Eb').
                           pose proof Ib' as EE.
                           apply (lower_squares_spec _ E0) in EE as (Sq&Eb'').
                           rewrite <-prod_assoc,Eb'',Eb';split;[|reflexivity].
                           apply in_map_iff;exists (b''⋅b',b2);split;[reflexivity|].
                           apply factors_In;[assumption|].
                           rewrite <-prod_assoc,Eb'',Eb';reflexivity.
                   --- unfold F;rewrite Σ_distr_r,map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (b'&<-&Ib').
                       destruct (case_e b') as [-> |hb];
                         [rewrite left_absorbing;apply zero_minimal|].
                       etransitivity;[|apply (IH β)].
                       simpl;apply Σ_bigger,in_map_iff.
                       exists (b',b2);split;[reflexivity|].
                       apply factors_In;[assumption|].
                       unfold L in Ib';simpl_In in Ib';rewrite eqX_correct in Ib';tauto.
                ** rewrite e1.
                   repeat rewrite (mon_assoc _ _ _).
                   rewrite e2.
                   rewrite e3.
                   apply ka_star_right_ind.
                   unfold E1;rewrite Σ_distr_l,map_map.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as (b'&<-&Ib').
                   destruct (case_e β) as [-> |hb];[rewrite left_absorbing;apply zero_minimal|].
                   etransitivity;[|apply (IH β)].
                   simpl;apply Σ_bigger,in_map_iff.
                   exists (β,b');split;[reflexivity|].
                   apply factors_In;[assumption|].
                   apply (lower_squares_spec _ E0) in Ib' as (Sb'&Eb').
                   apply factors_prod in Ib.
                   rewrite <- (prod_binding_maxBind Sb' E0),maxBind_comm,
                   (prod_binding_maxBind E0 Sb') in Eb'.
                   rewrite <- Ib,<-prod_assoc,Eb',Ib at 1;reflexivity.
  Qed.

  Lemma filter_binding_αKA_inf a β e f :
    is_binding_finite f -> 
    {|αKA,KA'|} ⊢ e =<= f ->
    {|αKA,KA'|} ⊢ filter_binding a β e =<= filter_binding a β f.
  Proof.
    intros B E.
    unfold ax_inf in E;apply (@filter_binding_αKA a β) in E.
    - simpl in E;apply E.
    - clear a β;apply αKA_lang in E.
      destruct B as (B&hB);exists B;intros a u Iu.
      cut (cl_α ⟦ f ⟧ u).
      + intros (v&Iv&Ev).
        rewrite <- (αequiv_binding Ev).
        apply hB,Iv.
      + apply E;exists u;split;[assumption|reflexivity].
  Qed.
  
  Lemma filter_binding_δ a β e :
    is_binding_finite e ->
    δ (open a) (filter_binding a (𝗳 a (open a) ⋅ β) (⟪open a⟫·e))
    =KA Σ (map (fun α => filter_binding a α e) (divide_by_open β)).
  Proof.
    intro Be;simpl;simpl_eqX.
    rewrite δ_Σ,map_map.
    apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros f If;
      apply in_map_iff in If as (x&<-&Ix).
    - destruct x as (b1,b2); simpl;destruct_eqX (0,false,1) b1;simpl.
      + replace eq_letter with tools.eqX by reflexivity;simpl_eqX.
        rewrite (ax_eq_ax _ (KA_un_left _));apply Σ_bigger.
        apply in_map_iff;exists b2;split;[reflexivity|].
        subst.
        eapply (divide_by_open_spec).
        eapply factors_prod,Ix.
      + replace (if (0, false, 1) =?= b1 then ⟪ open a ⟫ else 𝟬) with zero
          by (simpl_eqX;reflexivity).
        simpl;simpl_eqX.
        etransitivity;[|apply zero_minimal].
        rewrite (ax_eq_ax _ (KA_left_zero _));reflexivity.
    - transitivity (un· filter_binding a x e);[rewrite (ax_eq_ax _ (KA_un_left _));reflexivity |].
      apply Σ_bigger,in_map_iff;exists (0,false,1,x);simpl;simpl_eqX.
      split.
      + simpl;replace eq_letter with tools.eqX by reflexivity.
        simpl_eqX;reflexivity.
      + apply factors_In.
        * reflexivity.
        * apply (divide_by_open_spec) in Ix.
          revert Ix;simpl;simpl_eqX;tauto.
  Qed.
  Opaque filter_binding.
  


  Lemma filter_binding_star e a β :
    is_binding_finite (e⋆) -> 
    filter_binding a β (e⋆) <=KA Σ (map (fun b => filter_binding a b e) (lower_squares β)) ⋆.
  Proof.
    intros Be';apply CompletenessKA_inf.
    assert (Be : is_binding_finite e)
      by (rewrite <- binding_finite_spec in *;simpl in *;rewrite andb_true_iff in Be';tauto).
    intros u Iu.
    apply filter_binding_lang in Iu as ((n&Iu)&E);[|assumption].
    assert (Sq : ⟦e⋆⟧ u) by (exists n;tauto).
    apply (is_binding_finite_bindings Be' a),(binding_finite_sqExpr_star Be') in Sq.
    rewrite E in *.
    cut (β ∈ (lower_squares β));
      [|apply lower_squares_spec;[assumption|split;[assumption|]];
        etransitivity;[|apply maxBind_idem];
        symmetry;apply prod_binding_maxBind;assumption].
    rewrite <- E at 1;clear E;intros Iu';exists n;revert u Iu Iu';induction n.
    - intros u -> _;reflexivity.
    - intros u (u1&u2&->&Iu1&Iu2).
      simpl_binding;intros Iβ'.
      assert (Sq1 : ⟦e⋆⟧ u1) by (exists 1,u1,[];rewrite app_nil_r;repeat split;tauto).
      apply (is_binding_finite_bindings Be' a),(binding_finite_sqExpr_star Be') in Sq1.
      assert (Sq2 : ⟦e⋆⟧ u2) by (exists n;tauto).
      apply(is_binding_finite_bindings Be' a),(binding_finite_sqExpr_star Be') in Sq2.                
      apply lower_squares_prod in Iβ' as (I1&I2);try assumption.
      exists u1,u2;split;[reflexivity|].
      split.
      + apply Σ_lang;exists (filter_binding a (𝗙 a u1) e);split;[apply in_map_iff;eexists;eauto|].
        apply filter_binding_lang;tauto.
      + apply IHn;assumption.
  Qed.


  Lemma binding_prod_lower_squares a L u e :
    is_binding_finite (e⋆) ->
    ⟦Σ (map (fun b => filter_binding a b e) L)⋆⟧ u ->
    𝗙 a u ∈ (ε::L).
  Proof.
    intro Be';rewrite <- binding_finite_spec in Be';simpl in Be';
      apply andb_true_iff in Be' as (Be&Sq');rewrite binding_finite_spec in Be.
    assert (Sq : forall u, ⟦e⟧ u -> square (𝗙 a u)).
    - clear u;intros u Iu.
      case_in a ⌊e⌋.
      + apply (is_binding_finite_bindings Be a) in Iu.
        repeat setoid_rewrite forallb_forall in Sq';apply (Sq' a I) in Iu.
        apply eqX_correct,Iu.
      + apply support_lang in Iu.
        rewrite <- Iu in I.
        apply αfresh_support in I as ->;reflexivity.
    - clear Sq';intros (n&Iu).
      cut (square (𝗙 a u) /\ 𝗙 a u ∈ (ε::L));[tauto|].
      revert u Iu;induction n.
      + intros u ->;split;[reflexivity|now left].
      + intros u (u1&u2&->&Iu1&Iu2).
        simpl_binding.
        apply IHn in Iu2 as (Sq2&Iu2);simpl in Iu2.
        apply Σ_lang in Iu1 as (g&Ig&Iu1).
        apply in_map_iff in Ig as (β&<-&Iβ).
        apply filter_binding_lang in Iu1 as (Iu1&<-);[|assumption].
        apply Sq in Iu1 as Sq1.
        rewrite <- (prod_binding_maxBind Sq1 Sq2).
        destruct (maxBind_square_disj Sq1 Sq2) as [-> | ->];tauto.
  Qed.
  

  Lemma filter_binding_zero a β1 β2 e :
    is_binding_finite e -> β1 <> β2 -> filter_binding a β1 (filter_binding a β2 e) =KA zero.
  Proof.
    intros Be N;apply test0_spec,not_false_is_true.
    intro Iu;apply test0_false in Iu as (u&Iu).
    apply filter_binding_lang in Iu as (Iu&<-);[|apply is_binding_finite_filter_binding,Be].
    apply filter_binding_lang in Iu as (Iu&<-);[|apply Be].
    apply N;reflexivity.
  Qed.

  Lemma filter_binding_twice a β e :
    is_binding_finite e ->
    filter_binding a β (filter_binding a β e) =KA filter_binding a β e.
  Proof.
    intros Be;apply CompletenessKA;intro u.
    repeat rewrite filter_binding_lang by (try apply is_binding_finite_filter_binding;assumption).
    tauto.
  Qed.
  
  Transparent filter_binding.
  Lemma filter_binding_support a β e : ⌊filter_binding a β e⌋ ⊆ ⌊e⌋.
  Proof.
    revert β;induction e;intros β;simpl.
    - reflexivity.
    - unfold_eqX;reflexivity.
    - unfold support in *;simpl.
      rewrite IHe1,IHe2;reflexivity.
    - rewrite <- Σ_support.
      intros b Ib;apply In_support_list in Ib as (f&If&Ib).
      apply in_map_iff in If as ((β1,β2)&<-&_).
      unfold support in *;simpl in *.
      rewrite IHe1,IHe2 in Ib;tauto.
    - unfold is_square;unfold_eqX.
      + apply IHe.
      + repeat rewrite support_prod||rewrite support_star.
        rewrite <- Σ_support.
        intros b;simpl_In;intros [[Ib|Ib]|Ib].
        * apply In_support_list in Ib as (f&If&Ib).
          apply in_map_iff in If as ((β1,β2)&<-&_).
          apply IHe in Ib;apply Ib.
        * apply IHe in Ib;apply Ib.
        * apply In_support_list in Ib as (f&If&Ib).
          apply in_map_iff in If as ((β1,β2)&<-&_).
          apply IHe in Ib;apply Ib.
      + apply incl_nil.
    - unfold_eqX;[reflexivity|apply incl_nil].
  Qed.
  Opaque filter_binding.
End s.