Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp systems.
Require Import factors aeq_facts.
Require Import alpha_regexp closed_languages binding_finite alphaKA.
Require Import filters splits.

Opaque filter_binding.
Opaque lower_squares.

Section s.

  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.

  Notation Regexp := (@regexp letter).

  Definition range (e f :Regexp) : list (𝖡*𝖡):=
    flat_map (fun m => pairs
                      (map (fun x => (x,m)) (pairs [0] [true;false]))
                      (pairs (pairs (seq 0 (S m)) [true;false]) (seq 0 (S(sizeExpr f)))))
             (seq 0 (S(sizeExpr e))).

  Lemma range_result e f b1 b2 : (b1,b2) ∈ range e f -> d_binding (b1 ⋅ b2) = 0.
  Proof.
    unfold range.
    destruct b1 as ((n1,m1),p1),b2 as ((n2,m2),p2).
    rewrite in_flat_map.
    setoid_rewrite pairs_spec.
    setoid_rewrite in_map_iff.
    setoid_rewrite pairs_spec.
    setoid_rewrite pairs_spec.
    setoid_rewrite in_seq.
    simpl; simpl_binding.
    intros (?&e1&(?&e2&e3)&(e4&_)&e5).
    inversion e2;clear e2;subst.
    destruct e3 as [e3|[e3|e3]];inversion e3;clear e3;subst;lia.
  Qed.       
  Lemma range_In e f a u1 u2 :
    is_binding_finite e -> is_binding_finite f ->
    ⟦e⟧ u1 -> ⟦f⟧ u2 -> a ◁ (u1++u2) ->
    (𝗙 a u1,𝗙 a u2) ∈ range e f.
  Proof.
    intros Be Bf Ie If.
    unfold close_balanced; intro Eq;simpl_binding in Eq.
    apply (binding_finite_bound_size a Be) in Ie.
    apply (binding_finite_bound_size a Bf) in If.
    destruct (𝗙 a u1) as ((n1,m1),p1),(𝗙 a u2) as ((n2,m2),p2).
    unfold size,d_binding in *;simpl in Ie,If,Eq.
    unfold range.
    apply in_flat_map;exists p1;split.
    - apply in_seq;lia.
    - apply pairs_spec;split.
      + apply in_map_iff;exists (0,m1);split.
        * f_equal;f_equal;lia.
        * destruct m1;simpl;tauto.
      + apply pairs_spec;split.
        * apply pairs_spec;split.
          -- apply in_seq;lia.
          -- destruct m2;simpl;tauto.
        * apply in_seq;lia.
  Qed.

  Lemma range_act p p' e f : range (p∙e) (p'∙f) = range e f.
  Proof. unfold range;repeat rewrite sizeExpr_act;reflexivity. Qed.
    
  Opaque range.
  
  Fixpoint δ1 a e :=
    match e with
    | e_zero | e_un | ⟪close _⟫ | ⟪var _⟫ => 𝟬
    | ⟪open b⟫ => if a =?= b then 𝟭 else 𝟬
    | e_add e f => δ1 a e ∪ δ1 a f
    | e_prod e f => (ϵ e · δ1 a f)
                     ∪ Σ (map (fun p => filter_binding a (fst p) (δ1 a e) · filter_binding a (snd p) f)
                              (range (δ1 a e) f))
    | e_star e =>
      Σ (map (fun p => filter_binding a (fst p) (δ1 a e) · filter_binding a (snd p) (e⋆)) (range (δ1 a e) (e⋆)))
    end.

  Lemma test0_δ1 a e :
    test0 e = true -> test0 (δ1 a e) = true.
  Proof.
    induction e;simpl.
    - reflexivity.
    - discriminate.
    - rewrite andb_true_iff;intros (h1&h2);rewrite IHe1,IHe2 by assumption;reflexivity.
    - rewrite orb_true_iff;intros [h|h].
      + apply andb_true_iff;split.
        * destruct (ϵ_zero_or_un e1) as [F| ->];simpl;[|reflexivity].
          apply test0_spec,soundness in h as T.
          exfalso;apply ϵ_spec,T in F;apply F.
        * rewrite test0_Σ;apply forallb_forall;intros f If.
          apply in_map_iff in If as (?&<-&_).
          simpl;apply orb_true_iff;left.
          simpl;apply filter_binding_test0.
          tauto.
      + apply andb_true_iff;split.
        * rewrite IHe2 by assumption;apply orb_true_r.
        * rewrite test0_Σ;apply forallb_forall;intros f If.
          apply in_map_iff in If as (?&<-&_).
          simpl;apply orb_true_iff;right.
          simpl;apply filter_binding_test0.
          tauto.
    - discriminate.
    - discriminate.
  Qed.
          
  
  Lemma is_binding_finite_δ1 a e :
    is_binding_finite e -> is_binding_finite (δ1 a e).
  Proof.
    intro Be;rewrite <- binding_finite_spec;induction_bin_fin e Be;simpl.
    - reflexivity.
    - reflexivity.
    - destruct x as [b|b|x];[unfold_eqX| |];reflexivity.
    - rewrite IHe1,IHe2;reflexivity.
    - apply andb_true_iff;split.
      + rewrite IHe2.
        destruct (ϵ_zero_or_un e1) as [-> | ->];simpl;[apply orb_true_r|reflexivity].
      + rewrite binding_finite_Σ;apply forallb_forall;intros f If.
        apply in_map_iff in If as (b&<-&_).
        simpl.
        eapply is_binding_finite_filter_binding,binding_finite_spec in B2 as ->.
        eapply binding_finite_spec,is_binding_finite_filter_binding,binding_finite_spec in IHe1 as ->.
        simpl;apply orb_true_r.
    - apply orb_true_iff in T as [T|T].
      + apply andb_true_iff;split.
        * apply orb_true_iff;left.
          apply orb_true_iff;left.
          destruct (ϵ_zero_or_un e1) as [F| ->];simpl;[|reflexivity].
          apply test0_spec,soundness in T.
          exfalso;apply ϵ_spec,T in F;apply F.
        * rewrite binding_finite_Σ;apply forallb_forall;intros f If.
          apply in_map_iff in If as (b&<-&_).
          simpl;apply orb_true_iff;left.
          apply orb_true_iff;left.
          simpl;apply filter_binding_test0.
          apply test0_δ1,T.
      + apply andb_true_iff;split.
        * apply orb_true_iff;left.
          apply orb_true_iff;right.
          apply test0_δ1,T.
        * rewrite binding_finite_Σ;apply forallb_forall;intros f If.
          apply in_map_iff in If as (b&<-&_).
          simpl;apply orb_true_iff;left.
          apply orb_true_iff;right.
          simpl;apply filter_binding_test0,T.
    - rewrite binding_finite_Σ;apply forallb_forall;intros f If.
      apply in_map_iff in If as (?&<-&_);simpl.
      apply orb_true_iff;right.
      apply andb_true_iff;split.
      + eapply binding_finite_spec,is_binding_finite_filter_binding,binding_finite_spec,IHe.
      + eapply binding_finite_spec,is_binding_finite_filter_binding.
        apply sqExpr_bindings_finite_star,Sq.
  Qed.
      
  Lemma δ1_lang a e :
    is_binding_finite e -> ⟦δ1 a e⟧ ≃ (fun u => ⟦e⟧ (open a::u) /\ a ◁ u).
  Proof.
    intro Be;induction_bin_fin e Be;simpl.
    - intro u;simpl;unfold zero,zeroLang;tauto.
    - intro u;split;intro Iu;exfalso;[apply Iu|destruct Iu as (Iu&_);discriminate].
    - destruct x as [b|b|x].
      + unfold_eqX.
        * intro u;split.
          -- intros ->;split;reflexivity.
          -- intros (e&_);inversion e;reflexivity.
        * intro u;split;intro Iu;exfalso;[apply Iu|destruct Iu as (e&_);inversion e;tauto].
      + intro u;split;intro Iu;exfalso;[apply Iu|destruct Iu as (e&_);inversion e].
      + intro u;split;intro Iu;exfalso;[apply Iu|destruct Iu as (e&_);inversion e].
    - rewrite IHe1,IHe2;intro u;simpl;unfold join,joinLang;tauto.
    - intros u;split.
      + intros [Iu|Iu].
        * destruct Iu as (u1&u2&->&Iu1&Iu2).
          revert Iu1;destruct (ϵ_zero_or_un e1) as [E | E];rewrite E.
          -- intros ->;simpl.
             apply IHe2 in Iu2 as (Iu2&h).
             split;[|tauto].
             exists [];eexists;split;[|split;[|eassumption]];[reflexivity|].
             apply ϵ_spec,E.
          -- intro h;exfalso;apply h.
        * apply Σ_lang in Iu as (g&Ig&Iu).
          apply in_map_iff in Ig as ((b1&b2)&<-&I).
          destruct Iu as (u1&u2&->&I1&I2).
          simpl in *;apply (filter_binding_lang _ _ (is_binding_finite_δ1 _ B1)) in I1 as (I1&E1).
          apply (filter_binding_lang _ _ B2) in I2 as (I2&E2).
          apply IHe1 in I1 as (I1&E1').
          split.
          -- exists (open a::u1),u2;tauto.
          -- unfold close_balanced;rewrite 𝗙_app.
             rewrite E1,E2;apply (range_result I).
      + intros ((u1&u2&E&I1&I2)&Eq).
        destruct u1;simpl in E;inversion E;clear E;subst.
        * left;exists [],u;split;[reflexivity|split].
          -- apply ϵ_spec in I1 as ->;reflexivity.
          -- apply IHe2;tauto.
        * right;apply Σ_lang.
          eexists;split;[apply in_map_iff;exists (𝗙 a u1,𝗙 a u2);split;[reflexivity|]|].
          -- apply range_In.
             ++ apply is_binding_finite_δ1,B1.
             ++ assumption.
             ++ apply IHe1;split;[assumption|].
                eapply close_balanced_prefix,Eq.
             ++ assumption.
             ++ assumption.
          -- exists u1,u2;split;[reflexivity|split].
             ++ apply filter_binding_lang.
                ** apply is_binding_finite_δ1,B1.
                ** split;[|reflexivity].
                   apply IHe1;split;[assumption|].
                   eapply close_balanced_prefix,Eq.
             ++ apply filter_binding_lang;simpl;tauto.
    - cut (test0 (e1·e2) = true);[|apply T].
      clear T;intro T;pose proof T as T'.
      apply (test0_δ1 a),test0_spec,soundness in T.
      apply test0_spec,soundness in T'.
      intro u;rewrite (T' (open a::u)).
      rewrite (T u);simpl;unfold zero,zeroLang;tauto.
    - intros u;split;intros Iu.
      + apply Σ_lang in Iu as (g&Ig&Iu).
        apply in_map_iff in Ig  as ((b1&b2)&<-&I).
        destruct Iu as (u1&u2&->&I1&I2).
        apply filter_binding_lang in I1 as (I1&E1);[|apply is_binding_finite_δ1,Sq].
        apply filter_binding_lang in I2 as (I2&E2);[|apply sqExpr_bindings_finite_star,Sq].
        simpl in *.
        unfold close_balanced;rewrite 𝗙_app.
        subst;split.
        * apply IHe in I1 as (I1&E).
          destruct I2 as (n&I2);exists (S n),(open a::u1),u2;tauto.
        * apply (range_result I).
      + cut (⟦positive e·e⋆⟧ (open a::u)).
        * destruct Iu as (_&Eq).
          intros (u1&u2&E&I1&I2).
          apply positive_lang in I1 as (I1&N).
          destruct u1;[tauto|inversion E;clear E N;subst].
          apply Σ_lang;eexists;split.
          -- apply in_map_iff;exists (𝗙 a u1,𝗙 a u2);split;[reflexivity|].
             apply range_In.
             ++ apply is_binding_finite_δ1,Sq.
             ++ apply sqExpr_bindings_finite_star,Sq.
             ++ apply IHe;split;[assumption|].
                eapply close_balanced_prefix;eassumption.
             ++ assumption.
             ++ assumption.
          -- exists u1,u2;split;[reflexivity|].
             split;apply filter_binding_lang.
             ++ apply is_binding_finite_δ1,Sq.
             ++ simpl;split;[|reflexivity].
                apply IHe;split;[assumption|].
                eapply close_balanced_prefix;eassumption.
             ++ apply sqExpr_bindings_finite_star,Sq.
             ++ tauto.
        * cut (⟦positive (e⋆)⟧ (open a::u)).
          -- simpl;tauto.
          -- apply positive_lang.
             split;[tauto|discriminate].
  Qed.


  Lemma δ1_KA a e f :
    is_binding_finite f -> e =KA f -> δ1 a e =KA δ1 a f.
  Proof.
    intros Bf E.
    assert (Be : is_binding_finite e)
      by (eapply is_binding_finite_ax_eq;[apply KA_αKA,E|apply Bf]).
    apply soundness in E;apply CompletenessKA.
    rewrite (δ1_lang a Be),(δ1_lang a Bf).
    intro u;simpl;rewrite (E (open a::u));tauto.
  Qed.

  Lemma δ1_KA_inf a e f :
    is_binding_finite f -> e <=KA f -> δ1 a e <=KA δ1 a f.
  Proof. unfold ax_inf;apply (@δ1_KA a (e_add e f) f). Qed.

  Lemma δ1_act p a e : δ1 a (p∙e) = p∙δ1 (p∗∙a) e.
  Proof.
    induction e.
    - reflexivity.
    - reflexivity.
    - simpl;replace actReg with act by reflexivity.
      rewrite IHe1,IHe2;reflexivity.
    - simpl.
      replace act with actReg by reflexivity;simpl.
      replace actReg with act by reflexivity.
      unfold join,regJoin;f_equal.
      + rewrite IHe2,ϵ_act.
        unfold prod,regProduct;f_equal.
        destruct (ϵ_zero_or_un e1) as [-> | ->];reflexivity.
      + rewrite Σ_act;f_equal.
        unfold act at 5,act_lists.
        rewrite map_map.
        rewrite IHe1,range_act.
        apply map_ext.
        intros (?,?);simpl.
        unfold act at 4;simpl.
        unfold prod,regProduct;f_equal;replace actReg with act by reflexivity.
        * rewrite filter_binding_act,act_p_pinv;reflexivity.
        * rewrite filter_binding_act,act_p_pinv;reflexivity.
    - replace act with actReg by reflexivity;simpl.
      replace actReg with act by reflexivity.
      rewrite Σ_act;f_equal.
      unfold act at 5,act_lists.
      rewrite map_map.
      rewrite <-(@range_act p p (δ1 (p∗∙a) e) (e⋆)),<-IHe.
      replace act with actReg by reflexivity;simpl.
      replace actReg with act by reflexivity.
      rewrite IHe.
      apply map_ext.
      intros (?,?);simpl.
      unfold act at 4;simpl.
      unfold prod,regProduct;f_equal;replace actReg with act by reflexivity.
      * rewrite filter_binding_act,act_p_pinv;reflexivity.
      * setoid_rewrite filter_binding_act.
        rewrite act_p_pinv;reflexivity.
    - destruct x as [b|b|x];simpl;[|reflexivity|reflexivity].
      destruct_eqX a (p∙b).
      + rewrite act_pinv_p;simpl_eqX;reflexivity.
      + unfold_eqX;[|reflexivity].
        exfalso;apply N;rewrite <-E,act_p_pinv;reflexivity.
  Qed.

  Lemma δ1_αKA a e f :
    is_binding_finite f -> e =α f -> δ1 a e =α δ1 a f.
  Proof.
    intros Bf Eq;induction Eq.
    - reflexivity.
    - symmetry;apply IHEq.
      apply (is_binding_finite_ax_eq Eq),Bf.
    - cut (is_binding_finite e /\ is_binding_finite f).
      + intros (Be&Bf').
        etransitivity;[apply IHEq1|apply IHEq2];assumption.
      + apply is_binding_finite_ax_eq in Eq1.
        apply is_binding_finite_ax_eq in Eq2.
        tauto.
    - apply binding_finite_spec in Bf;simpl in Bf;apply orb_true_iff in Bf as [Bf|Bf].
      + assert (T: test0 (f·f') = true) by apply Bf.
        pose proof T as T'.
        eapply test0_δ1,test0_spec,KA_αKA in T' as ->.
        apply KA_αKA,test0_spec,test0_δ1.
        erewrite test0_αKA;[apply T|rewrite Eq1,Eq2];reflexivity.
      + apply andb_true_iff in Bf as (Bf&Bf');apply binding_finite_spec in Bf;
          apply binding_finite_spec in Bf'.
        pose proof (IHEq1 Bf) as IH;pose proof (IHEq2 Bf') as IH';clear IHEq1 IHEq2.
        simpl;rewrite (ϵ_αKA Eq1),IH' at 1.
        apply ax_eq_add;[reflexivity|].
        apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g Ig;
          apply in_map_iff in Ig as ((b1,b2)&<-&Ib);simpl.
        * transitivity (filter_binding a b1 (δ1 a f) · filter_binding a b2 f').
          -- apply proper_prod_inf;apply filter_binding_αKA_inf.
             ++ apply is_binding_finite_δ1,Bf.
             ++ rewrite IH;reflexivity.
             ++ assumption.
             ++ rewrite Eq2;reflexivity.
          -- case_eq (test0 (filter_binding a b1 (δ1 a f) · filter_binding a b2 f')).
             ++ intros E;apply test0_spec,KA_αKA in E as -> ;
                  transitivity zero;[reflexivity|apply zero_minimal].
             ++ intros Iu;apply test0_false in Iu as (u&u1&u2&->&I1&I2).
                apply filter_binding_lang in I1 as (I1&<-);
                  [|apply is_binding_finite_δ1,Bf].
                apply filter_binding_lang in I2 as (I2&<-);[|assumption].
                apply Σ_bigger,in_map_iff;exists (𝗙 a u1,𝗙 a u2);split;[reflexivity|].
                apply range_In;try assumption.
                ** apply is_binding_finite_δ1,Bf.
                ** unfold close_balanced;rewrite 𝗙_app;eapply range_result,Ib.
        * transitivity (filter_binding a b1 (δ1 a e) · filter_binding a b2 e').
          -- apply proper_prod_inf;apply filter_binding_αKA_inf.
             ++ eapply is_binding_finite_ax_eq;[eassumption|].
                apply is_binding_finite_δ1,Bf.
             ++ rewrite IH;reflexivity.
             ++ eapply is_binding_finite_ax_eq;eassumption.
             ++ rewrite Eq2;reflexivity.
          -- case_eq (test0 (filter_binding a b1 (δ1 a e) · filter_binding a b2 e')).
             ++ intros E;apply test0_spec,KA_αKA in E as -> ;
                  transitivity zero;[reflexivity|apply zero_minimal].
             ++ intros Iu;apply test0_false in Iu as (u&u1&u2&->&I1&I2).
                apply filter_binding_lang in I1 as (I1&<-);
                  [|eapply is_binding_finite_ax_eq;[eassumption|];apply is_binding_finite_δ1,Bf].
                apply filter_binding_lang in I2 as (I2&<-);
                  [|eapply is_binding_finite_ax_eq;eassumption].
                apply Σ_bigger,in_map_iff;exists (𝗙 a u1,𝗙 a u2);split;[reflexivity|].
                apply range_In;try assumption.
                ** eapply is_binding_finite_ax_eq;[eassumption|].
                   apply is_binding_finite_δ1,Bf.
                ** eapply is_binding_finite_ax_eq;eassumption.
                ** unfold close_balanced;rewrite 𝗙_app;eapply range_result,Ib.
    - simpl.
      apply binding_finite_spec in Bf;simpl in Bf;apply andb_true_iff in Bf as (Bf&Bf');
        apply binding_finite_spec in Bf;apply binding_finite_spec in Bf'.
      rewrite IHEq1,IHEq2.
      + reflexivity.
      + apply is_binding_finite_ax_eq in Eq1;tauto.
      + apply is_binding_finite_ax_eq in Eq2;tauto.
    - pose proof Bf as Bf'.
      apply binding_finite_spec in Bf';simpl in Bf';apply andb_true_iff in Bf' as (Bf'&Sq).
      apply binding_finite_spec in Bf';rewrite forallb_forall in Sq.
      setoid_rewrite forallb_forall in Sq.
      pose proof (IHEq Bf') as IH;clear IHEq.
      simpl.
      apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g Ig;
        apply in_map_iff in Ig as ((b1,b2)&<-&Ib);simpl.
      + transitivity (filter_binding a b1 (δ1 a f) · filter_binding a b2 (f⋆)).
        * apply proper_prod_inf;apply filter_binding_αKA_inf.
          -- apply is_binding_finite_δ1,Bf'.
          -- rewrite IH;reflexivity.
          -- assumption.
          -- rewrite Eq;reflexivity.
        * case_eq (test0 (filter_binding a b1 (δ1 a f) · filter_binding a b2 (f⋆))).
          -- intros E;apply test0_spec,KA_αKA in E as -> ;
               transitivity zero;[reflexivity|apply zero_minimal].
          -- intros Iu;apply test0_false in Iu as (u&u1&u2&->&I1&I2).
             apply filter_binding_lang in I1 as (I1&<-);
               [|apply is_binding_finite_δ1,Bf'].
             apply filter_binding_lang in I2 as (I2&<-);[|assumption].
             apply Σ_bigger,in_map_iff;exists (𝗙 a u1,𝗙 a u2);split;[reflexivity|].
             apply range_In;try assumption.
             ++ apply is_binding_finite_δ1,Bf'.
             ++ unfold close_balanced;rewrite 𝗙_app;eapply range_result,Ib.
      + transitivity (filter_binding a b1 (δ1 a e) · filter_binding a b2 (e⋆)).
        * apply proper_prod_inf;apply filter_binding_αKA_inf.
          -- eapply is_binding_finite_ax_eq;[eassumption|].
             apply is_binding_finite_δ1,Bf'.
          -- rewrite IH;reflexivity.
          -- eapply is_binding_finite_ax_eq;[rewrite Eq;reflexivity|assumption].
          -- rewrite Eq;reflexivity.
        * case_eq (test0 (filter_binding a b1 (δ1 a e) · filter_binding a b2 (e⋆))).
          -- intros E;apply test0_spec,KA_αKA in E as -> ;
               transitivity zero;[reflexivity|apply zero_minimal].
          -- intros Iu;apply test0_false in Iu as (u&u1&u2&->&I1&I2).
             apply filter_binding_lang in I1 as (I1&<-);
               [|eapply is_binding_finite_ax_eq;[eassumption|];apply is_binding_finite_δ1,Bf'].
             apply filter_binding_lang in I2 as (I2&<-);
               [|eapply is_binding_finite_ax_eq;[rewrite Eq;reflexivity|assumption]].
             apply Σ_bigger,in_map_iff;exists (𝗙 a u1,𝗙 a u2);split;[reflexivity|].
             apply range_In;try assumption.
             ++ eapply is_binding_finite_ax_eq;[eassumption|].
                apply is_binding_finite_δ1,Bf'.
             ++ eapply is_binding_finite_ax_eq;[rewrite Eq;reflexivity|assumption].
             ++ unfold close_balanced;rewrite 𝗙_app;eapply range_result,Ib.
    - destruct H as [b c e h|e f h];[|apply KA_αKA,δ1_KA;[assumption|apply ax_eq_ax,h]].
      rewrite δ1_act.
      unfold act at 2;simpl;unfold_eqX;subst.
      + apply is_binding_finite_act in Bf.
        transitivity zero;[|cut (δ1 c e =α zero);
                            [intro eq;eapply αKA_act in eq;rewrite eq;reflexivity|]];
        apply KA_αKA,test0_spec;[case_eq (test0 (δ1 b e))|case_eq (test0 (δ1 c e))];try reflexivity;
          intros Iu;exfalso;apply test0_false in Iu as (u&Iu);
            apply (δ1_lang _ Bf) in Iu as (Iu&Eu);apply h in Iu.
        * destruct Iu as (F&_);revert Eu F;unfold fresh__α,close_balanced,d_binding;simpl_binding.
          destruct (𝗙 b u) as ((k1&k2)&k3);simpl;intros ->.
          unfold prod_binding;simpl.
          intro eq;inversion eq;lia.
        * destruct Iu as (_&F);revert Eu F;unfold fresh__α,close_balanced,d_binding;simpl_binding.
          destruct (𝗙 c u) as ((k1&k2)&k3);simpl;intros ->.
          unfold prod_binding;simpl.
          intro eq;inversion eq;lia.
      + apply is_binding_finite_act in Bf.
        transitivity zero;[|cut (δ1 b e =α zero);
                            [intro eq;eapply αKA_act in eq;rewrite eq;reflexivity|]];
        apply KA_αKA,test0_spec;[case_eq (test0 (δ1 c e))|case_eq (test0 (δ1 b e))];try reflexivity;
          intros Iu;exfalso;apply test0_false in Iu as (u&Iu);
            apply (δ1_lang _ Bf) in Iu as (Iu&Eu);apply h in Iu.
        * destruct Iu as (_&F);revert Eu F;unfold fresh__α,close_balanced,d_binding;simpl_binding.
          destruct (𝗙 c u) as ((k1&k2)&k3);simpl;intros ->.
          unfold prod_binding;simpl.
          intro eq;inversion eq;lia.
        * destruct Iu as (F&_);revert Eu F;unfold fresh__α,close_balanced,d_binding;simpl_binding.
          destruct (𝗙 b u) as ((k1&k2)&k3);simpl;intros ->.
          unfold prod_binding;simpl.
          intro eq;inversion eq;lia.
      + apply ax_eq_ax,αKA_αα;intros u Iu.
        apply is_binding_finite_act in Bf.
        apply (δ1_lang _ Bf) in Iu as (Iu&eq).
        apply h in Iu;revert Iu.
        unfold fresh__α;simpl_binding;rewrite prod_unit_l,prod_unit_l;tauto.
    - destruct H.
      + assert (eq : e · f <=α f) by apply Eq;clear Eq.
        assert (ih :  δ1 a (e · f) <=α  δ1 a f) by (apply IHEq,Bf);clear IHEq.
        cut (δ1 a (e⋆·f) <=α δ1 a f);[intro h;apply h|].
        assert (e1 : e⋆·f <=αf) by (apply ka_star_left_ind,eq).
        assert (Bf' : is_binding_finite (δ1 a f)) by (apply is_binding_finite_δ1,Bf).
        assert (δ1 a (e⋆ · f)=KA zero \/ (is_binding_finite e /\ is_binding_finite (e⋆)))
          as [E|(Be1&Be2)];[|apply KA_αKA in E as ->;apply zero_minimal|].
        * cut (is_binding_finite (e⋆·f)).
          -- intro B;cut (f =KA zero \/ is_binding_finite e /\ is_binding_finite (e ⋆)).
             ++ intros [E|E];[left|right;assumption].
                apply test0_spec;apply test0_spec in E.
                apply test0_δ1;simpl;rewrite E;reflexivity.
             ++ revert B.
                repeat rewrite <- binding_finite_spec;simpl.
                repeat rewrite andb_true_iff||rewrite orb_true_iff||rewrite test0_spec.
                replace e_zero with zero by reflexivity.
                tauto.
          -- destruct Bf as (B&h);exists B;apply αKA_lang_inf in e1;clear ih Bf' eq.
             intros b u Iu.
             cut (cl_α ⟦f⟧ u);[|apply e1;exists u;split;[assumption|reflexivity]].
             intros (v&Iv&Ev).
             rewrite <- (αequiv_binding Ev);apply h,Iv.
        * assert (Be3 : is_binding_finite (δ1 a e)) by apply is_binding_finite_δ1,Be1.
          simpl;replace e_un with un by reflexivity.
          rewrite left_unit.
          apply inf_join_inf;[reflexivity|].
          set (E:= Σ (map (fun p => filter_binding a (fst p) (δ1 a e) · filter_binding a (snd p) (e ⋆))
                          (range (δ1 a e) (e ⋆)))).
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((b1&b2)&<-&Ib);simpl.
          unfold E;rewrite filter_binding_Σ,map_map,Σ_distr_r,map_map.
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((c1&c2)&<-&Ic);simpl.
          destruct_eqX b1 (c1⋅c2);
            [cut (filter_binding a (c1 ⋅ c2) (filter_binding a c1 (δ1 a e) · filter_binding a c2 (e ⋆))
                  =KA filter_binding a c1 (δ1 a e) · filter_binding a c2 (e ⋆))
            |cut (filter_binding a b1 (filter_binding a c1 (δ1 a e) · filter_binding a c2 (e ⋆))
                  =KA zero)].
          -- intro Eq;apply KA_αKA in Eq as ->.
             transitivity (filter_binding a c1 (δ1 a e)· filter_binding a (c2⋅b2) f).
             ++ rewrite <- (mon_assoc _ _ _).
                apply proper_prod_inf;[reflexivity|].
                transitivity (filter_binding a (c2⋅b2) (e⋆·f)).
                ** apply KA_αKA_inf,CompletenessKA_inf.
                   intros u (u1&u2&->&I1&I2).
                   apply filter_binding_lang in I1 as (I1&<-);[|assumption].
                   apply filter_binding_lang in I2 as (I2&<-);[|assumption].
                   apply filter_binding_lang;[|split].
                   --- apply binding_finite_spec;simpl;apply orb_true_intro;right;
                         apply andb_true_iff;split;[|apply binding_finite_spec;assumption].
                       apply binding_finite_spec in Be2;apply Be2.
                   --- exists u1,u2;tauto.
                   --- simpl_binding;reflexivity.
                ** apply filter_binding_αKA_inf;assumption.
             ++ etransitivity;[|apply ih].
                simpl;etransitivity;[|apply inf_cup_right].
                case_eq (test0 (filter_binding a c1 (δ1 a e) · filter_binding a (c2 ⋅ b2) f)).
                ** intro T;apply test0_spec,KA_αKA in T as ->.
                   transitivity zero;[reflexivity|apply zero_minimal].
                ** intro Iu;apply test0_false in Iu as (?&u1&u2&->&I1&I2).
                   apply Σ_bigger,in_map_iff.
                   exists (c1,c2⋅b2);split;[reflexivity|].
                   apply filter_binding_lang in I1 as (I1&E1);[|assumption].
                   apply filter_binding_lang in I2 as (I2&E2);[|assumption].
                   rewrite <-E1,<- E2;apply range_In;try assumption.
                   unfold close_balanced;rewrite 𝗙_app.
                   rewrite E1,E2,prod_assoc.
                   eapply range_result,Ib.
          -- apply CompletenessKA;intro u;simpl;split;intros Iu.
             ++ apply filter_binding_lang in Iu as ((u1&u2&->&I1&I2)&E1);[exists u1,u2;tauto|].
                apply binding_finite_spec;simpl;apply orb_true_intro;right;apply andb_true_iff;split;
                  apply binding_finite_spec,is_binding_finite_filter_binding;assumption.
             ++ destruct Iu as (u1&u2&->&I1&I2).
                apply filter_binding_lang.
                ** apply binding_finite_spec;simpl;apply orb_true_intro;right;apply andb_true_iff;
                     split;apply binding_finite_spec,is_binding_finite_filter_binding;assumption.
                ** split;[exists u1,u2;tauto|].
                   apply filter_binding_lang in I1 as (I1&<-);[|assumption].
                   apply filter_binding_lang in I2 as (I2&<-);[|assumption].
                   simpl_binding;reflexivity.
          -- intro Eq;apply KA_αKA in Eq as ->;rewrite left_absorbing;apply zero_minimal.
          -- apply test0_spec;
               case_eq (test0(filter_binding a b1(filter_binding a c1(δ1 a e)
                                                                 ·filter_binding a c2(e ⋆))));
               [reflexivity|].
             intros Iu;apply test0_false in Iu as (u&Iu).
             apply filter_binding_lang in Iu as ((u1&u2&->&I1&I2)&E1).
             ++ subst.
                apply filter_binding_lang in I1 as (I1&<-);[|assumption].
                apply filter_binding_lang in I2 as (I2&<-);[|assumption].
                exfalso;apply N;simpl_binding;reflexivity.
             ++ apply binding_finite_spec;simpl;apply orb_true_intro;right;apply andb_true_iff;split;
                  apply binding_finite_spec,is_binding_finite_filter_binding;assumption.
      + assert (eq : e · f <=α e) by apply Eq;clear Eq.
        assert (ih :  δ1 a (e · f) <=α  δ1 a e) by (apply IHEq,Bf);clear IHEq.
        cut (δ1 a (e·f⋆) <=α δ1 a e);[intro h;apply h|].
        assert (e1 : e·f⋆ <=α e) by (apply ka_star_right_ind,eq).
        assert (Bf' : is_binding_finite (δ1 a e)) by (apply is_binding_finite_δ1,Bf).
        assert (δ1 a (e · f⋆)=KA zero \/ (is_binding_finite f /\ is_binding_finite (f⋆)))
          as [E|(Be1&Be2)];[|apply KA_αKA in E as ->;apply zero_minimal|].
        * cut (is_binding_finite (e·f⋆)).
          -- intro B;cut (e =KA zero \/ is_binding_finite f /\ is_binding_finite (f ⋆)).
             ++ intros [E|E];[left|right;assumption].
                apply test0_spec;apply test0_spec in E.
                apply test0_δ1;simpl;rewrite E;reflexivity.
             ++ revert B.
                repeat rewrite <- binding_finite_spec;simpl.
                repeat rewrite andb_true_iff||rewrite orb_true_iff||rewrite test0_spec.
                replace e_zero with zero by reflexivity.
                intuition.
          -- destruct Bf as (B&h);exists B;apply αKA_lang_inf in e1;clear ih Bf' eq.
             intros b u Iu.
             cut (cl_α ⟦e⟧ u);[|apply e1;exists u;split;[assumption|reflexivity]].
             intros (v&Iv&Ev).
             rewrite <- (αequiv_binding Ev);apply h,Iv.
        * assert (Be3 : is_binding_finite (δ1 a f)) by apply is_binding_finite_δ1,Be1;simpl.
          transitivity (Σ (map (fun p => filter_binding a(fst p)(δ1 a e)·filter_binding a (snd p) (f ⋆)) 
                               (range (δ1 a e) (f ⋆)))).
          -- apply inf_join_inf;[|reflexivity].
             destruct (ϵ_zero_or_un e) as [E0| ->];
               [|replace e_zero with zero by reflexivity;rewrite left_absorbing;apply zero_minimal].
             rewrite E0;replace e_un with un by reflexivity;rewrite left_unit.
             assert (e2 : δ1 a f <=α δ1 a e)
               by (rewrite <- ih;simpl;rewrite E0;replace e_un with un by reflexivity;
                   rewrite left_unit; apply inf_cup_left).
             apply Σ_bounded;intros g Ig.
             apply in_map_iff in Ig as ((b1,b2)&<-&Ib).
             simpl.
             rewrite (filter_binding_αKA_inf _ _ Bf') by assumption.
             case_eq (test0 (filter_binding a b1 (δ1 a e) · filter_binding a b2 (f⋆))).
             ++ intro T;apply test0_spec,KA_αKA in T as ->.
                transitivity zero;[reflexivity|apply zero_minimal].
             ++ intro Iu;apply test0_false in Iu as (?&u1&u2&->&I1&I2).
                apply Σ_bigger,in_map_iff.
                exists (b1,b2);split;[reflexivity|].
                apply filter_binding_lang in I1 as (I1&<-);[|assumption].
                apply filter_binding_lang in I2 as (I2&<-);[|assumption].
                apply range_In;try assumption.
                unfold close_balanced;rewrite 𝗙_app.
                eapply range_result,Ib.
          -- apply Σ_bounded;intros g Ig.
             apply in_map_iff in Ig as ((b1&b2)&<-&Ib);simpl.
             case_eq (is_square b2);intro Sq.
             ++ transitivity (filter_binding a b1 (δ1 a e)·Σ (map (fun α => filter_binding a α f)
                                                                  (lower_squares b2))⋆).
                ** apply proper_prod_inf;[reflexivity|].
                   Transparent filter_binding.
                   simpl;rewrite Sq;unfold_eqX;simpl.
                   --- replace (lower_squares ε) with [ε] by reflexivity.
                       simpl;rewrite right_unit;reflexivity.
                   --- cut (filter_binding a b2 f
                            <=α Σ (map (fun α => filter_binding a α f) (lower_squares b2)) ⋆ ).
                       +++ intros ->;rewrite ka_star_dup,ka_star_dup;reflexivity.
                       +++ rewrite <- star_incr.
                           apply Σ_bigger,in_map_iff;exists b2;split;[reflexivity|].
                           unfold is_square in Sq;rewrite eqX_correct in Sq.
                           apply (lower_squares_spec _ Sq);split;[assumption|].
                           rewrite <- (prod_binding_maxBind Sq Sq).
                           apply maxBind_idem.
                           Opaque filter_binding.
                ** transitivity ((filter_binding a b1 (δ1 a e))
                                   ∪ filter_binding a ((0,true),c_binding b1) (δ1 a e));
                     [|apply inf_join_inf;apply KA_αKA_inf,filter_binding_inf,Bf'].
                   etransitivity;[apply proper_prod_inf;[apply inf_cup_left|reflexivity]
                                 |apply ka_star_right_ind].
                   rewrite (semiring_right_distr _ _ _),Σ_distr_l,Σ_distr_l.
                   cut (forall b', b' ∈ lower_squares b2 -> (b1 ⋅ b' = b1
                                                       \/ b1 ⋅ b' = (0, true, c_binding b1))
                                                      /\ (0, true, c_binding b1)⋅b' = (0, true, c_binding b1)).
                   --- intros hyp.                                  
                       repeat rewrite map_map;apply inf_join_inf;apply Σ_bounded;intros g Ig;
                         apply in_map_iff in Ig as (b'&<-&Ib').
                       +++ destruct (hyp b' Ib') as ([Eq|Eq]&_).
                           *** etransitivity;[|apply inf_cup_left].
                               transitivity
                                 (filter_binding a b1 (filter_binding a b1 (δ1 a e)
                                                                      ·filter_binding a b' f)).
                               ---- apply KA_αKA_inf,CompletenessKA_inf.
                                    intros u (u1&u2&->&I1&I2).
                                    apply filter_binding_lang.
                                    ++++ apply binding_finite_spec;simpl;apply orb_true_intro;right.
                                         apply andb_true_iff;split.
                                         **** apply binding_finite_spec,
                                              is_binding_finite_filter_binding;assumption.
                                         **** apply binding_finite_spec,
                                              is_binding_finite_filter_binding;assumption.
                                    ++++ split;[exists u1,u2;tauto|].
                                         simpl_binding.
                                         apply filter_binding_lang in I1 as (I1&->);[|assumption].
                                         apply filter_binding_lang in I2 as (I2&->);[|assumption].
                                         assumption.
                               ---- apply filter_binding_αKA_inf;[assumption|].
                                    etransitivity;[|apply ih].
                                    simpl;etransitivity;[|apply inf_cup_right].
                                    case_eq (test0 (filter_binding a b1 (δ1 a e)
                                                                   · filter_binding a b' f)).
                                    ++++ intro T;apply test0_spec,KA_αKA in T as ->.
                                         transitivity zero;[reflexivity|apply zero_minimal].
                                    ++++ intro Iu;apply test0_false in Iu as (?&u1&u2&->&I1&I2).
                                         apply Σ_bigger,in_map_iff.
                                         exists (b1,b');split;[reflexivity|].
                                         apply filter_binding_lang in I1 as (I1&<-);[|assumption].
                                         apply filter_binding_lang in I2 as (I2&<-);[|assumption].
                                         apply range_In;try assumption.
                                         unfold close_balanced;rewrite 𝗙_app,Eq.
                                         apply range_result in Ib.
                                         simpl_binding in Ib;lia.
                           *** etransitivity;[|apply inf_cup_right].
                               transitivity
                                 (filter_binding a (0, true, c_binding b1)
                                                 (filter_binding a b1 (δ1 a e)
                                                                 ·filter_binding a b' f)).
                               ---- apply KA_αKA_inf,CompletenessKA_inf.
                                    intros u (u1&u2&->&I1&I2).
                                    apply filter_binding_lang.
                                    ++++ apply binding_finite_spec;simpl;apply orb_true_intro;right.
                                         apply andb_true_iff;split.
                                         **** apply binding_finite_spec,
                                              is_binding_finite_filter_binding;assumption.
                                         **** apply binding_finite_spec,
                                              is_binding_finite_filter_binding;assumption.
                                    ++++ split;[exists u1,u2;tauto|].
                                         simpl_binding.
                                         apply filter_binding_lang in I1 as (I1&->);[|assumption].
                                         apply filter_binding_lang in I2 as (I2&->);[|assumption].
                                         assumption.
                               ---- apply filter_binding_αKA_inf;[assumption|].
                                    etransitivity;[|apply ih].
                                    simpl;etransitivity;[|apply inf_cup_right].
                                    case_eq (test0 (filter_binding a b1 (δ1 a e)
                                                                   · filter_binding a b' f)).
                                    ++++ intro T;apply test0_spec,KA_αKA in T as ->.
                                         transitivity zero;[reflexivity|apply zero_minimal].
                                    ++++ intro Iu;apply test0_false in Iu as (?&u1&u2&->&I1&I2).
                                         apply Σ_bigger,in_map_iff.
                                         exists (b1,b');split;[reflexivity|].
                                         apply filter_binding_lang in I1 as (I1&<-);[|assumption].
                                         apply filter_binding_lang in I2 as (I2&<-);[|assumption].
                                         apply range_In;try assumption.
                                         unfold close_balanced;rewrite 𝗙_app,Eq;reflexivity.
                       +++ pose proof (hyp _ Ib') as (_&Eq).
                           etransitivity;[|apply inf_cup_right].
                           transitivity
                             (filter_binding a (0, true, c_binding b1)
                                             (filter_binding a (0, true, c_binding b1) (δ1 a e)
                                                             ·filter_binding a b' f)).
                           ---- apply KA_αKA_inf,CompletenessKA_inf.
                                intros u (u1&u2&->&I1&I2).
                                apply filter_binding_lang.
                                ++++ apply binding_finite_spec;simpl;apply orb_true_intro;right.
                                     apply andb_true_iff;split.
                                     **** apply binding_finite_spec,
                                          is_binding_finite_filter_binding;assumption.
                                     **** apply binding_finite_spec,
                                          is_binding_finite_filter_binding;assumption.
                                ++++ split;[exists u1,u2;tauto|].
                                     simpl_binding.
                                     apply filter_binding_lang in I1 as (I1&->);[|assumption].
                                     apply filter_binding_lang in I2 as (I2&->);[|assumption].
                                     assumption.
                           ---- apply filter_binding_αKA_inf;[assumption|].
                                etransitivity;[|apply ih].
                                simpl;etransitivity;[|apply inf_cup_right].
                                case_eq (test0 (filter_binding a (0, true, c_binding b1) (δ1 a e)
                                                               · filter_binding a b' f)).
                                ++++ intro T;apply test0_spec,KA_αKA in T as ->.
                                     transitivity zero;[reflexivity|apply zero_minimal].
                                ++++ intro Iu;apply test0_false in Iu as (?&u1&u2&->&I1&I2).
                                     apply Σ_bigger,in_map_iff.
                                     exists ((0, true, c_binding b1),b');split;[reflexivity|].
                                     apply filter_binding_lang in I1 as (I1&E1);[|assumption].
                                     apply filter_binding_lang in I2 as (I2&E2);[|assumption].
                                     rewrite <- E1,<-E2;apply range_In;try assumption.
                                     unfold close_balanced;rewrite 𝗙_app,E1,E2,Eq.
                                     reflexivity.
                   --- apply range_result in Ib;revert Ib Sq;clear.
                       simpl_binding;intros E.
                       unfold is_square;rewrite eqX_correct.
                       intros Sq b' Ib'.
                       apply (lower_squares_spec _ Sq) in Ib' as (Sq'&E').
                       destruct b2 as ((x,x'),x''),b' as ((y,y'),y''),b1 as ((z,z'),z'');
                         unfold square,d_binding,prod_binding in *;simpl in *;subst.
                       replace z with 0 in * by lia.
                       revert E'.
                       destruct_ltb z'' x;[|lia].
                       destruct_ltb x z'';[replace z'' with x in * by lia|].
                       +++ simpl_nat.
                           destruct_ltb y x;[destruct_ltb x y;[replace y with x in * by lia|]|];
                             intro heq;inversion heq;subst.
                           *** split;[|reflexivity].
                               destruct y';simpl in *.
                               ---- rewrite orb_true_r;tauto.
                               ---- rewrite orb_false_r;tauto.
                           *** lia.
                           *** destruct_ltb x y;[|lia];tauto.
                       +++ simpl_nat.
                           destruct_ltb y x;[destruct_ltb x y;[replace y with x in * by lia|]|];
                             intro heq;inversion heq;subst.
                           *** destruct_ltb z'' x;[|lia].
                               destruct_ltb x z'';[lia|].
                               tauto.
                           *** lia.
                           *** destruct_ltb z'' y;[|lia].
                               destruct_ltb y z'';[lia|].
                               tauto.
             ++ case_eq (test0 (filter_binding a b1 (δ1 a e) · filter_binding a b2 (f⋆))).
                ** intro T;apply test0_spec,KA_αKA in T as ->.
                   transitivity zero;[reflexivity|apply zero_minimal].
                ** intro Iu;apply test0_false in Iu as (?&u1&u2&->&I1&I2).
                   exfalso.
                   apply filter_binding_lang in I2 as (I2&<-);[|assumption].
                   apply eqX_false in Sq;apply Sq.
                   apply binding_finite_sqExpr_star in Be2 as (h1&h2).
                   apply (h2 a),is_binding_finite_bindings;assumption.
  Qed.
  
  Lemma δ1_αKA_inf a e f :
    is_binding_finite f -> e <=α f -> δ1 a e <=α δ1 a f.
  Proof. unfold ax_inf;intros Bf E;rewrite <- (@δ1_αKA a (e∪f) f Bf E) at 2;reflexivity. Qed.
           
  Lemma δ1_δ a e : is_binding_finite e -> δ1 a e <=KA δ (open a) e.
  Proof.
    intro Be;induction_bin_fin e Be;simpl.
    - reflexivity.
    - reflexivity.
    - replace eq_letter with tools.eqX by reflexivity.
      destruct x as [b|b|x];[destruct_eqX a b;[simpl_eqX;reflexivity|]| |];apply zero_minimal.
    - rewrite IHe1,IHe2;reflexivity.
    - destruct (ϵ_zero_or_un e1) as [-> | ->];
        [replace e_un with un by reflexivity|replace e_zero with zero by reflexivity];simpl_eqX.
      + rewrite (ax_eq_ax _ (KA_un_left _)).
        apply inf_join_inf;etransitivity;[|apply inf_cup_right| |apply inf_cup_left].
        * assumption.
        * apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as ((b1&b2)&<-&_);simpl.
          rewrite (filter_binding_inf _ _ (is_binding_finite_δ1 _ B1)), (filter_binding_inf _ _ B2).
          rewrite IHe1;reflexivity.
      + rewrite (ax_eq_ax _ (KA_left_zero _)),(ax_eq_ax _ (KA_zero _)).
        apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as ((b1&b2)&<-&_);simpl.
        rewrite (filter_binding_inf _ _ (is_binding_finite_δ1 _ B1)), (filter_binding_inf _ _ B2).
        rewrite IHe1;reflexivity.
    - apply orb_true_iff in T as [T|T].
      + pose proof T as E;apply test0_ϵ,test0_spec in E.
        replace e_zero with zero in E by reflexivity.
        rewrite E at 1;rewrite (ax_eq_ax _ (KA_left_zero _)),(ax_eq_ax _ (KA_zero _)).
        apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as ((?&?)&<-&_);simpl.
        eapply test0_δ1,filter_binding_test0,test0_spec in T as ->.
        replace e_zero with zero by reflexivity.
        rewrite (ax_eq_ax _ (KA_left_zero _)).
        apply zero_minimal.
      + pose proof T as E; eapply test0_δ1,test0_spec in E as ->.
        replace e_zero with zero by reflexivity.
        rewrite (ax_eq_ax _ (KA_right_zero _)),(ax_eq_ax _ (KA_zero _)).
        apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as ((?&?)&<-&_);simpl.
        eapply filter_binding_test0,test0_spec in T as ->.
        replace e_zero with zero by reflexivity.
        rewrite (ax_eq_ax _ (KA_right_zero _)).
        apply zero_minimal.
    - apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as ((?&?)&<-&_);simpl.
      repeat rewrite filter_binding_inf.
      + rewrite IHe;reflexivity.
      + apply sqExpr_bindings_finite_star,Sq.
      + apply is_binding_finite_δ1,Sq.
  Qed.

  Lemma δ1_alt a e : 
    is_binding_finite e ->
    δ1 a e =KA Σ (map (fun β => filter_binding a β (δ (open a) e))
                                       ((fun β : 𝖡 => d_binding β =?= 0) :> bindings (δ (open a) e) a)).
  Proof.
    intros Be;apply CompletenessKA.
    rewrite δ1_lang by assumption.
    intros u;rewrite δ_lang;split.
    - intros (Iu&Lu).
      apply Σ_lang;exists (filter_binding a (𝗙 a u) (δ (open a) e)).
      split.
      + apply in_map_iff;exists (𝗙 a u);split;[reflexivity|].
        simpl_In;split.
        * apply is_binding_finite_bindings;[|assumption].
          apply δ_binFin,Be.
        * rewrite Lu;simpl_eqX;reflexivity.
      + apply filter_binding_lang;[apply δ_binFin,Be|tauto].
    - intros Iu;apply Σ_lang in Iu as (f&If&Iu).
      apply in_map_iff in If as (β&<-&Iβ).
      simpl_In in Iβ;destruct Iβ as (Iβ&Eu).
      rewrite eqX_correct in Eu.
      apply filter_binding_lang in Iu as (Iu&<-);[|apply δ_binFin,Be].
      tauto.
  Qed.

  Lemma support_δ1 a e : ⌊δ1 a e⌋ ⊆ ⌊e⌋.
  Proof.
    induction e;simpl;repeat rewrite support_join||rewrite support_prod||rewrite support_star.
    - reflexivity.
    - reflexivity.
    - replace e_add with join by reflexivity;rewrite support_join,IHe1,IHe2;reflexivity.
    - replace (e_prod e1 e2) with (prod e1 e2) by reflexivity;rewrite support_prod,support_ϵ;simpl.
      intro b;simpl_In;intros [I|I];[right;apply IHe2,I|].
      rewrite <- Σ_support,In_support_list in I.
      destruct I as (f&If&Ib).
      apply in_map_iff in If as ((?&?)&<-&_).
      rewrite support_prod,filter_binding_support,filter_binding_support,IHe1 in Ib.
      simpl_In in Ib;tauto.
    - intro b;simpl_In;intro I.
      rewrite <- Σ_support,In_support_list in I.
      destruct I as (f&If&Ib).
      apply in_map_iff in If as ((?&?)&<-&_).
      rewrite support_prod,filter_binding_support,filter_binding_support,IHe in Ib.
      simpl_In in Ib;tauto.
    - destruct x;unfold_eqX;apply incl_nil.
  Qed.

  Require Import strict_split.
  Definition δ3 c e := Σ (map (fun a => (splitActStrict c a 0 (δ (open a) e))) ⌊e⌋).

  Lemma δ3_test0 c e : test0 e = true -> δ3 c e =KA zero.
  Proof.
    intro T;unfold δ3.
    transitivity (Σ (map (fun a => zero) ⌊ e ⌋)).
    - f_equal.
      apply Σ_map_equiv;intros a _.
      apply test0_spec,splitActStrict_test0,test0_δ,T.
    - induction ⌊e⌋ as [|a l];[reflexivity|].
      simpl;rewrite IHl;apply left_unit.
  Qed.

  Lemma δ3_is_binding_finite c e : is_binding_finite e -> is_binding_finite (δ3 c e).
  Proof.
    intro Be;apply is_binding_finite_Σ;intros g Ig.
    apply in_map_iff in Ig as (a&<-&Ia).
    apply is_binding_finite_splitActStrict,δ_binFin,Be. 
  Qed.

  Lemma δ3_lang c e :
    is_binding_finite e ->
    ⟦δ3 c e⟧ ≃ (fun u => exists u1 u2 a, u =[(a,c)]∙u1++u2 /\ 𝗙 a u1 = (1,false,0) /\ ⟦e⟧ (open a::u1++u2)
               /\  (forall v w, u1 = v ++ w -> ⎢ v ⎥ < ⎢ u1 ⎥ -> 𝗙 a v <> ((1, false, 0) : 𝖡))).
  Proof.
    unfold δ3;intros Be u;rewrite Σ_lang;split.
    - intros (g&Ig&Iu).
      apply in_map_iff in Ig as (a&<-&Ia).
      apply splitActStrict_lang in Iu as (u1&u2&->&Iu&N&Min);[|apply δ_binFin,Be].
      apply δ_lang in Iu.
      exists u1,u2,a;tauto.
    - intros (u1&u2&a&->&F&Iu&Min).
      apply δ_lang in Iu.
      exists (splitActStrict c a 0 (δ(open a) e));split.
      + apply in_map_iff;exists a;split;[reflexivity|].
        apply δ_lang in Iu.
        apply support_lang in Iu as <-.
        simpl;rewrite support_list_cons;simpl_In.
        left;left;reflexivity.
      + apply splitActStrict_lang;[apply δ_binFin,Be|].
        exists u1,u2;repeat split;try assumption.
  Qed.

  Lemma δ3_KA c e f :
    is_binding_finite f -> e =KA f -> δ3 c e =KA δ3 c f.
  Proof.
    intros Bf E.
    pose proof Bf as Be;apply (is_binding_finite_ax_eq (KA_αKA E)) in Be.
    apply soundness in E;apply CompletenessKA.
    rewrite (δ3_lang c Be),(δ3_lang c Bf).
    intros u;split;intros (u1&u2&a&Eu&F&Iu&Min);apply E in Iu;exists u1,u2,a;tauto.
  Qed.
  
  Lemma δ3_join c e f : δ3 c (e∪f) =KA δ3 c e ∪ δ3 c f.
  Proof.
    unfold δ3;simpl.
    unfold support at 1;simpl.
    replace supReg with support by reflexivity.
    rewrite map_app.
    etransitivity;[symmetry;apply algebra.Σ_app|].
    apply ax_inf_PartialOrder;unfold Basics.flip;split;apply inf_join_inf;
      apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as (a&<-&Ia);simpl in *;simpl_In in *.
    - apply inf_join_inf.
      + etransitivity;[|apply inf_cup_left].
        apply Σ_bigger,in_map_iff;exists a;tauto.
      + case_in a ⌊f⌋.
        * etransitivity;[|apply inf_cup_right].
          apply Σ_bigger,in_map_iff;exists a;tauto.
        * etransitivity;[|apply zero_minimal].
          apply ax_eq_inf,test0_spec,splitActStrict_test0.
          apply not_false_is_true;intros Iu;apply I.
          apply test0_false in Iu as (u&Iu);apply δ_lang,support_lang in Iu as <-.
          apply support_list_cons;simpl_In;left;left;reflexivity.
    - apply inf_join_inf.
      + case_in a ⌊e⌋.
        * etransitivity;[|apply inf_cup_left].
          apply Σ_bigger,in_map_iff;exists a;tauto.
        * etransitivity;[|apply zero_minimal].
          apply ax_eq_inf,test0_spec,splitActStrict_test0.
          apply not_false_is_true;intros Iu;apply I.
          apply test0_false in Iu as (u&Iu);apply δ_lang,support_lang in Iu as <-.
          apply support_list_cons;simpl_In;left;left;reflexivity.
      + etransitivity;[|apply inf_cup_right].
        apply Σ_bigger,in_map_iff;exists a;tauto.
    - etransitivity;[|apply inf_cup_left].
      etransitivity;[apply inf_cup_left|].
      apply Σ_bigger,in_map_iff;exists a;split;[reflexivity|assumption].
    - etransitivity;[|apply inf_cup_right].
      etransitivity;[apply inf_cup_right|].
      apply Σ_bigger,in_map_iff;exists a;split;[reflexivity|assumption].
  Qed.

  Ltac non_zero e :=
    let T:=fresh "T" in
    case_eq (test0 e);intro T;
    [etransitivity;[|apply zero_minimal];
     try apply KA_αKA_inf;
     apply ax_eq_inf,test0_spec;
     repeat (simpl;rewrite T||rewrite test0_act||rewrite orb_true_r);
     try reflexivity|].

  Lemma δ3_prod c e f :
    is_binding_finite (e·f) -> c # (e·f) ->
    δ3 c (e·f) =α δ3 c e · f 
                   ∪ ϵ e · δ3 c f
                   ∪ Σ (flat_map (fun a => map (fun B =>
                                               [(a,c)]∙filter_binding a (fst B) (δ1 a e)
                                                      ·splitActStrict c a (snd B) f)
                                       (SplitRange 0 (sizeExpr (δ1 a e))))
                                 ⌊e⌋).
  Proof.
    intros Bef Fc;pose proof Bef as B.
    case_eq (test0 (e·f)).
    - intro T.
      apply KA_αKA.
      pose proof T as T'.
      eapply δ3_test0 in T' as ->.
      simpl in T.
      apply ax_inf_PartialOrder;unfold Basics.flip;split;[apply zero_minimal|].
      repeat rewrite (ax_eq_ax _ (KA_left_distr _ _ _)).
      repeat apply inf_join_inf.
      + apply orb_true_iff in T as [T|T].
        * eapply δ3_test0 in T as ->.
          etransitivity;[apply ax_eq_inf,left_absorbing|reflexivity].
        * eapply test0_spec in T as ->.
          replace e_zero with zero by reflexivity.
          etransitivity;[apply ax_eq_inf,right_absorbing|reflexivity].
      + apply orb_true_iff in T as [T|T].
        * apply test0_ϵ,test0_spec in T as ->.
          replace e_zero with zero by reflexivity.
          etransitivity;[apply ax_eq_inf,left_absorbing|reflexivity].
        * eapply δ3_test0 in T as ->.
          etransitivity;[apply ax_eq_inf,right_absorbing|reflexivity].
      + apply Σ_bounded;intros g Ig;apply in_flat_map in Ig as (a&Ia&Ig).
        apply in_map_iff in Ig as ((β1&β2)&<-&Iβ);simpl.
        apply ax_eq_inf,test0_spec;simpl.
        rewrite test0_act.
        apply orb_true_iff in T as [T|T].
        * eapply test0_δ1,filter_binding_test0 in T as ->;reflexivity.
        * rewrite splitActStrict_test0 by assumption.
          apply orb_true_r.
    - simpl;intro T;apply orb_false_iff in T as (Te&Tf).
      apply binding_finite_spec in Bef;simpl in Bef.
      rewrite Te,Tf in Bef;simpl in Bef.
      apply andb_true_iff in Bef as (Be&Bf);rewrite binding_finite_spec in Be,Bf.
      unfold δ3;simpl.
      apply ax_inf_PartialOrder;unfold Basics.flip;split;
        repeat apply inf_join_inf.
      + apply Σ_bounded;intros g Ig.
        apply in_map_iff in Ig as (a&<-&Ia).
        transitivity (splitActStrict c a 0 (δ (open a) e · f)
                                     ∪ ϵ e · splitActStrict c a 0 (δ (open a) f)).
        * destruct (ϵ_zero_or_un e) as [-> | ->];simpl_eqX;simpl;simpl_In.
          -- replace e_un with un by reflexivity.
             destruct (_||_);repeat rewrite left_unit;reflexivity.
          -- replace (prod e_zero) with (prod zero) by reflexivity.
             destruct (_||_);repeat rewrite left_unit||rewrite left_absorbing||rewrite right_unit;reflexivity.
        * simpl.
          rewrite Tf,orb_false_r.
          apply inf_join_inf;[case_eq (test0(δ(open a) e));[intros _;apply zero_minimal
                                                           |intro Te';apply inf_join_inf]|].
          -- etransitivity;[|apply inf_cup_left].
             etransitivity;[|apply inf_cup_left].
             apply proper_prod_inf;[|reflexivity].
             apply Σ_bigger,in_map_iff;exists a;split;[reflexivity|].
             apply test0_false in Te' as (u&Iu).
             apply δ_lang,support_lang in Iu.
             rewrite <- Iu,support_list_cons;left;reflexivity.
          -- etransitivity;[|apply inf_cup_right].
             apply Σ_bounded;intros g Ig.
             apply in_map_iff in Ig as ((β&N)&<-&I).
             apply SplitRange_result in I as (Eβ&Min);simpl.
             pose proof Eβ as h.
             apply destr_bind_prod_full in h as (_&h).
             replace (d_binding (S N,false,0)) with (S N) in * by reflexivity.
             destruct h as [(L&E')| ->];[|exfalso;apply (Min (0,false,S N));reflexivity].
             transitivity ([(a, c)] ∙ filter_binding a β (δ1 a e) · splitActStrict c a N f).
             ++ apply proper_prod_inf;[|reflexivity].
                apply αKA_inf_act.
                apply KA_αKA_inf,CompletenessKA_inf.
                intros u Iu;apply filter_binding_lang in Iu as (Iu&Eu);[|apply δ_binFin,Be].
                apply filter_binding_lang;[apply is_binding_finite_δ1,Be|].
                split;[|assumption].
                apply δ1_lang;[assumption|split].
                ** apply δ_lang,Iu.
                ** unfold close_balanced.
                   rewrite Eu;clear Iu Eu u.
                   lia.
             ++ non_zero (filter_binding a β (δ1 a e)).
                apply Σ_bigger,in_flat_map;exists a;split.
                ** apply test0_false in Te' as (u&Iu).
                   apply δ_lang,support_lang in Iu.
                   rewrite <- Iu,support_list_cons;left;reflexivity.
                ** apply in_map_iff;exists (β,N);split;[reflexivity|].
                   apply SplitRange_In';try assumption.
                   apply test0_false in T as (u&Iu).
                   apply filter_binding_lang in Iu as (Iu&<-);[|apply is_binding_finite_δ1,Be].
                   apply binding_finite_bound_size,Iu.
                   apply is_binding_finite_δ1,Be.
          -- etransitivity;[|apply inf_cup_left].
             etransitivity;[|apply inf_cup_right].
             apply proper_prod_inf;[reflexivity|].
             non_zero (splitActStrict c a 0 (δ (open a) f)).
             apply Σ_bigger,in_map_iff;exists a;split;[reflexivity|].
             apply test0_false in T as (u&Iu).
             apply splitActStrict_lang in Iu as (?&?&_&Iu&_);[|apply δ_binFin,Bf].
             apply δ_lang,support_lang in Iu.
             rewrite <- Iu,support_list_cons;left;reflexivity.
      + rewrite Σ_distr_r;apply Σ_bounded;rewrite map_map; intros g Ig.
        apply in_map_iff in Ig as (a&<-&Ia).
        etransitivity;[|apply Σ_bigger,in_map_iff;exists a;split;[reflexivity|]].
        * destruct (ϵ_zero_or_un e) as [-> | ->];simpl_eqX;simpl;rewrite Tf,orb_false_r.
          -- case_eq (test0 (δ (open a) e)).
             ++ intro T.
                etransitivity;[|apply inf_cup_left].
                apply ax_eq_inf,KA_αKA,test0_spec;simpl in *.
                apply orb_true_iff;left.
                apply splitActStrict_test0,T.
             ++ intros _;etransitivity;[|apply inf_cup_left].
                apply inf_cup_left.
          -- case_eq (test0 (δ (open a) e)).
             ++ intro T.
                apply ax_eq_inf,KA_αKA,test0_spec;simpl in *.
                apply orb_true_iff;left.
                apply splitActStrict_test0,T.
             ++ intros _;apply inf_cup_left.
        * rewrite support_prod;simpl_In;tauto.
      + destruct (ϵ_zero_or_un e) as [-> | ->];simpl_eqX.
        * replace e_un with un by reflexivity.
          rewrite left_unit.
          apply Σ_bounded; intros g Ig.
          apply in_map_iff in Ig as (a&<-&Ia).
          simpl.
          etransitivity;[apply inf_cup_right|].
          apply Σ_bigger,in_map_iff;exists a;split;[reflexivity|].
          rewrite support_prod;simpl_In;tauto.
        * etransitivity;[|apply zero_minimal].
          apply ax_eq_inf,KA_αKA,test0_spec;reflexivity.
      + apply Σ_bounded; intros g Ig.
        apply in_flat_map in Ig as (a&Ia&Ig).
        apply in_map_iff in Ig as ((β&N)&<-&Iβ);simpl in *.
        apply SplitRange_result in Iβ as (Eβ&Min);simpl.
        pose proof Eβ as h.
        apply destr_bind_prod_full in h as (_&h).
        replace (d_binding (S N,false,0)) with (S N) in * by reflexivity.
        destruct h as [(L&E')| ->];[|exfalso;apply (Min (0,false,S N));reflexivity].
        transitivity (splitActStrict c a 0 (δ (open a) e · f)).
        * simpl.
          rewrite Tf,orb_false_r.
          non_zero (filter_binding a β (δ1 a e)).
          case_eq (test0 (δ (open a) e)).
          -- intro T';exfalso.
             apply test0_spec,soundness in T'.
             apply test0_false in T as (u&Iu).
             apply filter_binding_lang in Iu as (Iu&_);[|apply is_binding_finite_δ1,Be].
             apply δ1_lang in Iu as (Iu&_);[|assumption].
             apply δ_lang,T' in Iu;apply Iu.
          -- intros _.
             etransitivity;[|apply inf_cup_right].
             etransitivity;[|apply Σ_bigger,in_map_iff;exists (β,N);split;[reflexivity|]].
             ++ simpl;apply proper_prod_inf;[|reflexivity].
                apply αKA_inf_act,filter_binding_αKA_inf,KA_αKA_inf,δ1_δ,Be.
                apply δ_binFin,Be.
             ++ apply test0_false in T as (u&Iu).
                apply filter_binding_lang in Iu as (Iu&<-);[|apply is_binding_finite_δ1,Be].
                apply δ1_lang in Iu as (Iu&_);[|assumption].
                apply δ_lang in Iu.
                apply SplitRange_In';try tauto.
                apply binding_finite_bound_size;try tauto.
                apply δ_binFin,Be.
        * etransitivity;[|apply Σ_bigger,in_map_iff;exists a;split;[reflexivity|]].
          -- destruct (ϵ_zero_or_un e) as [-> | ->];simpl_eqX;[|reflexivity].
             apply inf_cup_left.
          -- rewrite support_prod;simpl_In;tauto.
  Qed.

  Lemma δ3_star c e : is_binding_finite (e⋆) -> c # e -> δ3 c (e⋆) =α δ3 c e · e⋆.
  Proof.
    intros Bs Fc;unfold δ3;simpl.
    rewrite Σ_distr_r,map_map,support_star.
    apply Σ_map_equiv_α.
    intros a Ia.
    case_eq (test0 (δ (open a) e)).
    - intro T;simpl.
      symmetry;apply KA_αKA,test0_spec;simpl.
      rewrite splitActStrict_test0 by (simpl;rewrite T;reflexivity);reflexivity.
    - intro T;simpl.
      apply ax_inf_PartialOrder;unfold Basics.flip;split;[|apply inf_cup_left].
      apply inf_join_inf;[reflexivity|].
      apply Σ_bounded;intros f If.
      apply in_map_iff in If as ((β&N)&<-&Iβ).
      apply SplitRange_result in Iβ as (Eβ&Min);simpl.
      pose proof Eβ as h.
      apply destr_bind_prod_full in h as (_&h).
      replace (d_binding (S N,false,0)) with (S N) in * by reflexivity.
      destruct h as [(L&E')| ->];[|exfalso;apply (Min (0,false,S N));reflexivity].
      non_zero (filter_binding a β (δ (open a) e));exfalso.
      apply test0_false in T0 as (u&Iu).
      pose proof Bs as Be.
      rewrite <- binding_finite_spec in Be;simpl in Be;apply andb_true_iff in Be as (Be&Sq).
      apply binding_finite_spec in Be.
      apply filter_binding_lang in Iu as (Iu&Eu);[|apply δ_binFin,Be].
      apply δ_lang,(is_binding_finite_bindings Be a) in Iu;revert Iu;simpl_binding;simpl_eqX;
        rewrite Eu;intros Iu.
      rewrite forallb_forall in Sq;pose proof (Sq _ Ia) as Sq';clear Sq.
      rewrite forallb_forall in Sq';apply Sq' in Iu;clear Sq' u Eu.
      revert Iu;unfold is_square;simpl_binding.
      replace (d_binding β) with 0 in * by lia;simpl.
      rewrite PeanoNat.Nat.eqb_eq;lia.
  Qed.

  Lemma 𝗙_perm p (a:atom) (u:list letter) : 𝗙 a (p∙u) = 𝗙 (p∗∙a) u.
  Proof. apply 𝗙_perm. Qed.

  Lemma δ3_star_ind c e f : is_binding_finite (e⋆·f) -> c # (e·f) ->
                            δ3 c (e⋆·f) =α δ3 c e · e⋆·f ∪ δ3 c f.
  Proof.
    intros B Fc;pose proof B as Bp.
    apply binding_finite_spec in B;simpl in B;apply orb_true_iff in B as [T|B].
    - transitivity zero.
      + apply KA_αKA,δ3_test0.
        simpl;rewrite T;reflexivity.
      + rewrite (KA_αKA(δ3_test0 c T)).
        apply test0_spec,KA_αKA in T as ->.
        rewrite right_unit.
        symmetry;etransitivity;[|apply right_absorbing];reflexivity.
    - repeat rewrite andb_true_iff in B;destruct B as ((Be&Sq')&Bf).
      rewrite binding_finite_spec in Be,Bf.
      assert (Sq : is_binding_finite (e⋆))
        by (rewrite <- binding_finite_spec in *;simpl;rewrite Be,Sq';reflexivity);clear Sq'.
      rewrite δ3_prod by assumption.
      assert (c# e /\ c # f) as (Fe&Ff) by (revert Fc;rewrite support_prod;simpl_In;tauto).
      rewrite δ3_star by assumption.
      simpl.
      replace e_un with un by reflexivity.
      rewrite left_unit.
      apply ax_inf_PartialOrder;unfold Basics.flip;split.
      + apply inf_join_inf;[reflexivity|].
        etransitivity;[apply ax_eq_inf|apply zero_minimal].
        apply KA_αKA,test0_spec,not_false_is_true.
        intros Iu.
        apply test0_false in Iu as (u&Iu).
        apply Σ_lang in Iu as (g&Ig&Iu).
        apply in_flat_map in Ig as (a&Ia&Ig).
        apply in_map_iff in Ig as ((β&N)&<-&Iβ).
        apply SplitRange_result in Iβ as (Eβ&Min);simpl.
        pose proof Eβ as h.
        apply destr_bind_prod_full in h as (_&h).
        replace (d_binding (S N,false,0)) with (S N) in * by reflexivity.
        destruct h as [(L&E')| ->];[|exfalso;apply (Min (0,false,S N));reflexivity].
        destruct Iu as (?&w&->&Iu&Iw).
        rewrite filter_binding_act,Σ_act in Iu.
        simpl in *.
        apply filter_binding_lang in Iu as (Iu&Eu).
        * unfold act in Eu;simpl in Eu;revert Eu;simpl_eqX;intro.
          apply Σ_lang in Iu as (g&Ig&Iu).
          apply In_act_lists,in_map_iff in Ig as ((α1,α2)&Eg&Iα).
          apply (act_bij [(a,c)]) in Eg.
          rewrite act_p_pinv in Eg;subst.
          rewrite act_prod,filter_binding_act,filter_binding_act in Iu.
          revert Iu;unfold act at 1 3;simpl;simpl_eqX.
          intros (u1&u2&->&Iu1&Iu2).
          rewrite filter_binding_lang in Iu1,Iu2
            by (apply is_binding_finite_act;try apply is_binding_finite_δ1;assumption).
          destruct Iu1 as (Iu1&Eu1),Iu2 as (Iu2&Eu2).
          apply splitActStrict_lang in Iw as (u3&u4&->&Iw&Ew&Min');[|assumption].
          rewrite act_lang in Iu1,Iu2.
          apply δ1_lang in Iu1 as (Iu1&CB);[|assumption].
          assert (Iu1' : ⟦e⋆⟧(open a:: ([(a, c)] ∗) ∙ u1))
            by (exists 1,(open a:: ([(a, c)] ∗) ∙ u1),[];split;[symmetry;apply app_nil_r
                                                          |split;[assumption|reflexivity]]).
          apply (is_binding_finite_bindings Sq a),(binding_finite_sqExpr_star Sq) in Iu1'.
          apply (is_binding_finite_bindings Sq a),(binding_finite_sqExpr_star Sq) in Iu2.
          revert CB Iu2 Iu1';unfold close_balanced, square.
          destruct_eqX c a;[tauto|].
          simpl_binding;repeat rewrite 𝗙_perm.
          unfold act;simpl;simpl_eqX;rewrite Eu1,Eu2;intros CB;rewrite CB;lia.
        * apply is_binding_finite_Σ;intros g Ig.
          apply In_act_lists in Ig.
          apply in_map_iff in Ig as ((α1,α2)&Eg&Iα).
          apply (act_bij [(a,c)]) in Eg.
          rewrite act_p_pinv in Eg;subst.
          rewrite act_prod.
          apply binding_finite_spec;simpl;apply orb_true_iff;right.
          apply andb_true_iff;split;apply binding_finite_spec,is_binding_finite_act,
                                    is_binding_finite_filter_binding.
          -- apply is_binding_finite_δ1;assumption.
          -- assumption.
      + apply inf_cup_left.
  Qed.
  Opaque split_binding.
  
  Lemma δ3_KA_inf c e f :
    is_binding_finite f -> e <=KA f -> δ3 c e <=KA δ3 c f.
  Proof. unfold ax_inf;rewrite <- δ3_join;apply δ3_KA. Qed.

  Lemma δ3_act p c e : p ∙ δ3 c e =KA δ3 (p∙c) (p∙e).
  Proof.
    unfold δ3.
    rewrite Σ_act.
    apply algebra.Σ_equivalent.
    intros f;rewrite In_act_lists.
    setoid_rewrite in_map_iff.
    split. 
    - intros (a&Ef&Ia).
      apply (act_bij p) in Ef;rewrite act_p_pinv in Ef;subst.
      exists (p∗∗∙a);split.
      + rewrite inverse_inv;simpl.
        rewrite splitActStrict_act.
        f_equal.
        rewrite δ_act.
        unfold act at 2;simpl.
        rewrite act_pinv_p.
        reflexivity.
      + apply In_act_lists,support_action;rewrite act_pinv_p;assumption.
    - intros (a&<-&Ia).
      apply support_action,In_act_lists in Ia.
      exists (p∗∙a);split;[|assumption].
      rewrite splitActStrict_act.
      rewrite act_pinv_p;f_equal.
      rewrite δ_act,act_pinv_p;reflexivity.
  Qed.

      

  Lemma δ3_αKA c e f : is_binding_finite f -> c # e -> c # f -> e =α f -> δ3 c e =α δ3 c f.
  Proof.
    intros B2 F1 F2 eq.
    pose proof B2 as B1;apply (is_binding_finite_ax_eq eq) in B1.
    revert c F1 F2;induction eq;intros c F1 F2.
    - reflexivity.
    - symmetry;apply IHeq;assumption.
    - destruct (exists_fresh (⌊e⌋++⌊f⌋++⌊g⌋)) as (d&Id).
      assert (d # e /\ d # f /\ d # g) as (Fe&Ff&Fg) by (simpl_In in Id;tauto);clear Id.
      rewrite <- (act_pinv_p [(c,d)] (δ3 c e)).
      rewrite <- (act_pinv_p [(c,d)] (δ3 c g)).
      apply αKA_act.
      etransitivity;[apply KA_αKA,δ3_act|].
      etransitivity;[|symmetry;apply KA_αKA,δ3_act].
      replace ([(c,d)]∙e) with e;[replace ([(c,d)]∙g) with g|].
      + pose proof B1 as Bf;apply (is_binding_finite_ax_eq eq1) in Bf.
        etransitivity;[apply IHeq1|apply IHeq2];try (unfold act;simpl;simpl_eqX);assumption.
      + symmetry;apply elements_inv_act.
        intros a Ia [<-|[<-|F]];try tauto.
      + symmetry;apply elements_inv_act.
        intros a Ia [<-|[<-|F]];try tauto.
    - pose proof B1 as Be.
      apply binding_finite_spec in Be;simpl in Be.
      apply orb_true_iff in Be as [T|Be].
      + assert (E: test0 (e·e') = true) by apply T.
        transitivity zero.
        * apply KA_αKA, (δ3_test0 c E).
        * symmetry;apply KA_αKA,δ3_test0.
          erewrite test0_αKA;[apply E|].
          rewrite eq1,eq2;reflexivity.
      + apply andb_true_iff in Be as (Be&Be').
        rewrite binding_finite_spec in Be,Be'.
        pose proof Be as Bf;pose proof Be' as Bf'.
        apply (is_binding_finite_ax_eq eq1) in Bf.
        apply (is_binding_finite_ax_eq eq2) in Bf'.
        assert (c # e /\ c # e' /\ c # f /\ c # f') as (Fe&Fe'&Ff&Ff')
            by (revert F1 F2;repeat rewrite support_prod;simpl_In;tauto).
        repeat rewrite δ3_prod by assumption.
        repeat apply ax_eq_add || apply ax_eq_prod.
        * apply IHeq1;assumption.
        * assumption.
        * rewrite (ϵ_αKA eq1);reflexivity.
        * apply IHeq2;assumption.
        * assert (iheq1 : δ3 c e =α δ3 c f) by (apply IHeq1;tauto).
          assert (iheq2 : δ3 c e' =α δ3 c f') by (apply IHeq2;tauto);clear IHeq1 IHeq2 B1 B2.
          apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g Ig.
          -- apply in_flat_map in Ig as (a&Ia&Ig).
             apply in_map_iff in Ig as ((β&N)&<-&Iβ).
             apply SplitRange_result in Iβ as (Eβ&Min);simpl.
             pose proof Eβ as h.
             apply destr_bind_prod_full in h as (_&h).
             replace (d_binding (S N,false,0)) with (S N) in * by reflexivity.
             destruct h as [(L&E')| ->];[|exfalso;apply (Min (0,false,S N));reflexivity].
             etransitivity.
             ++ apply ax_eq_inf,proper_prod;[apply αKA_act,filter_binding_αKA,δ1_αKA,eq1
                                            |apply splitActStrict_αKA,eq2];try assumption.
                apply is_binding_finite_δ1,Be.
             ++ non_zero (filter_binding a β (δ1 a f)).
                apply test0_false in T as (u&Iu).
                assert (B : is_binding_finite (δ1 a f)) by apply is_binding_finite_δ1,Bf.
                apply filter_binding_lang in Iu as (Iu&Eu);
                  [pose proof Iu as Sz;apply (binding_finite_bound_size a B) in Sz|assumption].
                apply δ1_lang in Iu as (Iu&_);[|assumption].
                apply support_lang in Iu;rewrite Eu in *;clear Eu.
                apply Σ_bigger,in_flat_map;exists a;split.
                ** apply Iu,support_list_cons;now left.
                ** apply in_map_iff;exists (β,N);split;[reflexivity|].
                   apply SplitRange_In';tauto.
          -- apply in_flat_map in Ig as (a&Ia&Ig).
             apply in_map_iff in Ig as ((β&N)&<-&Iβ).
             apply SplitRange_result in Iβ as (Eβ&Min);simpl.
             pose proof Eβ as h.
             apply destr_bind_prod_full in h as (_&h).
             replace (d_binding (S N,false,0)) with (S N) in * by reflexivity.
             destruct h as [(L&E')| ->];[|exfalso;apply (Min (0,false,S N));reflexivity].
             etransitivity.
             ++ apply ax_eq_inf,proper_prod;symmetry;[apply αKA_act,filter_binding_αKA,δ1_αKA,eq1
                                                     |apply splitActStrict_αKA,eq2];try assumption.
                apply is_binding_finite_δ1,Be.
             ++ non_zero (filter_binding a β (δ1 a e)).
                apply test0_false in T as (u&Iu).
                assert (B : is_binding_finite (δ1 a e)) by apply is_binding_finite_δ1,Be.
                apply filter_binding_lang in Iu as (Iu&Eu);
                  [pose proof Iu as Sz;apply (binding_finite_bound_size a B) in Sz|assumption].
                apply δ1_lang in Iu as (Iu&_);[|assumption].
                apply support_lang in Iu;rewrite Eu in *;clear Eu.
                apply Σ_bigger,in_flat_map;exists a;split.
                ** apply Iu,support_list_cons;now left.
                ** apply in_map_iff;exists (β,N);split;[reflexivity|].
                   apply SplitRange_In';tauto.
    - pose proof B1 as Be.
      apply binding_finite_spec in Be;simpl in Be.
      apply andb_true_iff in Be as (Be&Be').
      rewrite binding_finite_spec in Be,Be'.
      pose proof Be as Bf;pose proof Be' as Bf'.
      apply (is_binding_finite_ax_eq eq1) in Bf.
      apply (is_binding_finite_ax_eq eq2) in Bf'.
      assert (c # e /\ c # e' /\ c # f /\ c # f') as (Fe&Fe'&Ff&Ff')
          by (revert F1 F2;repeat rewrite support_join;simpl_In;tauto).
      repeat rewrite (KA_αKA (δ3_join _ _ _)).
      apply ax_eq_add;[apply IHeq1|apply IHeq2];tauto.
    - repeat rewrite δ3_star by assumption.
      rewrite IHeq,eq.
      + reflexivity.
      + rewrite <-binding_finite_spec in *;simpl in B2;apply andb_true_iff in B2;tauto.
      + rewrite <-binding_finite_spec in *;simpl in B1;apply andb_true_iff in B1;tauto.
      + apply F1.
      + apply F2.
    - destruct H as [a b e h|h];[|apply KA_αKA,δ3_KA,ax_eq_ax;assumption].
      rewrite support_action,In_act_lists in F2.
      revert F2;unfold act at 1;simpl;unfold_eqX;subst.
      + intros;rewrite action_invariant;[reflexivity|].
        apply map_eq_id;intros c Ic;apply elements_inv_act_atom.
        intros [<-|[<-|F]];tauto.
      + intros;rewrite action_invariant;[reflexivity|].
        apply map_eq_id;intros c Ic;apply elements_inv_act_atom.
        intros [<-|[<-|F]];tauto.
      + intros _.
        replace c with ([(a,b)]∙c) at 2 by (apply elements_inv_act_atom;intros [<-|[<-|F]];tauto).
        etransitivity;[|apply KA_αKA,δ3_act].
        apply ax_eq_ax,αKA_αα.
        intros u Iu.
        apply δ3_lang in Iu as (u1&u2&d&->&Eu1&Iu&Min);[|assumption].
        destruct (h _ Iu) as (E1&E2).
        apply support_lang in Iu;rewrite <- Iu in F1.
        rewrite support_list_cons,support_list_app in F1;simpl_In in F1.
        assert (c<>d /\ c # u1 /\ c # u2) as (N1&Fu1&Fu2)
            by (split;[intros ->;apply F1;left;left;reflexivity|tauto]).
        apply αfresh_support in Fu1.
        apply αfresh_support in Fu2.
        revert E1 E2;unfold fresh__α;simpl_binding.
        repeat rewrite 𝗙_perm;unfold act;simpl;simpl_eqX.
        unfold_eqX;repeat rewrite Eu1||rewrite Fu1||rewrite Fu2||rewrite prod_unit_l
                   ||rewrite prod_assoc;intros ->;try intros ->;split;reflexivity.
    - destruct H as [e f|e f].
      + etransitivity;[apply KA_αKA,δ3_join|].
        cut (δ3 c (e⋆·f) <=α δ3 c f);[intro hyp;apply hyp|].
        case_eq (test0 f);intro Tf;[apply ax_eq_inf;transitivity zero;[|symmetry];
                                    apply KA_αKA,δ3_test0;simpl;assumption|].
        assert (is_binding_finite (e⋆) /\ is_binding_finite e) as (Bs&Be)
        by (revert Tf B1;clear;repeat rewrite <- binding_finite_spec;simpl;
            repeat rewrite orb_true_iff ||rewrite andb_true_iff;intros ->;firstorder).
        rewrite δ3_star_ind;
          [|revert B1;clear;repeat rewrite <- binding_finite_spec;simpl;
            repeat rewrite orb_true_iff|| rewrite andb_true_iff;tauto
           |revert F1;repeat rewrite support_prod||rewrite support_join;simpl_In;tauto].
        apply inf_join_inf;[|reflexivity].
        rewrite <- (mon_assoc _ _ _).
        etransitivity;[apply proper_prod_inf;[reflexivity|apply ka_star_left_ind;assumption]|].
        rewrite <- IHeq;try assumption;
          [|revert B1;clear;repeat rewrite <- binding_finite_spec;simpl;
            repeat rewrite orb_true_iff|| rewrite andb_true_iff;tauto].
        etransitivity;[|apply ax_eq_inf;symmetry;apply KA_αKA,δ3_join].
        etransitivity;[|apply inf_cup_left].
        rewrite δ3_prod.
        * etransitivity;[|apply inf_cup_left].
          apply inf_cup_left.
        * revert B1;clear;repeat rewrite <- binding_finite_spec;simpl;
            repeat rewrite orb_true_iff|| rewrite andb_true_iff;tauto.
        * revert F1;repeat rewrite support_prod||rewrite support_join;simpl_In;tauto.
      + etransitivity;[apply KA_αKA,δ3_join|].
        assert (L : e·f <=α e) by apply eq;clear eq.
        cut (δ3 c (e·f⋆) <=α δ3 c e);[intro hyp;apply hyp|].
        case_eq (test0 e);intro Te;[apply ax_eq_inf;transitivity zero;[|symmetry];
                                    apply KA_αKA,δ3_test0;simpl;[rewrite orb_false_r|];assumption|].
        assert (is_binding_finite (f⋆) /\ is_binding_finite f) as (Bs&Bf)
        by (revert Te B1;clear;repeat rewrite <- binding_finite_spec;simpl;
            repeat rewrite orb_true_iff ||rewrite andb_true_iff;intros ->;firstorder).
        assert (IH: δ3 c (e·f) <=α δ3 c e).
        * rewrite <- IHeq;simpl.
          -- etransitivity;[|apply ax_eq_inf,KA_αKA;symmetry;apply δ3_join]; apply inf_cup_left.
          -- assumption.
          -- rewrite <- binding_finite_spec in *;simpl;rewrite B2,Bf.
             repeat rewrite orb_true_r;reflexivity.
          -- revert F1;repeat rewrite support_prod||rewrite support_join||rewrite support_star;
               simpl_In;tauto.
          -- assumption.
        * clear IHeq B1; rewrite δ3_prod;
            [ | rewrite <- binding_finite_spec in *;simpl in *;rewrite B2,Bs,orb_true_r;reflexivity
              |revert F1;repeat rewrite support_prod||rewrite support_join||rewrite support_star;
               simpl_In;tauto].
          rewrite δ3_prod in IH;
            [ | rewrite <- binding_finite_spec in *;simpl in *;rewrite B2,Bf,orb_true_r;reflexivity
              |revert F1;repeat rewrite support_prod||rewrite support_join||rewrite support_star;
               simpl_In;tauto].   
          repeat apply inf_join_inf.
          -- apply ka_star_right_ind.
             etransitivity;[|apply IH].
             etransitivity;[|apply inf_cup_left].
             apply inf_cup_left.
          -- rewrite δ3_star;
               [|assumption
                |revert F1;repeat rewrite support_prod||rewrite support_join||rewrite support_star;
                 simpl_In;tauto].
             rewrite (mon_assoc _ _ _).
             etransitivity;[|apply ka_star_right_ind];[apply proper_prod_inf;[|reflexivity]|].
             ++ etransitivity;[|apply IH].
                etransitivity;[|apply inf_cup_left].
                apply inf_cup_right.
             ++ etransitivity;[|apply IH].
                etransitivity;[|apply inf_cup_left].
                apply inf_cup_left.
          -- apply Σ_bounded;intros g Ig.
             apply in_flat_map in Ig as (a&Ia&Ig).
             apply in_map_iff in Ig as ((β&N)&<-&Iβ).
             apply SplitRange_result in Iβ as (Eβ&Min);simpl.
             pose proof Eβ as h.
             repeat rewrite (mon_assoc _ _ _).
             transitivity (δ3 c e · f⋆);[apply proper_prod_inf;[|reflexivity]
                                        |apply ka_star_right_ind;rewrite <- IH at 2;
                                         etransitivity;[|apply inf_cup_left];apply inf_cup_left].
             apply destr_bind_prod_full in h as (_&h).
             replace (d_binding (S N,false,0)) with (S N) in * by reflexivity.
             destruct h as [(L'&E')| ->];[|exfalso;apply (Min (0,false,S N));reflexivity].
             destruct β as ((C,ff),K).
             unfold d_binding in E';simpl in *.
             replace C with 0 in * by lia.
             replace K with N in * by lia.
             clear E' C K.
             rewrite <- act_star.
             etransitivity;[apply ax_eq_inf,KA_αKA,proper_prod;
                              [apply proper_prod;
                               [|apply KA_act,LowerExpr_star_true_left]|];reflexivity|].
             repeat rewrite act_join||rewrite act_prod.
             repeat rewrite semiring_right_distr||rewrite semiring_left_distr
             ||rewrite (mon_assoc _ _ _).
             apply inf_join_inf.
             ++ transitivity ([(a, c)] ∙ filter_binding a (0, ff, N) (δ1 a e) · splitActStrict c a N f).
                ** repeat (apply proper_prod_inf;[|reflexivity]).
                   rewrite act_star.
                   apply ka_star_right_ind.
                   rewrite <- act_prod;apply αKA_inf_act.
                   etransitivity;[|apply filter_binding_αKA_inf;
                                   [apply is_binding_finite_δ1,B2
                                   |etransitivity;[|apply δ1_αKA_inf,L;assumption]];
                                   simpl;apply inf_cup_right].
                   rewrite filter_binding_Σ,map_map.
                   unfold LowerExpr;rewrite Σ_distr_l,map_map.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as (β&<-&Iβ).
                   non_zero (filter_binding a (0, ff, N) (δ1 a e)).
                   non_zero (filter_binding a β f).
                   etransitivity;[|apply Σ_bigger,in_map_iff;exists ((0,ff,N),β);split;[reflexivity|]].
                   --- apply KA_αKA_inf,CompletenessKA_inf;intros u Iu.
                       pose proof Iu as (u1&u2&->&Iu1&Iu2).
                       apply filter_binding_lang in Iu1 as (Iu1&Eu1);[|apply is_binding_finite_δ1,B2].
                       apply filter_binding_lang in Iu2 as (Iu2&Eu2);[|assumption].
                       apply filter_binding_lang;[|split;[assumption|]].
                       +++ rewrite <- binding_finite_spec;simpl;rewrite orb_true_iff,andb_true_iff.
                           right;split;apply binding_finite_spec,is_binding_finite_filter_binding;
                             [apply is_binding_finite_δ1|];assumption.
                       +++ simpl_binding;rewrite Eu1,Eu2.
                           destruct β as ((K,ff')&?).
                           rewrite lower_squares_alt in Iβ by reflexivity.
                           unfold square,d_binding in Iβ;simpl in Iβ.
                           destruct Iβ as (->&h).
                           rewrite orb_false_r,negb_true_iff in h.
                           unfold prod_binding;destruct_ltb N K;[|lia].
                           destruct_ltb K N;simpl_nat.
                           *** destruct h as [h|(->&->)];[lia|].
                               rewrite orb_false_r;reflexivity.
                           *** reflexivity.
                   --- apply test0_false in T as (u1&Iu1).
                       apply test0_false in T0 as (u2&Iu2).
                       apply filter_binding_lang in Iu1 as (Iu1&Eu1);[|apply is_binding_finite_δ1,B2].
                       apply filter_binding_lang in Iu2 as (Iu2&Eu2);[|apply Bf].
                       rewrite <- Eu1,<-Eu2.
                       apply range_In;try apply is_binding_finite_δ1;try assumption.
                       unfold close_balanced;simpl_binding.
                       rewrite Eu1,Eu2;simpl.
                       destruct β as ((K,ff')&?).
                       rewrite lower_squares_alt in Iβ by reflexivity.
                       unfold square,d_binding in *;simpl in *;lia.
                ** non_zero(filter_binding a (0, ff, N) (δ1 a e)).
                   apply test0_false in T as (u&Iu).
                   apply filter_binding_lang in Iu as (Iu&Eu);[|apply is_binding_finite_δ1,B2].
                   apply (binding_finite_bound_size a (is_binding_finite_δ1 a B2)) in Iu as Sz.
                   rewrite Eu in Sz;clear u Iu Eu.
                   rewrite <-  IH.
                   etransitivity;[|apply inf_cup_right].
                   apply Σ_bigger,in_flat_map;exists a;split;[assumption|].
                   apply in_map_iff;exists ((0,ff,N),N);split;[reflexivity|].
                   apply SplitRange_In';assumption.
             ++ transitivity  (((([(a, c)] ∙ filter_binding a (0, ff, N) (δ1 a e))
                                   · [(a, c)] ∙ filter_binding a (N, true, N) f)
                                  · [(a, c)] ∙ (LowerExpr a N true f ⋆))
                                 · splitActStrict c a N f);
                  repeat (apply proper_prod_inf;[|reflexivity]).
                ** clear IH Eβ Min L'.
                   rewrite <- act_prod;apply αKA_inf_act.
                   apply ka_star_right_ind.
                   etransitivity;[|apply filter_binding_αKA_inf,δ1_αKA_inf,L;
                                   try apply is_binding_finite_δ1;assumption].
                   apply KA_αKA_inf,CompletenessKA_inf;intros u (u1&u2&->&Iu1&Iu2).
                   apply LowerExpr_lang in Iu2 as (Iu2&Eu2);[|assumption].
                   apply filter_binding_lang in Iu1 as (Iu1&Eu1);[|apply is_binding_finite_δ1,B2].
                   apply filter_binding_lang;
                     [apply is_binding_finite_δ1;rewrite <- binding_finite_spec in *;simpl;
                      rewrite B2,Bf,orb_true_r;reflexivity|].
                   cut (𝗙 a (u1 ++ u2) = (0, ff, N));[intros Eu;split;[|tauto]|].
                   --- apply δ1_lang;[rewrite <- binding_finite_spec in *;simpl;
                                      rewrite B2,Bf,orb_true_r;reflexivity|].
                       split.
                       +++ apply δ1_lang in Iu1 as (Iu1&E1);[|assumption].
                           exists (open a::u1),u2;tauto.
                       +++ unfold close_balanced;rewrite Eu;reflexivity.
                   --- simpl_binding;rewrite Eu1.
                       apply lower_squares_alt in Eu2 as (Eu2&h);[|reflexivity].
                       destruct (𝗙 a u2) as ((K&ff')&?).
                       unfold square,d_binding in *;simpl in *;subst.
                       rewrite orb_false_r,negb_true_iff in h.
                       unfold prod_binding.
                       destruct_ltb N K;[|lia].
                       destruct_ltb K N.
                       +++ destruct h as [h|(->&->)];[lia|].
                           rewrite orb_false_r;reflexivity.
                       +++ simpl_nat;reflexivity.
                ** transitivity  ((([(a, c)] ∙ filter_binding a (0, true, N) (δ1 a e)))
                                    · splitActStrict c a N f);
                     repeat (apply proper_prod_inf;[|reflexivity]).
                   --- clear IH Eβ Min L'.
                       repeat rewrite <- act_prod;apply αKA_inf_act.
                       etransitivity;[|apply filter_binding_αKA_inf,δ1_αKA_inf,ka_star_right_ind,L;
                                       try apply is_binding_finite_δ1;assumption].
                       apply KA_αKA_inf,CompletenessKA_inf;intros u (?&u3&->&(u1&u2&->&Iu1&Iu2)&Iu3).
                       apply LowerExpr_star_lang in Iu3 as (Iu3&Eu3);[|assumption].
                       apply filter_binding_lang in Iu1 as (Iu1&Eu1);[|apply is_binding_finite_δ1,B2].
                       apply filter_binding_lang in Iu2 as (Iu2&Eu2);[|assumption].
                       apply filter_binding_lang;
                         [apply is_binding_finite_δ1;rewrite <- binding_finite_spec in *;simpl in *;
                          rewrite B2,Bs,orb_true_r;reflexivity|].
                       cut (𝗙 a ((u1 ++ u2)++u3) = (0, true, N));[intros Eu;split;[|tauto]|].
                       +++ apply δ1_lang;[rewrite <- binding_finite_spec in *;simpl in *;
                                          rewrite B2,Bs,orb_true_r;reflexivity|].
                           split.
                           *** apply δ1_lang in Iu1 as (Iu1&E1);[|assumption].
                               exists (open a::u1),(u2++u3);rewrite app_ass;repeat split; try tauto.
                               destruct Iu3 as (n&Iu3);exists (S n),u2,u3;tauto.
                           *** unfold close_balanced;rewrite Eu;reflexivity.
                       +++ simpl_binding;rewrite Eu1,Eu2.
                           apply lower_squares_alt in Eu3 as (Eu3&h);[|reflexivity].
                           destruct (𝗙 a u3) as ((K&ff')&?).
                           unfold square,d_binding in *;simpl in *;subst.
                           assert (L': K<=N) by lia;clear h.
                           unfold prod_binding.
                           repeat rewrite orb_true_r.
                           destruct_ltb N N;[|lia].
                           destruct_ltb N K;[|lia];simpl;simpl_nat.
                           destruct_ltb K N;[replace K with N by lia|];reflexivity.
                   --- non_zero(filter_binding a (0, true, N) (δ1 a e)).
                       apply test0_false in T as (u&Iu).
                       apply filter_binding_lang in Iu as (Iu&Eu);[|apply is_binding_finite_δ1,B2].
                       apply (binding_finite_bound_size a (is_binding_finite_δ1 a B2)) in Iu as Sz.
                       rewrite Eu in Sz;clear u Iu Eu.
                       rewrite <-  IH.
                       etransitivity;[|apply inf_cup_right].
                       apply Σ_bigger,in_flat_map;exists a;split;[assumption|].
                       apply in_map_iff;exists ((0,true,N),N);split;[reflexivity|].
                       apply SplitRange_In';try assumption.
                       +++ unfold prod_binding;destruct_ltb N (S N);[lia|].
                           f_equal;f_equal;lia.
                       +++ intros ((K&?)&?).
                           unfold prod_binding;destruct K;simpl;discriminate.
  Qed.
  
  Corollary δ3_αKA_inf c e f : is_binding_finite f -> c # e -> c # f -> e <=α f -> δ3 c e <=α δ3 c f.
  Proof.
    intros Bf Fe Ff eq.
    unfold ax_inf.
    etransitivity;[apply KA_αKA;rewrite <- δ3_join;reflexivity|].
    apply δ3_αKA,eq;try assumption.
    rewrite support_join;simpl_In;tauto.
  Qed.

  Lemma δ3_open c e : is_binding_finite e -> c # e -> ⟪open c⟫·δ3 c e <=α e.
  Proof.
    intros Be Fc;unfold δ3;rewrite Σ_distr_l,map_map.
    apply Σ_bounded;intros f If.
    apply in_map_iff in If as (a&<-&Ia).
    etransitivity;[apply proper_prod_inf;[reflexivity
                                         |apply ax_eq_inf,KA_αKA,splitActStrict_splitStrict_list]|].
    rewrite Σ_distr_l,map_map.
    apply Σ_bounded;intros f If.
    apply in_map_iff in If as ((f1&f2)&<-&If).
    simpl.
    transitivity ([(a,c)]∙(⟪open a⟫·f1)·f2).
    - rewrite act_prod,(mon_assoc _ _ _).
      apply proper_prod_inf;[|reflexivity].
      apply proper_prod_inf;[|reflexivity].
      repeat (unfold act;simpl);simpl_eqX;reflexivity.
    - case_eq (test0 f2);intro T;
        [etransitivity;[|apply zero_minimal];
         apply ax_eq_inf,KA_αKA,test0_spec;simpl;rewrite T;
         apply orb_true_r|].
      etransitivity;[apply proper_prod_inf;[|reflexivity];
                     apply ax_eq_inf;symmetry;apply ax_eq_ax,αKA_αα|].
      + intros w (?&u&->&->&Iu).
        unfold fresh__α at 1; simpl_binding.
        apply test0_false in T as (v&Iv).
        split.
        * destruct (splitStrict_list_binding (δ_binFin _ Be) If Iu) as (->&_);reflexivity.
        * pose proof (splitStrict_list_lang (δ_binFin _ Be) If Iu Iv) as Iu'.
          apply αfresh_support;simpl.
          apply δ_lang,support_lang in Iu'.
          rewrite app_comm_cons,support_list_app in Iu'.
          rewrite <- Iu' in Fc;simpl_In in Fc;tauto.
      + rewrite <- (mon_assoc _ _ _).
        etransitivity;[|apply KA_αKA_inf,δ_inf_e].
        apply proper_prod_inf;[reflexivity|].
        eapply KA_αKA_inf,splitStrict_list_inf,If.
        apply δ_binFin,Be.
  Qed.
        
  Lemma δ3_support c e : ⌊δ3 c e⌋ ⊆ c::⌊e⌋.
  Proof.
    unfold δ3.
    rewrite <- Σ_support.
    intros a Ia.
    apply In_support_list in Ia as (f&If&Ia).
    apply in_map_iff in If as (b&<-&Ib).
    apply splitActStrict_support in Ia.
    rewrite δ_support in Ia.
    destruct Ia as [<-|[<-|Ia]];simpl;tauto.
  Qed.
    
End s.