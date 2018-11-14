Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp.
Require Import aeq_facts alpha_regexp closed_languages binding_finite alphaKA systems.
Require Import factors filters.

Opaque filter_binding.
Section s.

  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.

  Notation Regexp := (@regexp letter).

  Fixpoint split_binding a β e :=
    match e with
    | e_zero => []
    | e_un => []
    | ⟪x⟫ => if β=?= 𝗳 a x then [(⟪x⟫,un)] else []
    | e_add e f => split_binding a β e ++ split_binding a β f
    | e_prod e f =>
      if (test0 (e·f))
      then []
      else map (fun e' => (fst e',snd e'·f)) (split_binding a β e)
               ++ (flat_map (fun B => map (fun F => (filter_binding a (fst B) e·fst F,snd F))
                                       (split_binding a (snd B) f))
                            (factors β (sizeExpr e)))
    | e_star e =>
      (flat_map (fun B => map (fun F => (filter_binding a (fst B) (e⋆)·fst F,snd F·e⋆))
                           (split_binding a (snd B) e))
                (factors β (sizeExpr e)))
    end.

  Fixpoint splitExpr a β e :=
    match e with
    | e_zero => zero
    | e_un => zero
    | ⟪x⟫ => if β=?= 𝗳 a x then ⟪x⟫ else zero
    | e_add e f => splitExpr a β e ∪ splitExpr a β f
    | e_prod e f =>
      if (test0 (e·f))
      then zero
      else (splitExpr a β e · f)
             ∪ (Σ (map (fun B => filter_binding a (fst B) e·(splitExpr a (snd B) f))
                       (factors β (sizeExpr e))))
    | e_star e =>
      Σ (map (fun B => filter_binding a (fst B) (e⋆)·(splitExpr a (snd B) e)·e⋆)
             (factors β (sizeExpr e)))
    end.

  Lemma splitExpr_alt a β e : splitExpr a β e =KA Σ (map (fun p => fst p·snd p) (split_binding a β e)).
  Proof.
    revert β;induction e;intro β;simpl;try reflexivity.
    - rewrite IHe1,IHe2,map_app;apply algebra.Σ_app.
    - destruct (test0 e1||test0 e2);[reflexivity|].
      repeat rewrite map_app||rewrite map_map;rewrite IHe1.
      etransitivity;[|apply algebra.Σ_app];apply proper_join.
      + etransitivity;[apply Σ_distr_r|];rewrite map_map.
        simpl;apply Σ_map_equiv;intros;symmetry;apply (mon_assoc  _ _ _).
      + clear IHe1;induction (factors β (sizeExpr e1)) as [|(β1,β2) I];simpl;[reflexivity|].
        rewrite IHe2.
        repeat rewrite map_app.
        etransitivity;[|apply algebra.Σ_app];apply proper_join.
        * etransitivity;[apply Σ_distr_l|];repeat rewrite map_map.
          simpl;apply Σ_map_equiv;intros;apply (mon_assoc  _ _ _).
        * apply IHI.
    - induction (factors β (sizeExpr e)) as [|(β1,β2) I];simpl;[reflexivity|].
      rewrite IHe.
      repeat rewrite map_app.
      etransitivity;[|apply algebra.Σ_app];apply proper_join.
      + etransitivity;[apply proper_prod;[apply Σ_distr_l|reflexivity]|].
        etransitivity;[apply Σ_distr_r|];repeat rewrite map_map;simpl.
        simpl;apply Σ_map_equiv;intros.
        etransitivity;[symmetry;apply (mon_assoc  _ _ _)|].
        etransitivity;[apply proper_prod;[reflexivity|symmetry;apply (mon_assoc  _ _ _)]|].
        apply (mon_assoc  _ _ _).
      + apply IHI.
    - unfold_eqX;simpl;[|reflexivity].
      etransitivity;[|symmetry;apply right_unit].
      symmetry;apply right_unit.
  Qed.
        
      
      

  Lemma split_binding_test0 a β e:
    test0 e = true -> split_binding a β e = [].
  Proof.
    induction e;simpl;try reflexivity||discriminate.
    - rewrite andb_true_iff; intros (eq1,eq2);rewrite IHe1,IHe2;tauto.
    - intros ->;reflexivity.
  Qed.
      
  Corollary splitExpr_test0 a β e :
    test0 e = true -> splitExpr a β e =KA zero.
  Proof.
    intros T;rewrite splitExpr_alt,(split_binding_test0 a β T);reflexivity.
  Qed.

  Lemma split_binding_ϵ a β e f1 f2 : (f1,f2) ∈ split_binding a β e -> ϵ f1 = zero.
  Proof.
    revert β f1 f2;induction e;intros β f1 f2;simpl;simpl_In;try tauto.
    - intros [I|I];[eapply IHe1|eapply IHe2];eassumption.
    - destruct (test0 e1||test0 e2);[simpl;tauto|simpl_In].
      rewrite in_map_iff,in_flat_map;setoid_rewrite in_map_iff.
      intros [I|I].
      + destruct I as ((g1,g2)&heq&I);inversion heq;clear heq;subst.
        eapply IHe1,I.
      + destruct I as ((β1,β2)&Ib&(g1&g2)&heq&I);inversion heq;clear heq;subst;simpl.
        destruct (ϵ_zero_or_un (filter_binding a β1 e1)) as [-> | ->];[|reflexivity].
        eapply IHe2 in I as ->;reflexivity.
    - rewrite in_flat_map;setoid_rewrite in_map_iff;intro I.
      destruct I as ((β1,β2)&Ib&(g1&g2)&heq&I);inversion heq;clear heq;subst;simpl.
      destruct (ϵ_zero_or_un (filter_binding a β1 (e⋆))) as [-> | ->];[|reflexivity].
      eapply IHe in I as ->;reflexivity.
    - unfold_eqX;simpl;[|tauto].
      intros [heq|heq];inversion heq;reflexivity.
  Qed.

  Corollary splitExpr_ϵ a β e : ϵ (splitExpr a β e) = zero.
  Proof.
    rewrite (ϵ_KA (splitExpr_alt a β e));apply ϵ_Σ_zero.
    intros f If;apply in_map_iff in If as ((f1,f2)&<-&If).
    unfold fst,snd;simpl;apply split_binding_ϵ in If as ->;reflexivity.
  Qed.

  Lemma split_binding_act p a β e : split_binding a β (p∙e) = p ∙ (split_binding (p∗∙a) β e).
  Proof.
    unfold act at 2,act_lists;revert β;induction e;intros β;simpl;try reflexivity.
    - rewrite map_app;replace actReg with act by reflexivity.
      rewrite IHe1,IHe2;reflexivity.
    - repeat rewrite map_app;replace actReg with act by reflexivity.
      repeat rewrite test0_act;destruct (test0 e1||test0 e2);[reflexivity|].
      repeat rewrite map_app.
      repeat rewrite sizeExpr_act.
      repeat setoid_rewrite IHe1.
      repeat setoid_rewrite IHe2.
      f_equal.
      + repeat rewrite map_map;reflexivity.
      + induction (factors β (sizeExpr e1)) as [|(x,y)L];simpl;[reflexivity|].
        rewrite IHe2,map_map.
        repeat rewrite map_map||rewrite map_app.
        f_equal.
        * apply map_ext;intro.
          unfold act at 4,act_pair;simpl.
          f_equal.
          unfold act,prod,regProduct;simpl;replace actReg with act by reflexivity.
          f_equal.
          rewrite filter_binding_act.
          rewrite <- (act_p_pinv p a) at 1.
          reflexivity.
        * apply IHL.
    - repeat rewrite map_app;replace actReg with act by reflexivity.
      repeat rewrite sizeExpr_act.
      repeat setoid_rewrite IHe.
      induction (factors β (sizeExpr e)) as [|(x,y)L];simpl;[reflexivity|].
      rewrite IHe,map_map.
      repeat rewrite map_map||rewrite map_app.
      f_equal.
      + apply map_ext;intro.
        unfold act at 4,act_pair;simpl.
        f_equal.
        unfold act,prod,regProduct;simpl;replace actReg with act by reflexivity.
        f_equal.
        rewrite filter_binding_act.
        rewrite <- (act_p_pinv p a) at 1.
        reflexivity.
      + apply IHL.
    - rewrite 𝗳_perm;unfold_eqX;try reflexivity.
  Qed.
          
  Lemma splitExpr_act p a β e : splitExpr a β (p∙e) = p ∙ (splitExpr (p∗∙a) β e).
  Proof.
    unfold act at 2,act_lists;revert β;induction e;intros β;simpl;try reflexivity.
    - rewrite IHe1,IHe2;reflexivity.
    - replace actReg with act by reflexivity.
      repeat rewrite test0_act;destruct (test0 e1||test0 e2);[reflexivity|].
      replace act with  actReg by reflexivity.
      rewrite IHe1.
      unfold join,regJoin; f_equal;simpl.
      f_equal.
      replace actReg with act by reflexivity.
      rewrite Σ_act,sizeExpr_act.
      unfold act at 3,act_lists.
      rewrite map_map.
      f_equal;apply map_ext.
      intros (β1,β2);rewrite IHe2;simpl.
      rewrite <- (act_p_pinv p a) at 1.
      rewrite <-filter_binding_act.
      reflexivity.
    - replace actReg with act by reflexivity;rewrite Σ_act.
      unfold act at 5,act_lists;rewrite map_map,sizeExpr_act.
      f_equal;apply map_ext.
      intros (β1,β2);rewrite IHe;simpl.
      rewrite <- (act_p_pinv p a) at 1.
      replace (p∙e⋆) with (p∙(e⋆)) by reflexivity.
      rewrite <- (filter_binding_act p (p∗∙a) β1 (e⋆)).
      reflexivity.
    - rewrite 𝗳_perm;unfold_eqX;try reflexivity.
  Qed.
  
  Lemma split_binding_bindings a β e f1 f2 u1 :
    is_binding_finite e -> (f1,f2) ∈ split_binding a β e ->
    ⟦f1⟧ u1 -> 𝗙 a u1 = β.
  Proof.
    intros Be ;revert β f1 f2 u1.
    induction_bin_fin e Be;intros β f1 f2 u1;simpl;try tauto.
    - unfold_eqX;simpl;[|tauto].
      intros [heq|heq];inversion heq;clear heq;subst.
      intros -> ;simpl_binding;repeat split;discriminate.
    - simpl_In;intros [I|I] I1 ;[eapply IHe1 in I|eapply IHe2 in I];
        eassumption||unfold join,joinLang;tauto.
    - rewrite T;simpl_In; rewrite in_map_iff,in_flat_map;setoid_rewrite in_map_iff.
      intros [I|I];[destruct I as ((g1,g2)&heq&I)|destruct I as ((β1,β2)&Ib&(g1&g2)&heq&I)];
        inversion heq;clear heq;subst.
      + intros I1.
        eapply IHe1 in I1;eassumption.
      + simpl in I;intros (v1&v2&->&I1&I2).
        apply factors_prod in Ib as <-;simpl_binding.
        apply (IHe2 β2 g1 f2 v2) in I as <-;try assumption.
        apply filter_binding_lang in I1 as (I1&<-);[|assumption].
        reflexivity.
    - rewrite T;simpl;tauto. 
    - rewrite in_flat_map;setoid_rewrite in_map_iff;intro I.
      destruct I as ((β1,β2)&Ib&(g1&g2)&heq&I);inversion heq;clear heq;subst;simpl.
      intros (v1&v2&->&I1&I2).
      apply factors_prod in Ib as <-;simpl_binding.
      apply (IHe β2 g1 g2 v2) in I as <-;try assumption.
      apply filter_binding_lang in I1 as (I1&<-);[|apply sqExpr_bindings_finite_star,Sq].
      reflexivity.
  Qed.

  Lemma split_binding_lang a β e f1 f2 u1 u2 :
    is_binding_finite e -> (f1,f2) ∈ split_binding a β e ->
    ⟦f1⟧ u1 -> ⟦f2⟧ u2 -> ⟦e⟧ (u1++u2) /\ u1 <> [] /\ 𝗙 a u1 = β.
  Proof.
    intros Be ;revert β f1 f2 u1 u2.
    induction_bin_fin e Be;intros β f1 f2 u1 u2;simpl;try tauto.
    - unfold_eqX;simpl;[|tauto].
      intros [heq|heq];inversion heq;clear heq;subst.
      intros -> -> ;simpl_binding;repeat split;discriminate.
    - simpl_In;intros [I|I] I1 I2 ;[eapply IHe1 in I|eapply IHe2 in I];
        eassumption||unfold join,joinLang;tauto.
    - rewrite T;simpl_In; rewrite in_map_iff,in_flat_map;setoid_rewrite in_map_iff.
      intros [I|I];[destruct I as ((g1,g2)&heq&I)|destruct I as ((β1,β2)&Ib&(g1&g2)&heq&I)];
        inversion heq;clear heq;subst.
      + intros I1 (v1&v2&->&I2&I3).
        apply (IHe1 _ _ _ u1 v1) in I as (I&N&<-);try assumption.
        rewrite <- app_ass;split;[|tauto].
        exists (u1++v1),v2;tauto.
      + simpl in I;intros (v1&v2&->&I1&I2) I3.
        apply factors_prod in Ib as <-;simpl_binding.
        apply (IHe2 β2 g1 f2 v2 u2) in I as (I&N&<-);try assumption.
        apply filter_binding_lang in I1 as (I1&<-);[|assumption].
        rewrite app_ass;split;[exists v1,(v2++u2);tauto|].
        split;[|reflexivity].
        intros Eq;apply app_eq_nil in Eq as (->&->);apply N;reflexivity.
    - rewrite T;simpl;tauto. 
    - rewrite in_flat_map;setoid_rewrite in_map_iff;intro I.
      destruct I as ((β1,β2)&Ib&(g1&g2)&heq&I);inversion heq;clear heq;subst;simpl.
      intros (v1&v2&->&I1&I2) (v3&v4&->&I3&I4).
      apply factors_prod in Ib as <-;simpl_binding.
      apply (IHe β2 g1 g2 v2 v3) in I as (I&N&<-);try assumption.
      apply filter_binding_lang in I1 as (I1&<-);[|apply sqExpr_bindings_finite_star,Sq].
      split.
      + cut (⟦e⟧⋆·⟦e⟧·⟦e⟧⋆≲⟦e⟧⋆).
        * intros h;apply h.
          exists ((v1++v2)++v3),v4;repeat rewrite app_ass;split;[reflexivity|].
          split;[|assumption].
          exists v1,(v2++v3);tauto.
        * rewrite star_switch_side,<- (mon_assoc _ _ _),ka_star_dup.
          rewrite ka_star_unfold_eq at 2.
          intro;unfold join,joinLang;tauto.
      + split;[|reflexivity].
        intros Eq;apply app_eq_nil in Eq as (->&->);apply N;reflexivity.
  Qed.

  Lemma split_binding_lang_full a e u1 u2 :
    is_binding_finite e -> ⟦e⟧ (u1++u2) -> u1 <> [] ->
    exists f1 f2, (f1,f2) ∈ (split_binding a (𝗙 a u1) e) /\ ⟦f1⟧ u1 /\ ⟦f2⟧ u2.
  Proof.
    - intros Be Iu N.
      revert u1 u2 Iu N.
      induction_bin_fin e Be;intros u1 u2 Iu N;simpl.
      + exfalso;apply Iu.
      + exfalso;apply N;apply app_eq_nil in Iu as (->&_);reflexivity.
      + simpl in Iu;destruct u1;[exfalso;apply N;reflexivity|].
        inversion Iu;subst;apply app_eq_nil in H1 as (->&->);clear.
        exists ⟪x⟫,un;simpl_binding;simpl;repeat split;tauto.
      + destruct Iu as [Iu|Iu].
        * eapply IHe1 in Iu as (f1&f2&If&Iu);try eassumption.
          exists f1,f2;simpl_In;tauto.
        * eapply IHe2 in Iu as (f1&f2&If&Iu);try eassumption.
          exists f1,f2;simpl_In;tauto.
      + rewrite T;destruct Iu as (v1&v2&Eq&I1&I2).
        levi Eq;clear Eq;subst.
        * rewrite <- app_nil_r in I1.
          eapply IHe1 in I1 as (f1&f2&If&Iu1&Iu2);try eassumption||reflexivity.
          exists f1,(f2 · e2);split.
          -- simpl_In;left;apply in_map_iff;exists (f1,f2);simpl;tauto.
          -- split;[assumption|].
             exists [],v2;simpl;tauto.
        * rewrite app_comm_cons in I2.
          eapply IHe2 in I2 as (f1&f2&If&Iu1&Iu2);try eassumption||discriminate||reflexivity.
          exists (filter_binding a (𝗙 a v1) e1·f1),f2;split.
          -- simpl_In;right.
             apply in_flat_map;exists (𝗙 a v1,𝗙 a (a0::w));split.
             ++ apply factors_In;[|simpl_binding;reflexivity].
                apply binding_finite_bound_size;assumption.
             ++ apply in_map_iff; exists (f1, f2);simpl;tauto.
          -- split;[|assumption].
             exists v1,(a0::w);split;[reflexivity|split;[|assumption]].
             apply filter_binding_lang;tauto.
        * eapply IHe1 in I1 as (f1&f2&If&Iu1&Iu2);try eassumption||reflexivity.
          exists f1,(f2 · e2);split.
          -- simpl_In;left;apply in_map_iff;exists (f1,f2);simpl;tauto.
          -- split;[assumption|].
             exists (a0::w),v2;simpl;tauto.
      + assert (Eq : test0(e1·e2) = true) by apply T.
        apply test0_spec,soundness in Eq;apply Eq in Iu.
        exfalso;apply Iu.
      + cut (exists w1 w2 v1 v2, u1 = w1 ++ v1 /\ u2 = v2++w2 /\ v1 <> [] /\ ⟦e⋆⟧ w1 /\ ⟦e⋆⟧ w2 /\ ⟦e⟧ (v1++v2)).
        * subst;clear Iu N.
          intros (w1&w2&v1&v2&->&->&N&Iw1&Iw2&Ih).
          apply (IHe) in Ih as (f1&f2&If&Iv1&Iv2); [|assumption].
          exists (filter_binding a (𝗙 a w1) (e⋆)·f1),(f2·e⋆);split;[|split].
          -- apply in_flat_map;exists (𝗙 a w1,𝗙 a v1);split.
             ++ apply factors_In.
                ** transitivity (sizeExpr (e⋆));[|reflexivity].
                   apply binding_finite_bound_size;[|assumption].
                   apply sqExpr_bindings_finite_star,Sq.
                ** simpl_binding;reflexivity.
             ++ apply in_map_iff;exists (f1,f2);simpl;tauto.
          -- exists w1,v1;split;[reflexivity|split;[|assumption]].
             apply filter_binding_lang;[apply sqExpr_bindings_finite_star,Sq|].
             tauto.
          -- exists v2,w2;tauto.
        * clear IHe Sq a.
          destruct Iu as (n&In);revert u1 In N;induction n.
          -- intros u1 E N;apply app_eq_nil in E as (->&_);exfalso;apply N;reflexivity.
          -- intros u1 (v1&v2&E&I1&Ih) N.
             levi E;clear E;subst.
             ++ exists [],v2,v1,[];simpl;rewrite app_nil_r;repeat split.
                ** assumption.
                ** exists 0;reflexivity.
                ** exists n;assumption.
                ** assumption.
             ++ rewrite app_comm_cons in Ih;apply IHn in Ih as (x1&x2&x3&x4&->&->&N1&Ix1&Ix4&Ie);
                  [|discriminate].
                exists (v1++x1),x2,x3,x4;rewrite app_ass;repeat split;try assumption||reflexivity.
                destruct Ix1 as (m&Im);exists (S m),v1,x1;tauto.
             ++ exists [],v2,u1,(a::w);simpl;repeat split;try assumption||reflexivity.
                ** exists 0;reflexivity.
                ** exists n;tauto.
  Qed.

  Lemma splitExpr_lang a β e :
    is_binding_finite e ->
    ⟦splitExpr a β e⟧  ≃ (fun u => ⟦e⟧ u /\ exists u1 u2, u = u1++u2 /\ u1 <> [] /\ 𝗙 a u1 = β).
  Proof.
    rewrite (soundness (splitExpr_alt _ _ _));intros Be u;split.
    - intro Iu;apply Σ_lang in Iu as (f&If&Iu).
      apply in_map_iff in If as ((f1&f2)&<-&If);simpl in *.
      destruct Iu as (u1&u2&->&I1&I2).
      destruct (split_binding_lang Be If I1 I2) as (I3&N&<-).
      split;[assumption|exists u1,u2;tauto].
    - intros (Iu&u1&u2&->&N&F).
      apply Σ_lang;cut (exists f1 f2, (f1,f2) ∈ split_binding a β e /\ ⟦f1⟧ u1 /\ ⟦f2⟧ u2);
        [intros (f1&f2&If&I1&I2);exists (f1·f2);split;[apply in_map_iff;exists (f1,f2)|exists u1,u2];tauto|].
      subst;apply split_binding_lang_full;tauto.
  Qed.

  Lemma splitExpr_KA a β e f : is_binding_finite f -> e =KA f -> splitExpr a β e =KA splitExpr a β f.
  Proof.
    intros Bf E;apply CompletenessKA.
    rewrite (splitExpr_lang _ _ Bf).
    pose proof Bf as Be;apply (is_binding_finite_ax_eq (KA_αKA E)) in Be.
    rewrite (splitExpr_lang _ _ Be).
    intro u;rewrite (soundness E u);tauto.
  Qed.

  Lemma splitExpr_KA_inf a β e f :
    is_binding_finite f -> e <=KA f -> splitExpr a β e <=KA splitExpr a β f.
  Proof.
    unfold ax_inf;intros Bf Ef;rewrite <- (splitExpr_KA a β Bf Ef) at 2.
    reflexivity.
  Qed.

  Lemma splitExpr_zero a β e :
    is_binding_finite e -> c_binding β = 0 ->
    (forall u : list letter, ⟦ e ⟧ u -> a #α u) ->
    (β = ε \/ splitExpr a β e =KA 𝟬).
  Proof.
    intros Be CB F;destruct β as ((N,t)&z);simpl in CB;subst.
    destruct_eqX ((N,t,0) : 𝖡) ε;[left;reflexivity|right].
    apply test0_spec,not_false_is_true.
    intros T;apply test0_false in T as (u&Iu).
    apply splitExpr_lang in Iu as (Eu&u1&u2&->&_&h);[|assumption].
    apply F in Eu;revert Eu.
    unfold fresh__α;simpl_binding;rewrite h.
    destruct (𝗙 a u2) as (([]&t')&c');unfold prod_binding;simpl;
      intro heq;inversion heq;subst.
    - apply N0;destruct t;[discriminate|reflexivity].
    - lia.
  Qed.

  Lemma filter_binding_splitExpr e a β1 β2 :
    is_binding_finite e ->
    β2 <> ε ->
    c_binding β2 = 0 ->
    d_binding β2 <= d_binding β1 ->
    (snd(fst(β2)) = false) \/ (snd(fst(β1)) = true /\ d_binding β2 = d_binding β1) ->
    filter_binding a β1 e <=KA splitExpr a β2 e .
  Proof.
    intros Be N CB L1 hyp.
    apply CompletenessKA_inf.
    intros u Iu.
    apply filter_binding_lang in Iu as (Iu&Eu);[|assumption].
    apply splitExpr_lang;[assumption|].
    split;[assumption|];subst.
    clear Iu e Be.
    revert β2 CB N L1 hyp;induction u as [|[b|b|x] u];intros.
    - destruct hyp as [E|(F&_)];[|discriminate].
      exfalso;apply N.
      destruct β2 as ((x,y),z).
      unfold d_binding in *;simpl in *.
      rewrite E,CB;replace x with 0 by lia.
      reflexivity.
    - destruct_eqX b a.
      + destruct β2 as ((n&t)&?);simpl in *;subst.
        destruct (IHu (S n,t,0)) as (u1&u2&->&N'&Eu1);clear IHu.
        * reflexivity.
        * discriminate.
        * revert L1;unfold d_binding at 1 3;simpl_binding;simpl.
          revert hyp.
          simpl_binding;simpl.
          unfold prod_binding;simpl.
          destruct (𝗙 a u) as (([|[]]&?)&?);unfold d_binding;simpl.
          -- intros h L;exfalso.
             replace n with 0 in * by lia.
             destruct h as [->|(F&_)];[|discriminate].
             apply N;reflexivity.
          -- intros h L;replace n with 0 by lia;reflexivity.
          -- lia.
        * simpl.
          destruct hyp as [->|(e1&e2)];[now left|].
          destruct t;[right|now left].
          revert L1 e1 e2;simpl_binding;simpl.
          destruct (𝗙 a u) as (([|[]]&?)&?);unfold d_binding;simpl.
          -- discriminate.
          -- intros _ -> ->;split;reflexivity.
          -- intros _ -> ->;split;reflexivity.
        * exists (open a::u1),u2.
          split;[reflexivity|].
          split;[discriminate|].
          simpl_binding;rewrite Eu1.
          unfold prod_binding;destruct n;reflexivity.
      + destruct (IHu β2) as (u1&u2&->&N'&Eu1);clear IHu.
        * assumption.
        * assumption.
        * revert L1;simpl_binding;simpl;lia.
        * revert hyp;simpl_binding;simpl.
          rewrite prod_unit_l;simpl_nat;tauto.
        * exists (open b::u1),u2.
          split;[reflexivity|].
          split;[discriminate|].
          simpl_binding;rewrite Eu1,prod_unit_l;reflexivity.
    - destruct_eqX b a;[destruct_eqX β2 (1,false,0);subst|].
      + exists [close a],u.
        split;[reflexivity|].
        split;[discriminate|].
        simpl_binding;reflexivity.
      + destruct β2 as (([|[]]&t)&?);simpl in *;subst;
          [destruct t;[|exfalso;apply N,reflexivity]|destruct t;[|exfalso;apply N0,reflexivity] |].
        * exfalso.
          destruct hyp as [F|(e1&e2)];[discriminate|].
          revert e2;simpl_binding;simpl;discriminate.
        * destruct (IHu (0,true,0)) as (u1&u2&->&N'&Eu1);clear IHu.
          -- reflexivity.
          -- discriminate.
          -- unfold d_binding;simpl; lia.
          -- right; destruct hyp as [F|(e1&e2)];[discriminate|clear L1].
             revert e1 e2;simpl_binding.
             destruct (𝗙 a u) as (([]&?)&?);unfold d_binding;simpl.
             ++ intros -> _ ;split;reflexivity.
             ++ discriminate.
          -- exists (close a::u1),u2.
             split;[reflexivity|].
             split;[discriminate|].
             simpl_binding;rewrite Eu1;reflexivity.
        * destruct (IHu (S n,t,0)) as (u1&u2&->&N'&Eu1);clear IHu.
          -- reflexivity.
          -- discriminate.
          -- revert L1;simpl_binding;simpl;lia.
          -- destruct t;[destruct hyp as [F|(e1&e2)];[discriminate|right]|now left].
             clear L1 N N0;revert e1 e2.
             simpl_binding;simpl.
             intros e1 e2;split;[|lia].
             revert e1;destruct (𝗙 a u) as (([]&?)&?);simpl;tauto.
          -- exists (close a::u1),u2.
             split;[reflexivity|].
             split;[discriminate|].
             simpl_binding;rewrite Eu1;reflexivity.
      + destruct (IHu β2) as (u1&u2&->&N'&Eu1);clear IHu.
        * assumption.
        * assumption.
        * revert L1;simpl_binding;simpl;lia.
        * revert hyp;simpl_binding;simpl.
          rewrite prod_unit_l;simpl_nat;tauto.
        * exists (close b::u1),u2.
          split;[reflexivity|].
          split;[discriminate|].
          simpl_binding;rewrite Eu1,prod_unit_l;reflexivity.
    - case_in a ⌊x⌋.
      + destruct_ltb 0 (d_binding β2).
        * destruct β2 as (([]&t)&?);simpl in *;subst;
            [destruct t;[|exfalso;apply N,reflexivity]|unfold d_binding in *;simpl in *;lia].
          exists [var x],u.
          split;[reflexivity|].
          split;[discriminate|].
          simpl_binding;simpl.
          case_in a ⌊x⌋;[|tauto].
          reflexivity.
        * destruct (IHu β2) as (u1&u2&->&N'&Eu1);clear IHu.
          -- assumption.
          -- assumption.
          -- revert L1;simpl_binding;simpl;lia.
          -- revert hyp;simpl_binding.
             case_in a ⌊x⌋;[|tauto].
             simpl;simpl_nat.
             destruct β2 as ((n&t)&?);simpl in *;subst.
             replace (d_binding (n,t,0)) with n in * by reflexivity.
             destruct n;[lia|].
             destruct t;[|now left].
             destruct (𝗙 a u) as ((?&?)&?);simpl;unfold d_binding;simpl.
             intros [F|(e1&<-)];[discriminate|].
             right;split;[|reflexivity].
             revert e1;unfold prod_binding;simpl;tauto.
          -- exists (var x::u1),u2.
             split;[reflexivity|].
             split;[discriminate|].
             simpl_binding;simpl; case_in a ⌊x⌋;[|tauto].
             rewrite Eu1;unfold prod_binding.
             destruct β2 as (([]&t)&?);unfold d_binding in L;simpl in *;subst;[lia|reflexivity].
      + destruct (IHu β2) as (u1&u2&->&N'&Eu1);clear IHu.
        * assumption.
        * assumption.
        * revert L1;simpl_binding;simpl;lia.
        * revert hyp;simpl_binding;simpl.
          case_in a ⌊x⌋;[tauto|].
          rewrite prod_unit_l;simpl_nat;tauto.
        * exists (var x::u1),u2.
          split;[reflexivity|].
          split;[discriminate|].
          simpl_binding;simpl; case_in a ⌊x⌋;[tauto|].
          rewrite Eu1,prod_unit_l;reflexivity.
  Qed.
  Lemma splitExpr_inf a β e :
    is_binding_finite e -> splitExpr a β e <=KA e.
  Proof.
    intros Be;apply CompletenessKA_inf;intros u Iu.
    apply splitExpr_lang in Iu;tauto.
  Qed.
    
  Lemma splitExpr_αKA a β e f :
    is_binding_finite f -> c_binding β = 0
    -> e =α f -> splitExpr a β e =α splitExpr a β f.
  Proof.
    intros B2 CB eq;pose proof B2 as B1.
    apply (is_binding_finite_ax_eq eq) in B1.
    destruct β as ((N,t)&z);simpl in CB;subst.
    revert N t;induction eq;intros N t.
    - reflexivity.
    - symmetry;apply IHeq;assumption.
    - pose proof B1 as B3.
      apply (is_binding_finite_ax_eq eq1) in B3.
      etransitivity;[apply IHeq1|apply IHeq2];assumption.
    - clear B2;case_eq (test0 (e·e')).
      + intro T;assert (T1 : test0 (e·e') = true) by apply T;clear T.
        assert (T2 : test0 (f·f') = true)
          by (erewrite test0_αKA;[apply T1|rewrite eq1,eq2;reflexivity]).
        eapply splitExpr_test0,KA_αKA in T1 as ->.
        eapply splitExpr_test0,KA_αKA in T2 as ->.
        reflexivity.
      + intro T1.
        assert (T2 : test0 (f·f') = false)
          by (erewrite test0_αKA;[apply T1|rewrite eq1,eq2;reflexivity]).
        apply binding_finite_spec in B1;simpl in B1,T1;rewrite T1 in B1;simpl in B1.
        apply andb_true_iff in B1 as (Be&Be');rewrite binding_finite_spec in Be,Be'.
        pose proof Be as Bf; apply (is_binding_finite_ax_eq eq1) in Bf.
        pose proof Be' as Bf'; apply (is_binding_finite_ax_eq eq2) in Bf'.
        pose proof (IHeq1 Bf Be) as eq1';pose proof (IHeq2 Bf' Be') as eq2';clear IHeq1 IHeq2.
        simpl in *;rewrite T1,T2;apply proper_join;[rewrite eq1',eq2;reflexivity|].
        apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g Ig;
          apply in_map_iff in Ig as ((β1&β2)&<-&Iβ);simpl;
            destruct (factors_open_balanced Iβ) as (N'&t'&->&Lβ).
        * rewrite eq2'.
          etransitivity;[apply proper_prod_inf;[apply filter_binding_αKA_inf;
                                                [apply Bf|rewrite eq1;reflexivity]|reflexivity]|].
          case_eq (test0 (filter_binding a β1 f)).
          -- intros T;apply test0_spec,KA_αKA in T as -> ;replace e_zero with zero by reflexivity.
             rewrite left_absorbing;apply zero_minimal.
          -- intro Iw;apply Σ_bigger,in_map_iff;exists (β1,(N',t',0));split;[reflexivity|].
             apply factors_In.
             ++ apply test0_false in Iw as (w&Iw).
                apply filter_binding_lang in Iw as (Iw&<-);[|assumption].
                apply binding_finite_bound_size;tauto.
             ++ apply factors_prod in Iβ as <-;reflexivity.
        * rewrite <- eq2'.
          etransitivity;[apply proper_prod_inf;[apply filter_binding_αKA_inf;
                                                [apply Be|rewrite eq1;reflexivity]|reflexivity]|].
          case_eq (test0 (filter_binding a β1 e)).
          -- intros T;apply test0_spec,KA_αKA in T as -> ;replace e_zero with zero by reflexivity.
             rewrite left_absorbing;apply zero_minimal.
          -- intro Iw;apply Σ_bigger,in_map_iff;exists (β1,(N',t',0));split;[reflexivity|].
             apply factors_In.
             ++ apply test0_false in Iw as (w&Iw).
                apply filter_binding_lang in Iw as (Iw&<-);[|assumption].
                apply binding_finite_bound_size;tauto.
             ++ apply factors_prod in Iβ as <-;reflexivity.
    - rewrite <- binding_finite_spec in B1,B2;simpl in B1,B2;rewrite andb_true_iff in B1,B2;
        repeat rewrite binding_finite_spec in B1,B2;destruct B1 as (Be&Be'),B2 as (Bf,Bf').
      simpl;rewrite IHeq1,IHeq2;reflexivity||assumption.
    - assert (is_binding_finite f /\ is_binding_finite e) as (Bf&Be)
          by (repeat rewrite <- binding_finite_spec in *;simpl in *;rewrite andb_true_iff in *;tauto).
      pose proof (IHeq Bf Be) as eq';clear IHeq;simpl.
      apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g Ig;
        apply in_map_iff in Ig as ((β1&β2)&<-&Iβ);simpl;
          destruct (factors_open_balanced Iβ) as (N'&t'&->&Lβ).
      + etransitivity;[apply proper_prod_inf;
                       [apply proper_prod_inf;
                        [apply filter_binding_αKA_inf;
                         [apply B2
                         |rewrite eq;reflexivity]
                        |rewrite eq';reflexivity]
                       |rewrite eq;reflexivity]|].
        case_eq (test0 (filter_binding a β1 (f⋆))).
        * intros T;apply test0_spec,KA_αKA in T as -> ;replace e_zero with zero by reflexivity.
           repeat rewrite left_absorbing;apply zero_minimal.
        * intro Iw;apply Σ_bigger,in_map_iff;exists (β1,(N',t',0));split;[reflexivity|].
          apply factors_In.
          -- apply test0_false in Iw as (w&Iw).
             apply filter_binding_lang in Iw as (Iw&<-);[|assumption].
             transitivity (sizeExpr (f⋆));[|reflexivity].
             apply binding_finite_bound_size;tauto.
          -- apply factors_prod in Iβ as <-;reflexivity.
      + etransitivity;[apply proper_prod_inf;
                       [apply proper_prod_inf;
                        [apply filter_binding_αKA_inf;
                         [apply B1
                         |rewrite <- eq;reflexivity]
                        |rewrite <- eq';reflexivity]
                       |rewrite <- eq;reflexivity]|].
        case_eq (test0 (filter_binding a β1 (e⋆))).
        * intros T;apply test0_spec,KA_αKA in T as -> ;replace e_zero with zero by reflexivity.
           repeat rewrite left_absorbing;apply zero_minimal.
        * intro Iw;apply Σ_bigger,in_map_iff;exists (β1,(N',t',0));split;[reflexivity|].
          apply factors_In.
          -- apply test0_false in Iw as (w&Iw).
             apply filter_binding_lang in Iw as (Iw&<-);[|assumption].
             transitivity (sizeExpr (e⋆));[|reflexivity].
             apply binding_finite_bound_size;tauto.
          -- apply factors_prod in Iβ as <-;reflexivity.
    - destruct H as [b c e h|e f h];[|apply KA_αKA,splitExpr_KA,ax_eq_ax;tauto].
      rewrite splitExpr_act.
      unfold act at 2;simpl;unfold_eqX.
      + destruct_eqX ((N,t,0) : 𝖡) ε.
        * cut (splitExpr b ε e =KA positive e /\ splitExpr c ε e =KA positive e).
          -- intros (T1&T2);apply KA_αKA in T1 as ->.
             etransitivity;[clear T2|symmetry;apply αKA_act,KA_αKA,T2].
             rewrite <- positive_act.
             apply positive_αKA.
             apply ax_eq_ax,αKA_αα;assumption.
          -- split;apply CompletenessKA;rewrite (splitExpr_lang _ _ B1);
               intro u;rewrite positive_lang;split.
             ++ intros (Iu&u1&u2&->&F&_);split;[assumption|].
                intro hyp;apply app_eq_nil in hyp as (->&_);apply F;reflexivity.
             ++ intros (Iu&Nu);split;[assumption|exists u,[];rewrite app_nil_r;repeat assumption||split].
                apply h,Iu.
             ++ intros (Iu&u1&u2&->&F&_);split;[assumption|].
                intro hyp;apply app_eq_nil in hyp as (->&_);apply F;reflexivity.
             ++ intros (Iu&Nu);split;[assumption|exists u,[];rewrite app_nil_r;repeat assumption||split].
                apply h,Iu.
        * destruct (@splitExpr_zero b (N,t,0) e B1) as [E1|E1];
            [reflexivity|intro;apply h|exfalso;apply N0,E1|].
          destruct (@splitExpr_zero c (N,t,0) e B1) as [E2|E2];
            [reflexivity|intro;apply h|exfalso;apply N0,E2|].
          apply KA_αKA in E1 as ->.
          etransitivity;[|symmetry;apply αKA_act,KA_αKA,E2].
          reflexivity.
      + destruct_eqX ((N,t,0) : 𝖡) ε.
        * cut (splitExpr b ε e =KA positive e /\ splitExpr c ε e =KA positive e).
          -- intros (T1&T2);apply KA_αKA in T2 as ->.
             etransitivity;[clear T1|symmetry;apply αKA_act,KA_αKA,T1].
             rewrite <- positive_act.
             apply positive_αKA.
             apply ax_eq_ax,αKA_αα;assumption.
          -- split;apply CompletenessKA;rewrite (splitExpr_lang _ _ B1);
               intro u;rewrite positive_lang;split.
             ++ intros (Iu&u1&u2&->&F&_);split;[assumption|].
                intro hyp;apply app_eq_nil in hyp as (->&_);apply F;reflexivity.
             ++ intros (Iu&Nu);split;[assumption|exists u,[];rewrite app_nil_r;repeat assumption||split].
                apply h,Iu.
             ++ intros (Iu&u1&u2&->&F&_);split;[assumption|].
                intro hyp;apply app_eq_nil in hyp as (->&_);apply F;reflexivity.
             ++ intros (Iu&Nu);split;[assumption|exists u,[];rewrite app_nil_r;repeat assumption||split].
                apply h,Iu.
        * destruct (@splitExpr_zero b (N,t,0) e B1) as [E1|E1];
            [reflexivity|intro;apply h|exfalso;apply N1,E1|].
          destruct (@splitExpr_zero c (N,t,0) e B1) as [E2|E2];
            [reflexivity|intro;apply h|exfalso;apply N1,E2|].
          apply KA_αKA in E2 as ->.
          etransitivity;[|symmetry;apply αKA_act,KA_αKA,E1].
          reflexivity.
      + apply ax_eq_ax,αKA_αα;intros u Iu.
        apply splitExpr_lang in Iu as (Iu&_);[|assumption].
        apply h,Iu.
    - destruct H as [e f|e f].
      + assert (eq1 : e · f <=α f) by apply eq;clear eq.
        pose proof B2 as Bf;clear B2.
        apply binding_finite_spec in B1;simpl in B1;apply andb_true_iff in B1 as (B&B').
        rewrite B' in B;clear B';simpl in B.
        rewrite andb_true_r in B.
        case_eq (test0 f).
        * intro T;transitivity zero;[|symmetry];apply KA_αKA,splitExpr_test0;simpl;
            rewrite T;reflexivity.
        * intro Tf;rewrite Tf in B.
          apply andb_true_iff in B as (Be&Sq');rewrite binding_finite_spec in Be.
          assert (Be' : is_binding_finite (e⋆))
            by (rewrite <- binding_finite_spec in *;simpl;rewrite Be,Sq';reflexivity);clear Sq'.
          cut (splitExpr a (N, t, 0) (e ⋆ · f) <=α splitExpr a (N, t, 0) f);[intro h;apply h|].
          assert (eq2 : forall N t, splitExpr a (N, t, 0) (e · f) <=α splitExpr a (N, t, 0) f)
            by (apply IHeq;try assumption||rewrite <- binding_finite_spec in *;simpl;
                rewrite Be,Bf,andb_true_r,orb_true_r;reflexivity).
          simpl;rewrite Tf.
          rewrite Σ_distr_r,map_map.
          apply inf_join_inf;apply Σ_bounded;intros g Ig;
            apply in_map_iff in Ig as ((β1,β2)&<-&Iβ);simpl.
          -- case_eq (test0 (filter_binding a β1 (e⋆)));
               [intros T;apply test0_spec in T;replace e_zero with zero in T by reflexivity;
                apply KA_αKA in T as ->;repeat rewrite left_absorbing;apply zero_minimal|].
             intro Sqβ1.
             case_eq (test0 e);intro Te;
               [apply (splitExpr_test0 a β2),KA_αKA in Te as -> ;
                repeat rewrite left_absorbing||rewrite right_absorbing;apply zero_minimal|].
             apply test0_false in Sqβ1 as (u&Sqβ1).
             apply filter_binding_lang in Sqβ1 as (Sqβ1&E);[|assumption].
             apply (is_binding_finite_bindings Be' a),(binding_finite_sqExpr_star Be') in Sqβ1;
               rewrite E in *;clear E u.
             transitivity ((filter_binding a β1 (e ⋆) · splitExpr a β2 e) · f).
             ++ repeat rewrite <- (mon_assoc _ _ _).
                apply proper_prod_inf;[reflexivity|].
                apply proper_prod_inf;[reflexivity|].
                apply ka_star_left_ind,eq1.
             ++ pose proof (factors_prod Iβ) as E.
                apply product_square_close_balanced in E;[|assumption|reflexivity].
                destruct E as (N1&N2&N3&t1&t2&t3&E1&->&E&L1&->&hyp).
                replace N3 with N in * by (inversion E;reflexivity).
                replace t3 with t in * by (inversion E;reflexivity).
                clear E N3 t3.
                destruct hyp as [(->&hyp)|(->&->&->&->&h1&h2)].
                ** rewrite (KA_αKA_inf (filter_binding_star a β1 Be')).
                   rewrite <- (mon_assoc _ _ _).
                   transitivity ((Σ (map (fun β => filter_binding a β e) (lower_squares β1)) ⋆
                                    · splitExpr a (N, t, 0) f));
                     [apply proper_prod_inf;
                      [reflexivity|rewrite <- eq2;simpl;rewrite Te,Tf;simpl;apply inf_cup_left]|].
                   apply ka_star_left_ind.
                   rewrite Σ_distr_r,map_map.
                   apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as (β1'&<-&Iβ').
                   etransitivity;[|apply eq2].
                   simpl;etransitivity;[|rewrite Te,Tf;apply inf_cup_right].
                   case_eq (test0 (filter_binding a β1' e));
                     [intros T;apply test0_spec,KA_αKA in T as -> ;
                      replace e_zero with zero by reflexivity;
                      repeat rewrite left_absorbing;apply zero_minimal|].
                   intros sβ1;apply Σ_bigger,in_map_iff;exists (β1',(N,t,0));split;[reflexivity|].
                   apply factors_In.
                   --- apply test0_false in sβ1 as (u&Iu).
                       apply filter_binding_lang in Iu as (Iu&<-);[|assumption].
                       apply binding_finite_bound_size;tauto.
                   --- rewrite <- (factors_prod Iβ) at 1.
                       rewrite prod_assoc.
                       apply lower_squares_spec in Iβ' as (_&->);[|assumption].
                       apply (factors_prod Iβ).
                ** clear L1.
                   assert (filter_binding a β1 (e⋆)
                           <=α Σ (map (fun b => filter_binding a b e)
                                     (lower_squares (N, false, N)))⋆
                              · (filter_binding a β1 e) · e⋆) as ->.
                   --- apply KA_αKA_inf,CompletenessKA_inf.
                       intros u Iu.
                       pose proof Iu as Eu.
                       apply filter_binding_lang in Eu as (_&Eu);[|assumption].
                       apply (ax_inf_lang_incl (filter_binding_star a β1 Be')) in Iu.
                       assert
                         (eq3: Σ (map (fun b : nat * bool * nat => filter_binding a b e) (lower_squares β1)) ⋆
                               =KA (filter_binding a β1 e ∪ Σ (map (fun b => filter_binding a b e)
                                                                   (lower_squares (N, false, N)))) ⋆)
                         by (etransitivity;[apply ax_eq_star,algebra.Σ_equivalent;
                                            rewrite h1;reflexivity|reflexivity]).
                       apply soundness in eq3;apply eq3 in Iu;clear eq3.
                       apply (soundness (star_join _ _)) in Iu.
                       assert (eq3 : ⟦filter_binding a β1 e⋆⟧ ≲ ⟦e⋆⟧)
                         by (apply ax_inf_lang_incl,proper_star_inf,filter_binding_inf,Be).
                       destruct Iu as [Iu|Iu].
                       +++ destruct Iu as ([|]&Iu).
                           *** exfalso;rewrite Iu,E1 in Eu;discriminate.
                           *** destruct Iu as (u1&u2&->&Iu1&Iu2).
                               exists u1,u2;split;[reflexivity|];split.
                               ---- exists [],u1;split;[reflexivity|].
                                    split;[exists 0;reflexivity|assumption].
                               ---- apply eq3;exists n;tauto.
                       +++ destruct Iu as (u1&u2'&->&Iu1&[]&Iu2).
                           *** exfalso.
                               rewrite Iu2 in *;clear Iu2 u2'.
                               rewrite app_nil_r in *.
                               cut (β1 ∈ lower_squares (N,false,N)).
                               ---- intro F;apply lower_squares_spec in F as (_&F);[|reflexivity].
                                    revert F;rewrite E1;unfold prod_binding.
                                    destruct_ltb N N;[discriminate|lia].
                               ---- revert Be Iu1;rewrite <- Eu;clear;intro Be.
                                    intros (n&Iu);revert u1 Iu;induction n;intros u Iu.
                                    ++++ rewrite Iu;apply lower_squares_spec;[reflexivity|].
                                         split;[reflexivity|].
                                         apply prod_unit_l.
                                    ++++ destruct Iu as (u1&u2&->&Iu&Ih);rewrite 𝗙_app.
                                         apply Σ_lang in Iu as (g&Ig&Iu).
                                         apply in_map_iff in Ig as (β&<-&Iβ).
                                         apply filter_binding_lang in Iu as (_&<-);[|assumption].
                                         apply IHn in Ih.
                                         apply lower_squares_spec in Iβ as (Sq&P);[|reflexivity].
                                         apply lower_squares_spec in Ih as (Sq'&P');[|reflexivity].
                                         apply lower_squares_spec;[|split].
                                         **** reflexivity.
                                         **** rewrite <- prod_binding_maxBind by assumption.
                                              destruct (maxBind_square_disj Sq Sq')
                                                as [-> | ->];assumption.
                                         **** rewrite <- prod_assoc,P',P;reflexivity.
                           *** destruct Iu2 as (?&u4&->&(u2&u3&->&Iu2&Iu3)&Iu4).
                               exists (u1++u2),(u3++u4);split;[repeat rewrite app_ass;reflexivity|split].
                               ---- exists u1,u2;tauto.
                               ---- revert Be Iu3 Iu4;clear;intros.
                                    cut ( ⟦ Σ (map (fun b => filter_binding a b e)
                                                   (lower_squares (N, false, N))) ⋆
                                              · (filter_binding a β1 e ·
                                              Σ (map (fun b  => filter_binding a b e)
                                                     (lower_squares (N, false, N)))
                                              ⋆ )⋆⟧(u3 ++ u4));[|exists u3,u4;split;[|split;[|exists n]];tauto].
                                    revert Be;clear;intro.
                                    generalize (u3++u4);apply ax_inf_lang_incl.
                                    transitivity ( e ⋆ · ( e · e⋆ )⋆).
                                    ++++ repeat apply proper_prod_inf || apply proper_star_inf.
                                         **** apply Σ_bounded;intros g Ig.
                                              apply in_map_iff in Ig as (x&<-&Ix).
                                              rewrite filter_binding_inf by assumption.
                                              reflexivity.
                                         **** rewrite filter_binding_inf by assumption;reflexivity.
                                         **** apply Σ_bounded;intros g Ig.
                                              apply in_map_iff in Ig as (x&<-&Ix).
                                              rewrite filter_binding_inf by assumption.
                                              reflexivity.
                                    ++++ transitivity (e⋆·e⋆⋆).
                                         **** repeat apply proper_prod_inf || apply proper_star_inf;
                                                try reflexivity.
                                              etransitivity;[|apply ka_star_unfold].
                                              apply inf_cup_right.
                                         **** apply ax_eq_inf.
                                              etransitivity;
                                                [apply proper_prod;[reflexivity
                                                                   |symmetry;apply ka_star_star]|].
                                              apply ka_star_dup.
                   --- rewrite (KA_αKA_inf (splitExpr_inf _ _ Be)).
                       repeat rewrite <- (mon_assoc _ _ _).
                       rewrite eq1,(ka_star_left_ind eq1).
                       etransitivity;
                         [apply proper_prod_inf;[reflexivity|apply proper_prod_inf;[|reflexivity]];
                          apply KA_αKA_inf,(@filter_binding_splitExpr _ _ _ (N,true,0)) |].
                       +++ assumption.
                       +++ discriminate.
                       +++ reflexivity.
                       +++ rewrite E1;reflexivity.
                       +++ right;rewrite E1;split;reflexivity.
                       +++ etransitivity;[apply proper_prod_inf;
                                          [reflexivity|etransitivity;[|apply (eq2 N true)]]|].
                           *** simpl;rewrite Te,Tf;apply inf_cup_left.
                           *** apply ka_star_left_ind.
                               etransitivity;[|apply (eq2 N true)].
                               etransitivity;[|simpl;rewrite Te,Tf;apply inf_cup_right].
                               rewrite Σ_distr_r,map_map.
                               apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as (β&<-&Iβ').
                               case_eq (test0 (filter_binding a β e));
                                 [intros T;apply test0_spec,KA_αKA in T as -> ;
                                  replace e_zero with zero by reflexivity;
                                  repeat rewrite left_absorbing;apply zero_minimal|].
                               intros sβ1;apply Σ_bigger,in_map_iff;exists (β,(N,true,0)).
                               split;[reflexivity|].
                               apply factors_In.
                               ---- apply test0_false in sβ1 as (u&Iu).
                                    apply filter_binding_lang in Iu as (Iu&<-);[|assumption].
                                    apply binding_finite_bound_size;tauto.
                               ---- pose proof Iβ' as E;
                                      apply lower_squares_spec in E as (S&E);[|reflexivity].
                                    apply factors_prod in Iβ.
                                    revert E;destruct β as ((n,t),m).
                                    rewrite S;unfold d_binding;simpl.
                                    unfold prod_binding;destruct_ltb n N;
                                      [destruct_ltb N n;[replace n with N in * by lia|]|].
                                    ++++ rewrite orb_true_r;reflexivity.
                                    ++++ simpl_nat.
                                         intros heq;exfalso;inversion heq;lia.
                                    ++++ simpl_nat;reflexivity.
          -- case_eq (test0 (filter_binding a β1 (e⋆)));
               [intros T;apply test0_spec in T;replace e_zero with zero in T by reflexivity;
                apply KA_αKA in T as ->;repeat rewrite left_absorbing;apply zero_minimal|].
             intro Sqβ1.
             apply test0_false in Sqβ1 as (u&Sqβ1).
             apply filter_binding_lang in Sqβ1 as (Sqβ1&E);[|assumption].
             pose proof (binding_finite_bound_size a Be' Sqβ1) as Sz.
             apply (is_binding_finite_bindings Be' a),(binding_finite_sqExpr_star Be') in Sqβ1;
               rewrite E in *;clear E u.
             pose proof (factors_prod Iβ) as E.
             apply product_square_close_balanced in E;[|assumption|reflexivity].
             case_eq (test0 e);intro Te;
               [|destruct E as (N1&N2&N3&t1&t2&t3&E1&->&E&L1&->&hyp);
                 replace N3 with N in * by (inversion E;reflexivity);
                 replace t3 with t in * by (inversion E;reflexivity);
                 clear E N3 t3;
                 destruct hyp as [(->&hyp)|(->&->&->&->&h1&h2)]].
             ++ transitivity (filter_binding a β1 un·splitExpr a β2 f).
                ** apply proper_prod_inf;[apply filter_binding_αKA_inf|reflexivity].
                   --- apply binding_finite_spec;reflexivity.
                   --- apply ax_eq_inf,KA_αKA.
                       etransitivity;[|apply ka_zero_star].
                       apply ax_eq_star,test0_spec,Te.
                ** Transparent filter_binding.
                   simpl.
                   Opaque filter_binding.
                   unfold_eqX.
                   --- rewrite left_unit.
                       apply factors_prod in Iβ;rewrite prod_unit_l in Iβ;subst;reflexivity.
                   --- rewrite left_absorbing;apply zero_minimal.
             ++ etransitivity;
                  [apply proper_prod_inf;
                   [apply KA_αKA_inf,filter_binding_star;assumption|reflexivity]|].
                apply ka_star_left_ind.
                rewrite Σ_distr_r,map_map;apply Σ_bounded;intros g Ig.
                apply in_map_iff in Ig as (β'&<-&Iβ').
                etransitivity;[|apply eq2].
                simpl;rewrite Te,Tf;etransitivity;[|apply inf_cup_right].
                apply Σ_bigger,in_map_iff.
                exists (β',(N,t,0));split;[reflexivity|].
                apply factors_In.
                ** etransitivity;[apply lower_squares_size;eassumption|assumption].
                ** apply hyp,Iβ'.
             ++ clear L1.
                assert (filter_binding a β1 (e⋆)
                        <=α Σ (map (fun b => filter_binding a b e) (lower_squares β1))⋆
                           · (filter_binding a β1 e) ·
                           Σ (map (fun b => filter_binding a b e) (lower_squares (N, false, N)))⋆) as ->.
                ** subst;revert Be' Be h1;clear.
                   intros Be' Be h1.
                   apply KA_αKA_inf,CompletenessKA_inf;intros u Iu0.
                   pose proof (ax_inf_lang_incl(filter_binding_star a (N,true,N) Be') Iu0) as Iu.
                   apply filter_binding_lang in Iu0 as (_&Eu);[|assumption].
                   revert h1 Iu;set (L:=lower_squares (N,false,N));intros.
                   assert (Iu' : ⟦ Σ (map (fun b => filter_binding a b e) ((N, true, N)::L)) ⋆ ⟧ u)
                     by (revert Iu;apply soundness,ax_eq_star,algebra.Σ_equivalent;
                         rewrite h1;reflexivity);clear Iu.
                   cut (⟦ (Σ (map (fun b => filter_binding a b e) ((N,true,N)::L)) ⋆ ·
                             filter_binding a (N, true, N) e)
                            · Σ (map (fun b => filter_binding a b e) L) ⋆ ⟧ u);
                     [apply soundness,ax_eq_prod;[apply ax_eq_prod;
                                                  [apply ax_eq_star,algebra.Σ_equivalent;
                                                   rewrite h1|]|];reflexivity|].
                   clear h1.
                   assert (h: forall β,β ∈ L -> β⋅(N,false,N)=(N,false,N))
                     by (unfold L;intros;apply lower_squares_spec;reflexivity||tauto).
                   destruct Iu' as (n&Iu);revert u Iu Eu;induction n;intros u Iu Eu.
                   --- exfalso;rewrite Iu in Eu;discriminate.
                   --- destruct Iu as (u1&u2&->&Iu1&Iu2).
                       assert (hyp : ⟦ Σ (map (fun b=> filter_binding a b e) ((N, true, N) :: L))⋆ ⟧ u2)
                         by (exists n;assumption).
                       assert (EL : (N,true,N)::L ≈ ε::(N,true,N)::L)
                         by (intro b;split;[intro;now right|intros [<-|?];[right|assumption]];
                             unfold L;apply lower_squares_spec;[|rewrite prod_unit_l;split];
                             reflexivity).
                       apply (binding_prod_lower_squares Be') in hyp;rewrite <- EL in hyp.
                       destruct hyp as [ E | I].
                       +++ symmetry in E.
                           apply IHn in E as (?&v3&->&(v1&v2&->&(n1&Iv1)&Iv2)&Iv3);[|assumption].
                           exists (u1++v1++v2),v3.
                           repeat rewrite app_ass;split;[reflexivity|split;[|assumption]].
                           exists (u1++v1),v2.
                           repeat rewrite app_ass;split;[reflexivity|split;[|assumption]].
                           exists (S n1),u1,v1.
                           repeat rewrite app_ass;split;[reflexivity|split;[assumption|assumption]].
                       +++ revert Eu;rewrite 𝗙_app;intros Eu.
                           apply Σ_lang in Iu1 as (g&Ig&Iu1).
                           apply in_map_iff in Ig as (β&<-&Iβ).
                           apply filter_binding_lang in Iu1 as (Iu1&<-);[|assumption].
                           assert (F : ~ (N,true,N)∈ L)
                             by (unfold L;intro F;
                                 apply lower_squares_spec in F as (_&F);[|reflexivity];
                                 revert F;unfold prod_binding;destruct_ltb N N;[discriminate|lia]).
                           exists u1,u2;split;[reflexivity|split;[|]].
                           *** exists [],u1;split;[reflexivity|split;[exists 0;reflexivity|]].
                               apply filter_binding_lang;[assumption|split;[assumption|]].
                               destruct Iβ as [<-|Iβ];[reflexivity|exfalso].
                               apply F; unfold L in *;apply lower_squares_spec;[reflexivity|].
                               split;[reflexivity|].
                               rewrite <- Eu,<- prod_assoc.
                               apply lower_squares_spec in I as (_&->);[|reflexivity].
                               apply lower_squares_spec in Iβ as (_&->);[|reflexivity].
                               reflexivity.
                           *** exists n;revert F EL Be Be' I Iu2;clear.
                               intros F EL Be Be';revert u2;induction n;intros u IL Iu.
                               ---- rewrite Iu;reflexivity.
                               ---- destruct Iu as (u1&u2&->&Iu1&Iu2).
                                    rewrite 𝗙_app in IL.
                                    assert (hyp : ⟦ Σ (map (fun b=> filter_binding a b e)
                                                           ((N, true, N) :: L))⋆ ⟧ u2)
                                      by (exists n;assumption).
                                    apply (binding_prod_lower_squares Be') in hyp.
                                    rewrite <- EL in hyp.
                                    apply Σ_lang in Iu1 as (g&Ig&Iu1).
                                    apply in_map_iff in Ig as (β&<-&Iβ).
                                    apply filter_binding_lang in Iu1 as (Iu1&<-);[|assumption].
                                    revert IL;destruct Iβ as [<-|I1].
                                    ++++ intros I;exfalso;apply lower_squares_prod in I as (I&_).
                                         **** apply F,I.
                                         **** reflexivity.
                                         **** destruct hyp as [<-|I2];[reflexivity|].
                                              apply lower_squares_spec in I2;reflexivity||tauto.
                                         **** reflexivity.
                                    ++++ intros I;exists u1,u2;split;[reflexivity|].
                                         split.
                                         **** apply Σ_lang;eexists;split;
                                                [apply in_map_iff;exists (𝗙 a u1);tauto|].
                                              apply filter_binding_lang;tauto.
                                         **** apply IHn,Iu2.
                                              revert I;destruct hyp as [<-|I2];[|intros _;assumption].
                                              intros I;exfalso;apply lower_squares_prod in I as (_&I).
                                              ----- apply F,I.
                                              ----- apply lower_squares_spec in I1;reflexivity||tauto.
                                              ----- reflexivity.
                                              ----- reflexivity.
                ** repeat rewrite <- (mon_assoc _ _ _).
                   transitivity
                     (Σ (map (fun b : nat * bool * nat => filter_binding a b e) (lower_squares β1)) ⋆ ·
                        splitExpr a (N,true,0) f).
                   --- apply proper_prod_inf;[reflexivity|].
                       transitivity (filter_binding a β1 e · splitExpr a (N, false, 0) f).
                       +++ apply proper_prod_inf;[reflexivity|].
                           apply ka_star_left_ind.
                           rewrite Σ_distr_r,map_map;apply Σ_bounded;intros g Ig.
                           apply in_map_iff in Ig as (β&<-&Iβ').
                           etransitivity;[|apply eq2].
                           simpl;rewrite Te,Tf;etransitivity;[|apply inf_cup_right].
                           apply Σ_bigger,in_map_iff.
                           exists (β,(N,false,0));split;[reflexivity|];apply factors_In.
                           *** etransitivity;[|apply Sz].
                               rewrite E1,lower_squares_size;[ | |apply Iβ'];reflexivity.
                           *** apply h2,Iβ'.
                       +++ etransitivity;[|apply eq2].
                           simpl;rewrite Te,Tf;etransitivity;[|apply inf_cup_right].
                           apply Σ_bigger,in_map_iff.
                           exists (β1,(N,false,0));split;[reflexivity|];apply factors_In.
                           *** apply Sz.
                           *** rewrite E1;unfold prod_binding;destruct_ltb N N;[reflexivity|lia].
                   --- apply ka_star_left_ind.
                       rewrite Σ_distr_r,map_map;apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (β&<-&Iβ').
                       etransitivity;[|apply eq2].
                       simpl;rewrite Te,Tf;etransitivity;[|apply inf_cup_right].
                       apply Σ_bigger,in_map_iff.
                       exists (β,(N,true,0));split;[reflexivity|];apply factors_In.
                       *** etransitivity;[|apply Sz].
                           apply lower_squares_size;assumption.
                       *** cut (β1⋅(N,true,0) = (N,true,0)).
                           ---- intro E;rewrite <- E at 1.
                                rewrite prod_assoc.
                                apply lower_squares_spec in Iβ' as (_&->);assumption.
                           ---- rewrite E1;unfold prod_binding;destruct_ltb N N;[reflexivity|lia].
      + assert (eq1 : e · f <=α e) by apply eq;clear eq.
        pose proof B2 as Be;clear B2.
        apply binding_finite_spec in B1;simpl in B1;apply andb_true_iff in B1 as (B&B').
        rewrite B' in B;clear B';simpl in B.
        rewrite orb_false_r in B.
        case_eq (test0 e);intro Te.
        * transitivity zero;[|symmetry];apply KA_αKA,splitExpr_test0;simpl;rewrite Te;reflexivity.
        * rewrite Te in B;apply andb_true_iff in B as (Bf&Sq');rewrite binding_finite_spec in Bf.
          assert (Bf' : is_binding_finite (f⋆))
            by (rewrite <- binding_finite_spec in *;simpl;rewrite Bf,Sq';reflexivity);clear Sq'.
          cut (splitExpr a (N, t, 0) (e · f⋆) <=α splitExpr a (N, t, 0) e);[intro h;apply h|].
          assert (eq2 : forall N t, splitExpr a (N, t, 0) (e · f) <=α splitExpr a (N, t, 0) e)
            by (apply IHeq;try assumption||rewrite <- binding_finite_spec in *;simpl;
                rewrite Be,Bf,andb_true_r,orb_true_r;reflexivity).
          simpl;rewrite Te;simpl.
          apply inf_join_inf.
          -- apply ka_star_right_ind;etransitivity;[|apply eq2].
             case_eq (test0 f);[|simpl;intros ->;rewrite Te;apply inf_cup_left].
             intro Tf;apply test0_spec,KA_αKA in Tf;rewrite Tf at 1.
             replace e_zero with zero by reflexivity;rewrite right_absorbing.
             apply zero_minimal.
          -- apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as ((β1,β2)&<-&Iβ);simpl.
             rewrite Σ_distr_l,map_map.
             apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as ((β3,β4)&<-&Iβ');simpl.
             case_eq (test0 (filter_binding a β3 (f⋆)));
               [intros T;apply test0_spec in T;replace e_zero with zero in T by reflexivity;
                apply KA_αKA in T as ->;repeat rewrite left_absorbing||rewrite right_absorbing;
                apply zero_minimal|].
             intro Sqβ3.
             apply test0_false in Sqβ3 as (u&Sqβ3).
             apply filter_binding_lang in Sqβ3 as (Sqβ3&E);[|assumption].
             pose proof (binding_finite_bound_size a Bf' Sqβ3) as Sz3;simpl in Sz3.
             apply (is_binding_finite_bindings Bf' a),(binding_finite_sqExpr_star Bf') in Sqβ3;
               rewrite E in *;clear E u.
             case_eq (test0 (filter_binding a β1 e));
               [intros T;apply test0_spec in T;replace e_zero with zero in T by reflexivity;
                apply KA_αKA in T as ->;repeat rewrite left_absorbing||rewrite right_absorbing;
                apply zero_minimal|].
             intro Sz1.
             apply test0_false in Sz1 as (u&Sz1).
             apply filter_binding_lang in Sz1 as (Sz1&E);[|assumption].
             apply (binding_finite_bound_size a Be) in Sz1;rewrite E in Sz1;clear E u.
             destruct (factors_open_balanced Iβ) as (N'&t'&->&L).
             apply factors_prod in Iβ'.
             apply product_square_close_balanced in Iβ';[|assumption|reflexivity].
             destruct Iβ' as (N3&N4&N0&t3&t4&t0&E3&->&E0&L2&->&hyp).
             replace N0 with N' in * by (inversion E0;reflexivity).
             replace t0 with t' in * by (inversion E0;reflexivity);clear N0 t0 E0.
             case_eq (test0 f);[|intro Tf;destruct hyp as [(->&hyp)|(->&->&->&->&h1&h2)]].
             ++ clear;intro Tf.
                apply (splitExpr_test0 a (N',t4,0)),KA_αKA in Tf as ->.
                repeat rewrite left_absorbing||rewrite right_absorbing;apply zero_minimal.
             ++ repeat rewrite (mon_assoc _ _ _).
                transitivity (splitExpr a (N, t, 0) e · f ⋆).
                ** apply proper_prod_inf;[|reflexivity].
                   transitivity (filter_binding a (β1⋅β3) e · splitExpr a (N', t', 0) f).
                   --- apply proper_prod_inf;[|reflexivity].
                       etransitivity;[|apply filter_binding_αKA_inf;
                                       [assumption|apply ka_star_right_ind,eq1]].
                       Transparent filter_binding.
                       remember (f⋆) as g;simpl;apply Σ_bigger;rewrite Heqg in *;clear g Heqg.
                       Opaque filter_binding.
                       apply in_map_iff;exists (β1,β3);split;[reflexivity|].
                       apply factors_In;[assumption|reflexivity].
                   --- etransitivity;[|apply eq2].
                       simpl;rewrite Te,Tf;etransitivity;[|apply inf_cup_right].
                        case_eq (test0 (filter_binding a (β1⋅β3) e));
                          [intros T;apply test0_spec in T;replace e_zero with zero in T
                             by reflexivity;
                           apply KA_αKA in T as ->;repeat rewrite left_absorbing
                                                ||rewrite right_absorbing;
                           apply zero_minimal|].
                        intro Sz.
                        apply test0_false in Sz as (u&Sz).
                        apply filter_binding_lang in Sz as (Sz&E);[|assumption].
                        apply (binding_finite_bound_size a Be) in Sz;rewrite E in Sz;clear E u.
                        
                        apply Σ_bigger,in_map_iff.
                        exists (β1⋅β3,(N',t',0));split;[reflexivity|].
                        apply factors_In;[assumption|].
                        rewrite <- prod_assoc.
                        rewrite hyp;[|apply lower_squares_spec;[|split];try assumption].
                       +++ eapply factors_prod,Iβ.
                       +++ rewrite <- prod_binding_maxBind by assumption;apply maxBind_idem.
                ** apply ka_star_right_ind.
                   etransitivity;[|apply eq2].
                   simpl;rewrite Te,Tf;apply inf_cup_left.
             ++ clear L2;repeat rewrite (mon_assoc _ _ _).
                transitivity (splitExpr a (N, t, 0) e · f ⋆).
                ** apply proper_prod_inf;[|reflexivity].
                   transitivity (filter_binding a (β1⋅β3) e · splitExpr a (N', false, 0) f).
                   --- apply proper_prod_inf;[|reflexivity].
                       etransitivity;[|apply filter_binding_αKA_inf;
                                       [assumption|apply ka_star_right_ind,eq1]].
                       Transparent filter_binding.
                       remember (f⋆) as g;simpl;apply Σ_bigger;rewrite Heqg in *;clear g Heqg.
                       Opaque filter_binding.
                       apply in_map_iff;exists (β1,β3);split;[reflexivity|].
                       apply factors_In;[assumption|reflexivity].
                   --- etransitivity;[|apply eq2].
                       simpl;rewrite Te,Tf;etransitivity;[|apply inf_cup_right].
                        case_eq (test0 (filter_binding a (β1⋅β3) e));
                          [intros T;apply test0_spec in T;replace e_zero with zero in T
                             by reflexivity;
                           apply KA_αKA in T as ->;repeat rewrite left_absorbing
                                                ||rewrite right_absorbing;
                           apply zero_minimal|].
                        intro Sz.
                        apply test0_false in Sz as (u&Sz).
                        apply filter_binding_lang in Sz as (Sz&E);[|assumption].
                        apply (binding_finite_bound_size a Be) in Sz;rewrite E in Sz;clear E u.
                        
                        apply Σ_bigger,in_map_iff.
                        exists (β1⋅β3,(N',false,0));split;[reflexivity|].
                        apply factors_In;[assumption|].
                        rewrite <- prod_assoc.
                        rewrite E3;unfold prod_binding at 2;destruct_ltb N' N';[|lia].
                        eapply factors_prod,Iβ.
                ** apply ka_star_right_ind.
                   etransitivity;[|apply eq2].
                   simpl;rewrite Te,Tf;apply inf_cup_left.
  Qed.

  Lemma splitExpr_αKA_inf a β e f :
    is_binding_finite f -> c_binding β = 0
    -> e <=α f -> splitExpr a β e <=α splitExpr a β f.
  Proof.
    intros Bf h;unfold ax_inf;intro E.
    rewrite <- (@splitExpr_αKA a β (e∪f) f Bf h E) at 2;reflexivity.
  Qed.

  Lemma split_binding_is_binding_finite a β e f1 f2 :
    is_binding_finite e -> (f1,f2) ∈ (split_binding a β e) ->
    is_binding_finite f1 /\ is_binding_finite f2.
  Proof.
    intros Be;repeat rewrite <- binding_finite_spec;revert β f1 f2;induction_bin_fin e Be;
      intros β f1 f2;simpl;try tauto.
    - unfold_eqX;simpl;[|tauto].
      intros [h|h];inversion h;subst;split;reflexivity.
    - simpl_In;intros [I|I].
      + eapply IHe1,I.
      + eapply IHe2,I.
    - rewrite T;simpl_In.
      intros [I|I].
      + apply in_map_iff in I as ((g1&g2)&E&Ig);inversion E;clear E;subst.
        simpl;apply IHe1 in Ig as (->&->);split;[tauto|].
        apply binding_finite_spec in B2 as ->;apply orb_true_r.
      + apply in_flat_map in I as ((β1&β2)&_&I2).
        apply in_map_iff in I2 as ((g1&g2)&E&I);inversion E;clear E;subst.
        simpl;apply IHe2 in I as (->&->).
        split;[|reflexivity].
        eapply is_binding_finite_filter_binding,binding_finite_spec in B1 as ->.
        apply orb_true_r.
    - rewrite T;simpl;tauto.
    - intro I; apply in_flat_map in I as ((β1&β2)&_&I2).
      apply in_map_iff in I2 as ((g1&g2)&E&I);inversion E;clear E;subst.
      simpl;apply IHe in I as (->&->).
      apply sqExpr_bindings_finite_star in Sq as B1.
      pose proof B1 as B2.
      apply binding_finite_spec in B2;simpl in B2;rewrite B2;split;[|apply orb_true_r]. 
      eapply is_binding_finite_filter_binding,binding_finite_spec in B1 as ->.
      apply orb_true_r.
  Qed.


  Lemma sqExpr_is_binding_finite_positive_star e :
    sqExpr e -> is_binding_finite (positive (e⋆)).
  Proof.
    intro Sq;apply sqExpr_bindings_finite_star in Sq.
    eapply is_binding_finite_ax_eq in Sq;[|apply KA_αKA,positive_inf].
    rewrite <- binding_finite_spec in *;simpl in Sq;apply andb_true_iff in Sq;tauto.
  Qed.

  Lemma split_binding_support a β e f1 f2 :
    (f1,f2)∈ (split_binding a β e) -> ⌊f1⌋++⌊f2⌋ ⊆ ⌊e⌋.
  Proof.
    revert β f1 f2;induction e;intros β f1 f2;simpl;try tauto.
    - simpl_In;intros [I|I];[etransitivity;[eapply IHe1,I|]|etransitivity;[eapply IHe2,I|]];
        unfold support;simpl;intro;simpl_In;tauto.
    - destruct (test0 e1||test0 e2);[simpl;tauto|].
      simpl_In;intros [I|I].
      + apply in_map_iff in I as ((g1,g2)&heq&Ig);symmetry in heq;inversion heq;clear heq;subst.
        unfold support in *;simpl.
        rewrite <- app_ass.
        apply IHe1 in Ig as ->;reflexivity.
      + apply in_flat_map in I as ((β1,β2)&Iβ&If).
        apply in_map_iff in If as ((g1&g2)&heq&If);symmetry in heq;inversion heq;clear heq;subst.
        rewrite support_prod,filter_binding_support,app_ass.
        apply IHe2 in If as ->;reflexivity.
    - intros If;apply in_flat_map in If as ((β1&β2)&Iβ&If).
      apply in_map_iff in If as ((g1&g2)&heq&Ig);symmetry in heq;inversion heq;clear heq;subst.
      repeat rewrite support_prod;rewrite filter_binding_support.
      rewrite app_ass,<-(app_ass ⌊g1⌋).
      apply IHe in Ig as ->;repeat rewrite support_star;repeat rewrite app_idem;reflexivity.
    - unfold_eqX;[|simpl;tauto].
      intros [heq|heq];inversion heq;subst.
      rewrite app_nil_r;reflexivity.
  Qed.

  Lemma is_binding_finite_splitExpr a β e :
    is_binding_finite e -> is_binding_finite (splitExpr a β e).
  Proof. intro Be;eapply is_binding_finite_ax_inf,KA_αKA_inf,splitExpr_inf;assumption. Qed.

  Definition splitAct c a β e :=
    Σ (map (fun p => ([(a,c)]∙fst p)·snd p) (split_binding a β e)).

  Lemma splitAct_support c a β e :
    ⌊splitAct c a β e⌋ ⊆ c::a::⌊e⌋.
  Proof.
    unfold splitAct;intros b Ib.
    rewrite <- Σ_support in Ib.
    apply In_support_list in Ib as (f&If&Ib).
    apply in_map_iff in If as ((e1&e2)&<-&Ie).
    apply split_binding_support in Ie as <-.
    rewrite support_prod,support_action in Ib;simpl in Ib.
    simpl_In in *;destruct Ib as [Ib|Ib].
    - rewrite In_act_lists in Ib;revert Ib.
      unfold act;simpl;unfold_eqX;tauto.
    - tauto.
  Qed.
    
  Lemma splitAct_act p c a β e :
    p ∙ splitAct c a β e = splitAct (p∙c) (p∙a) β (p∙e).
  Proof.
    unfold splitAct.
    rewrite Σ_act.
    unfold act at 1,act_lists;rewrite map_map.
    rewrite split_binding_act,act_pinv_p.
    unfold act at 6,act_lists;rewrite map_map.
    f_equal;apply map_ext;intros (?&?);simpl.
    rewrite act_prod;f_equal.
    repeat rewrite action_compose.
    apply support_eq_action_eq.
    intros b Ib;repeat rewrite <- action_compose.
    unfold act at 2 3;simpl.
    destruct_eqX b a;[reflexivity|].
    rewrite <- (act_bij p) in N;simpl_eqX.
    destruct_eqX b c;[reflexivity|].
    rewrite <- (act_bij p) in N0;simpl_eqX.
    reflexivity.
  Qed.
    
  Lemma splitAct_test0 c a β e : test0 e = true -> splitAct c a β e = 𝟬.
  Proof. intro T;unfold splitAct;rewrite (split_binding_test0 _ _ T);reflexivity. Qed.

  Lemma splitAct_lang c a β e :
    is_binding_finite e ->
    ⟦splitAct c a β e⟧ ≃ (fun u => exists u1 u2, u = [(a,c)]∙u1++u2 /\ ⟦e⟧ (u1++u2) /\ u1 <> [] /\ 𝗙 a u1 = β).
  Proof.
    unfold splitAct;intros Be u;rewrite Σ_lang;split;intros Iu.
    - destruct Iu as (?&Ie&Iu);apply in_map_iff in Ie as ((e1&e2)&<-&Ie).
      destruct Iu as (u1&u2&->&Iu1&Iu2).
      apply act_lang in Iu1;simpl in *.
      exists ([(a,c)]∙u1),u2;split;[replace [(a,c)] with ([(a,c)]∗) at 1 by reflexivity;
                               rewrite act_pinv_p;reflexivity|].
      apply (split_binding_lang Be Ie Iu1 Iu2).
    - destruct Iu as (u1&u2&->&Iu&N&<-).
      destruct (split_binding_lang_full a Be Iu N) as (e1&e2&Ie&Iu1&Iu2).
      exists ([(a,c)]∙e1·e2);split.
      + apply in_map_iff;exists (e1,e2);tauto.
      + exists ([(a,c)]∙u1),u2;split;[reflexivity|].
        split;[|assumption].
        apply act_lang;rewrite act_pinv_p;assumption.
  Qed.
    
       
  
  Transparent split_binding.
  Lemma splitAct_αKA c a β e f : is_binding_finite f -> c_binding β = 0 -> c # e -> c # f ->
                                 e =α f -> splitAct c a β e =α splitAct c a β f.
  Proof.
    intros B2 Eβ Fc Ff E;revert β a c Eβ Fc Ff;induction E;intros β a c Eβ F1 F2.
    - reflexivity.
    - symmetry;apply IHE;try assumption.
      apply (is_binding_finite_ax_eq E),B2.
    - destruct (exists_fresh (⌊e⌋++⌊f⌋++⌊g⌋)) as (d&Id).
      assert (d # e /\ d # f /\ d # g) as (Fe&Ff&Fg) by (simpl_In in Id;tauto);clear Id.
      rewrite <- (act_pinv_p [(c,d)] _).
      rewrite <- (act_pinv_p [(c,d)] (splitAct c a β e)).
      apply αKA_act.
      repeat rewrite splitAct_act.
      unfold act at 1 2 4 5;simpl;simpl_eqX.
      rewrite action_invariant.
      + etransitivity;[apply IHE1
                      |etransitivity;
                       [apply IHE2|rewrite action_invariant;[reflexivity|]]];try assumption.
        * apply (is_binding_finite_ax_eq E2),B2.
        * apply elements_inv_act.
          intros b Ib;rewrite support_list_atoms in Ib.
          intros [<-|[<-|F]];tauto.
      + apply elements_inv_act.
        intros b Ib;rewrite support_list_atoms in Ib.
        intros [<-|[<-|F]];tauto.
    - case_eq (test0 (e · e')).
      + intro T;rewrite (splitAct_test0 _ _ _ T),splitAct_test0;[reflexivity|].
        erewrite test0_αKA;[apply T|].
        rewrite E1,E2;reflexivity.
      + intro T1;pose proof T1 as T2.
        erewrite test0_αKA in T2 by (rewrite E1,E2;reflexivity).
        unfold splitAct;simpl.
        simpl in T1,T2;rewrite T1,T2.
        apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g Ig;
          repeat rewrite map_map in Ig||rewrite map_app in Ig;simpl_In in Ig;destruct Ig as [Ig|Ig].
        * apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
          transitivity (splitAct c a β f ·f').
          -- simpl;rewrite E2, (mon_assoc _ _ _).
             apply proper_prod_inf;[|reflexivity].
             rewrite <- IHE1;try assumption.
             ++ apply Σ_bigger,in_map_iff;exists (g1,g2);tauto.
             ++ revert B2;repeat rewrite <- binding_finite_spec;simpl;rewrite T2;simpl.
                rewrite andb_true_iff;tauto.
             ++ revert F1;rewrite support_prod;simpl_In;tauto.
             ++ revert F2;rewrite support_prod;simpl_In;tauto.
          -- rewrite map_app,<- algebra.Σ_app,map_map.
             etransitivity;[|apply inf_cup_left].
             unfold splitAct;rewrite Σ_distr_r,map_map;simpl.
             apply ax_eq_inf,Σ_map_equiv_α;intros (?,?) ?;simpl.
             symmetry;apply mon_assoc.
        * apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
          apply in_flat_map in Ig as ((β1&β2)&Iβ&Ig).
          apply in_map_iff in Ig as ((f1&f2)&heq&If).
          symmetry in heq;inversion heq;clear heq;subst;simpl in *.
          transitivity ([(a, c)] ∙ filter_binding a β1 f · splitAct c a β2 f').
          -- rewrite act_prod,<-(mon_assoc _ _ _).
             apply proper_prod_inf.
             ++ apply αKA_inf_act.
                apply filter_binding_αKA_inf;[|rewrite E1;reflexivity].
                revert B2;repeat rewrite <- binding_finite_spec;simpl;rewrite T2;simpl.
                rewrite andb_true_iff;tauto.
             ++ etransitivity;[|apply ax_eq_inf,IHE2];try assumption.
                ** apply Σ_bigger,in_map_iff;exists (f1,f2);simpl;tauto.
                ** revert B2;repeat rewrite <- binding_finite_spec;simpl;rewrite T2;simpl.
                   rewrite andb_true_iff;tauto.
                ** revert Eβ;apply factors_prod in Iβ as <-;simpl_binding;lia.
                ** revert F1;rewrite support_prod;simpl_In;tauto.
                ** revert F2;rewrite support_prod;simpl_In;tauto.
          -- clear f1 f2 If;unfold splitAct;rewrite Σ_distr_l,map_map.
             assert (Bf: is_binding_finite f) by
                 (revert B2;repeat rewrite <- binding_finite_spec;simpl;rewrite T2;simpl;
                  rewrite andb_true_iff;tauto).
             rewrite map_app,<-algebra.Σ_app;etransitivity;[|apply inf_cup_right].
             apply Σ_bounded;intros g Ig.
             apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
             case_eq (test0 (filter_binding a β1 f));
               [intros T;apply test0_spec,KA_αKA,(αKA_act [(a,c)]) in T as -> ;
                replace ([(a,c)]∙e_zero) with zero by reflexivity;simpl;
                rewrite left_absorbing;apply zero_minimal|intro Iv].
             apply test0_false in Iv as (v&Iv);apply filter_binding_lang in Iv as (Iv&Ev);
               [|assumption].
             eapply binding_finite_bound_size in Iv;[rewrite Ev in Iv;clear v Ev|assumption].
             simpl.
             rewrite (mon_assoc _ _ _),<-act_prod.
             apply Σ_bigger,in_map_iff;exists (filter_binding a β1 f·g1,g2);split;[reflexivity|].
             apply in_flat_map;exists (β1,β2);split.
             ++ apply factors_In;[assumption|eapply factors_prod;eassumption].
             ++ apply in_map_iff;exists (g1,g2);tauto.
        * assert (is_binding_finite e /\ is_binding_finite e') as (Be&Be')
              by (cut (is_binding_finite (e · e'));[repeat rewrite <- binding_finite_spec;simpl;
                                                    rewrite T1;simpl; rewrite andb_true_iff;tauto
                                                   |rewrite is_binding_finite_ax_eq;
                                                    [apply B2|rewrite E1,E2;reflexivity]]).
          apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
          transitivity (splitAct c a β e ·e').
          -- simpl;rewrite <- E2, (mon_assoc _ _ _).
             apply proper_prod_inf;[|reflexivity].
             rewrite IHE1;try assumption.
             ++ apply Σ_bigger,in_map_iff;exists (g1,g2);tauto.
             ++ revert B2;repeat rewrite <- binding_finite_spec;simpl;rewrite T2;simpl.
                rewrite andb_true_iff;tauto.
             ++ revert F1;rewrite support_prod;simpl_In;tauto.
             ++ revert F2;rewrite support_prod;simpl_In;tauto.
          -- rewrite map_app,<- algebra.Σ_app,map_map.
             etransitivity;[|apply inf_cup_left].
             unfold splitAct;rewrite Σ_distr_r,map_map;simpl.
             apply ax_eq_inf,Σ_map_equiv_α;intros (?,?) ?;simpl.
             symmetry;apply mon_assoc.
        * assert (is_binding_finite e /\ is_binding_finite e') as (Be&Be')
              by (cut (is_binding_finite (e · e'));[repeat rewrite <- binding_finite_spec;simpl;
                                                    rewrite T1;simpl; rewrite andb_true_iff;tauto
                                                   |rewrite is_binding_finite_ax_eq;
                                                    [apply B2|rewrite E1,E2;reflexivity]]).
          apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
          apply in_flat_map in Ig as ((β1&β2)&Iβ&Ig).
          apply in_map_iff in Ig as ((f1&f2)&heq&If).
          symmetry in heq;inversion heq;clear heq;subst;simpl in *.
          transitivity ([(a, c)] ∙ filter_binding a β1 e · splitAct c a β2 e').
          -- rewrite act_prod,<-(mon_assoc _ _ _).
             apply proper_prod_inf.
             ++ apply αKA_inf_act.
                apply filter_binding_αKA_inf;[assumption|rewrite E1;reflexivity].
             ++ etransitivity;[|apply ax_eq_inf;symmetry;apply IHE2];try assumption.
                ** apply Σ_bigger,in_map_iff;exists (f1,f2);simpl;tauto.
                ** revert B2;repeat rewrite <- binding_finite_spec;simpl;rewrite T2;simpl.
                   rewrite andb_true_iff;tauto.
                ** revert Eβ;apply factors_prod in Iβ as <-;simpl_binding;lia.
                ** revert F1;rewrite support_prod;simpl_In;tauto.
                ** revert F2;rewrite support_prod;simpl_In;tauto.
          -- clear f1 f2 If;unfold splitAct;rewrite Σ_distr_l,map_map.
             assert (Bf: is_binding_finite f) by
                 (revert B2;repeat rewrite <- binding_finite_spec;simpl;rewrite T2;simpl;
                  rewrite andb_true_iff;tauto).
             rewrite map_app,<-algebra.Σ_app;etransitivity;[|apply inf_cup_right].
             apply Σ_bounded;intros g Ig.
             apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
             case_eq (test0 (filter_binding a β1 e));
               [intros T;apply test0_spec,KA_αKA,(αKA_act [(a,c)]) in T as -> ;
                replace ([(a,c)]∙e_zero) with zero by reflexivity;simpl;
                rewrite left_absorbing;apply zero_minimal|intro Iv].
             apply test0_false in Iv as (v&Iv);apply filter_binding_lang in Iv as (Iv&Ev);
               [|assumption].
             eapply binding_finite_bound_size in Iv;[rewrite Ev in Iv;clear v Ev|assumption].
             simpl.
             rewrite (mon_assoc _ _ _),<-act_prod.
             apply Σ_bigger,in_map_iff;exists (filter_binding a β1 e·g1,g2);split;[reflexivity|].
             apply in_flat_map;exists (β1,β2);split.
             ++ apply factors_In;[assumption|eapply factors_prod;eassumption].
             ++ apply in_map_iff;exists (g1,g2);tauto.
    - unfold splitAct in *;simpl;repeat rewrite map_app,<-algebra.Σ_app.
      rewrite IHE1,IHE2;try reflexivity||assumption;clear IHE1 IHE2.
      + revert B2;repeat rewrite <- binding_finite_spec;simpl.
        rewrite andb_true_iff;tauto.
      + revert F1;rewrite support_join;simpl_In;tauto.
      + revert F2;rewrite support_join;simpl_In;tauto.
      + revert B2;repeat rewrite <- binding_finite_spec;simpl.
        rewrite andb_true_iff;tauto.
      + revert F1;rewrite support_join;simpl_In;tauto.
      + revert F2;rewrite support_join;simpl_In;tauto.
    - assert (Bf : is_binding_finite f)
        by (revert B2;repeat rewrite <- binding_finite_spec;simpl;rewrite andb_true_iff;tauto).
      assert (Be : is_binding_finite e)
        by (eapply is_binding_finite_ax_eq;[apply E|assumption]).
      assert (Be' : is_binding_finite (e⋆))
        by (eapply is_binding_finite_ax_eq;[rewrite E;reflexivity|assumption]).
      assert (IH : forall β, c_binding β = 0 -> splitAct c a β e =α splitAct c a β f)
        by (intros;apply IHE;try assumption);clear IHE.
      unfold splitAct;simpl;repeat rewrite map_app,<-algebra.Σ_app.
      apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g Ig.
      + apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
        apply in_flat_map in Ig as ((β1&β2)&Iβ&Ig).
        apply in_map_iff in Ig as ((f1&f2)&heq&If).
        symmetry in heq;inversion heq;clear heq;subst;simpl in *.
        rewrite act_prod,<- (mon_assoc _ _ _), (mon_assoc _ _ (e⋆)).
        transitivity ([(a, c)] ∙ filter_binding a β1 (f ⋆) · (splitAct c a β2 f · f ⋆)).
        * apply proper_prod_inf.
          -- apply αKA_inf_act,filter_binding_αKA_inf;[assumption|rewrite E;reflexivity].
          -- apply proper_prod_inf;[|rewrite E;reflexivity].
             rewrite <- IH.
             ++ apply Σ_bigger,in_map_iff;exists (f1,f2);tauto.
             ++ revert Eβ;apply factors_prod in Iβ as <-;simpl_binding;lia.
        * clear f1 f2 If;unfold splitAct;rewrite Σ_distr_r,Σ_distr_l,map_map,map_map.
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
          case_eq (test0 (filter_binding a β1 (f⋆)));
            [intros T;apply test0_spec,KA_αKA,(αKA_act [(a,c)]) in T as -> ;
             replace ([(a,c)]∙e_zero) with zero by reflexivity;simpl;
             rewrite left_absorbing;apply zero_minimal|intro Iv].
          apply test0_false in Iv as (v&Iv);apply filter_binding_lang in Iv as (Iv&Ev);
            [|assumption].
          eapply binding_finite_bound_size in Iv;[rewrite Ev in Iv;clear v Ev|assumption].
          simpl; repeat rewrite (mon_assoc _ _ _);rewrite <- act_prod, <- (mon_assoc _ g2 (f⋆));simpl.
          apply Σ_bigger,in_map_iff;exists (filter_binding a β1 (f⋆)·g1,g2·f⋆);split;[reflexivity|].
          apply in_flat_map;exists (β1,β2);split.
          -- apply factors_In;[|eapply factors_prod];eassumption.
          -- apply in_map_iff;exists (g1,g2);tauto.
      + apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
        apply in_flat_map in Ig as ((β1&β2)&Iβ&Ig).
        apply in_map_iff in Ig as ((f1&f2)&heq&If).
        symmetry in heq;inversion heq;clear heq;subst;simpl in *.
        rewrite act_prod,<- (mon_assoc _ _ _), (mon_assoc _ _ (f⋆)).
        transitivity ([(a, c)] ∙ filter_binding a β1 (e ⋆) · (splitAct c a β2 e · e ⋆)).
        * apply proper_prod_inf.
          -- apply αKA_inf_act,filter_binding_αKA_inf;[assumption|rewrite E;reflexivity].
          -- apply proper_prod_inf;[|rewrite E;reflexivity].
             rewrite IH.
             ++ apply Σ_bigger,in_map_iff;exists (f1,f2);tauto.
             ++ revert Eβ;apply factors_prod in Iβ as <-;simpl_binding;lia.
        * clear f1 f2 If;unfold splitAct;rewrite Σ_distr_r,Σ_distr_l,map_map,map_map.
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
          case_eq (test0 (filter_binding a β1 (e⋆)));
            [intros T;apply test0_spec,KA_αKA,(αKA_act [(a,c)]) in T as -> ;
             replace ([(a,c)]∙e_zero) with zero by reflexivity;simpl;
             rewrite left_absorbing;apply zero_minimal|intro Iv].
          apply test0_false in Iv as (v&Iv);apply filter_binding_lang in Iv as (Iv&Ev);
            [|assumption].
          eapply binding_finite_bound_size in Iv;[rewrite Ev in Iv;clear v Ev|assumption].
          simpl; repeat rewrite (mon_assoc _ _ _);rewrite <- act_prod, <- (mon_assoc _ g2 (e⋆));simpl.
          apply Σ_bigger,in_map_iff;exists (filter_binding a β1 (e⋆)·g1,g2·e⋆);split;[reflexivity|].
          apply in_flat_map;exists (β1,β2);split.
          -- apply factors_In;[|eapply factors_prod];eassumption.
          -- apply in_map_iff;exists (g1,g2);tauto.
    - destruct H as [b1 b2 e h|e f h].
      + rewrite support_action,In_act_lists in F2.
        unfold act in F2;simpl in F2;revert F2;unfold_eqX;subst;intros.
        * rewrite action_invariant;[reflexivity|].
          apply elements_inv_act.
          intro;rewrite support_list_atoms.
          intros ? [<-|[<-|?]];tauto.
        * rewrite action_invariant;[reflexivity|].
          apply elements_inv_act.
          intro;rewrite support_list_atoms.
          intros ? [<-|[<-|?]];tauto.
        * rewrite <- (act_p_pinv [(b1,b2)] a) at 2.
          rewrite <- (act_p_pinv [(b1,b2)] c) at 2.
          rewrite <- splitAct_act.
          rewrite is_binding_finite_act in B2.
          cut (splitAct c b1 β e =α [(b1, b2)] ∙ splitAct c b2 β e);
            [intro e';unfold act at 2 3;simpl;simpl_eqX;unfold_eqX;subst|].
          -- assumption.
          -- apply (αKA_act ([(b1,b2)]∗)) in e'.
             rewrite act_pinv_p in e'.
             symmetry in e'.
             apply e'.
          -- clear e';apply ax_eq_ax,αKA_αα;intros u Iu.
             apply splitAct_lang in Iu as (u1&u2&->&Iu&Nu&Eu);[|assumption].
             apply h in Iu as (E1&E2).
             unfold fresh__α in *;simpl_binding in *.
             split;[rewrite <- E1|rewrite <- E2];f_equal;(etransitivity;[apply 𝗙_perm|]);
               unfold act;simpl;simpl_eqX;reflexivity.
          -- destruct_eqX β ε;subst.
             ++ transitivity (positive e).
                ** apply ax_inf_PartialOrder;unfold Basics.flip;split.
                   --- apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
                       transitivity (g1·g2).
                       +++ simpl;case_eq (test0 g2);
                             [intros T;apply test0_spec,KA_αKA in T as -> ;
                              replace e_zero with zero by reflexivity;simpl;
                              rewrite right_absorbing;apply zero_minimal|].
                           intro I2;apply ax_eq_inf,ax_eq_prod;[|reflexivity ].
                           symmetry;apply ax_eq_ax,αKA_αα.
                           intros u1 Iu1;split.
                           *** apply test0_false in I2 as (u2&Iu2).
                               destruct (split_binding_lang B2 Ig Iu1 Iu2) as (_&_&hyp);apply hyp.
                           *** apply αfresh_support.
                               apply support_lang in Iu1 as ->.
                               revert F1;apply split_binding_support in Ig as <-;simpl_In;tauto.
                       +++ transitivity (splitExpr b1 ε e).
                           *** etransitivity;[|apply ax_eq_inf,KA_αKA;symmetry;apply splitExpr_alt].
                               apply Σ_bigger,in_map_iff;exists (g1,g2);tauto.
                           *** apply KA_αKA_inf,CompletenessKA_inf.
                               rewrite splitExpr_lang by assumption.
                               intro u;rewrite positive_lang.
                               intros (?&?&?&->&?&_);split;[assumption|].
                               intro hyp;apply app_eq_nil in hyp as (->&->);tauto.
                   --- transitivity (positive ([(b1,c)]∙e)).
                       +++ apply positive_αKA_inf.
                           apply ax_eq_inf,ax_eq_ax,αKA_αα.
                           intros u Iu;split.
                           *** apply h in Iu;tauto.
                           *** apply αfresh_support;apply support_lang in Iu as ->;assumption.
                       +++ apply KA_αKA_inf,CompletenessKA_inf.
                           rewrite splitAct_lang by assumption.
                           intros u Iu.
                           apply positive_lang in Iu as (Iu&Nu).
                           apply act_lang in Iu.
                           exists ([(b1,c)]∗∙u),[];repeat rewrite app_nil_r;split;[|split;[|split]].
                           *** rewrite act_p_pinv;reflexivity.
                           *** assumption.
                           *** rewrite <- (act_bij [(b1,c)]),act_p_pinv;apply Nu.
                           *** apply h in Iu as (Iu&_);apply Iu.
                ** etransitivity;[|apply αKA_act];
                     [apply ax_eq_ax,αKA_αα;intros u Iu;apply positive_lang in Iu as (Iu&_);
                      apply h,Iu|].
                   symmetry;apply ax_inf_PartialOrder;unfold Basics.flip;split.
                   --- apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
                       transitivity (g1·g2).
                       +++ simpl;case_eq (test0 g2);
                             [intros T;apply test0_spec,KA_αKA in T as -> ;
                              replace e_zero with zero by reflexivity;simpl;
                              rewrite right_absorbing;apply zero_minimal|].
                           intro I2;apply ax_eq_inf,ax_eq_prod;[|reflexivity ].
                           symmetry;apply ax_eq_ax,αKA_αα.
                           intros u1 Iu1;split.
                           *** apply test0_false in I2 as (u2&Iu2).
                               destruct (split_binding_lang B2 Ig Iu1 Iu2) as (_&_&hyp);apply hyp.
                           *** apply αfresh_support.
                               apply support_lang in Iu1 as ->.
                               revert F1;apply split_binding_support in Ig as <-;simpl_In;tauto.
                       +++ transitivity (splitExpr b2 ε e).
                           *** etransitivity;[|apply ax_eq_inf,KA_αKA;symmetry;apply splitExpr_alt].
                               apply Σ_bigger,in_map_iff;exists (g1,g2);tauto.
                           *** apply KA_αKA_inf,CompletenessKA_inf.
                               rewrite splitExpr_lang by assumption.
                               intro u;rewrite positive_lang.
                               intros (?&?&?&->&?&_);split;[assumption|].
                               intro hyp;apply app_eq_nil in hyp as (->&->);tauto.
                   --- transitivity (positive ([(b2,c)]∙e)).
                       +++ apply positive_αKA_inf.
                           apply ax_eq_inf,ax_eq_ax,αKA_αα.
                           intros u Iu;split.
                           *** apply h in Iu;tauto.
                           *** apply αfresh_support;apply support_lang in Iu as ->;assumption.
                       +++ apply KA_αKA_inf,CompletenessKA_inf.
                           rewrite splitAct_lang by assumption.
                           intros u Iu.
                           apply positive_lang in Iu as (Iu&Nu).
                           apply act_lang in Iu.
                           exists ([(b2,c)]∗∙u),[];repeat rewrite app_nil_r;split;[|split;[|split]].
                           *** rewrite act_p_pinv;reflexivity.
                           *** assumption.
                           *** rewrite <- (act_bij [(b2,c)]),act_p_pinv;apply Nu.
                           *** apply h in Iu as (_&Iu);apply Iu.
             ++ transitivity zero;[|symmetry];apply KA_αKA,test0_spec;[|rewrite test0_act];
                  apply not_false_is_true;intros I;apply test0_false in I as (u&Iu);
                    apply splitAct_lang in Iu as (u1&u2&->&Iu&Nu&Eu);try assumption;apply h in Iu;
                      revert Iu;unfold fresh__α;simpl_binding; rewrite Eu;
                        destruct β as ((k1,k2),k3);simpl in *;rewrite Eβ in *.
                ** intros (hyp&_);revert hyp N1;clear.
                   destruct (𝗙 b1 u2) as ((l1,l2),l3);unfold prod_binding.
                   destruct l1;simpl;intro E;inversion E as [[e1 e2 e3]];subst.
                   --- apply orb_false_iff in e2 as (->&_);tauto.
                   --- lia.
                ** intros (_&hyp);revert hyp N1;clear.
                   destruct (𝗙 b2 u2) as ((l1,l2),l3);unfold prod_binding.
                   destruct l1;simpl;intro E;inversion E as [[e1 e2 e3]];subst.
                   --- apply orb_false_iff in e2 as (->&_);tauto.
                   --- lia.
      + eapply ax_eq_ax in h.
        pose proof B2 as B1.
        apply (is_binding_finite_ax_eq (KA_αKA h)) in B1.
        apply CompletenessKA in h.
        apply KA_αKA,CompletenessKA.
        repeat rewrite splitAct_lang by assumption.
        revert h;clear;intros h u;split;intros (u1&u2&->&Iu&hyp);apply h in Iu;exists u1,u2;tauto.
    - destruct H as [e f|e f].
      + assert (eq : e · f <=α f) by apply E.
        assert (ih : forall β a c, c_binding β = 0 -> c # e -> c # f ->
                              splitAct c a β (e · f) <=α splitAct c a β f)
          by (intros β' a' c' CB Fe Ff;unfold ax_inf;etransitivity;[|apply IHE];try assumption;
              [unfold splitAct;simpl;rewrite map_app,algebra.Σ_app;reflexivity
              |rewrite support_join,support_prod;simpl_In;tauto]);clear E IHE.
        assert (c#e /\ c#f) as (Fe&Ff)
            by (revert F1;rewrite support_join,support_prod,support_star;simpl_In;tauto);clear F1 F2.
        cut (splitAct c a β (e ⋆ · f) <=α splitAct c a β f);
          [intros hyp;etransitivity;[|apply hyp];unfold splitAct;simpl;
           rewrite map_app,algebra.Σ_app;reflexivity|].
        case_eq (test0 f);intro Tf;
          [rewrite splitAct_test0 by (simpl;rewrite Tf;reflexivity);apply zero_minimal|].
        case_eq (test0 e);intro Te.
        * apply ax_eq_inf,KA_αKA,CompletenessKA.
          repeat rewrite splitAct_lang.
          -- apply test0_spec,soundness in Te.
             intro u;split;intros (u1&u2&->&Iu&?).
             ++ destruct Iu as (v1&v2&E&([]&Iv1)&Iv2).
                ** rewrite Iv1 in *;simpl in *;subst.
                   exists u1,u2;tauto.
                ** destruct Iv1 as (?&?&_&F&_);apply Te in F;exfalso;apply F.
             ++ exists u1,u2;split;[reflexivity|split;[|assumption]].
                exists [],(u1++u2);split;[reflexivity|split;[|assumption]].
                exists 0;reflexivity.
          -- assumption.
          -- eapply is_binding_finite_ax_inf;[apply B2|apply ka_star_left_ind,eq].
        * assert (Bs : is_binding_finite (e⋆))
            by (cut (is_binding_finite (e⋆·f));
                [|eapply is_binding_finite_ax_inf;[apply B2|apply ka_star_left_ind,eq]];
                repeat rewrite <- binding_finite_spec;simpl;rewrite Tf;simpl;
                apply binding_finite_spec in B2 as ->;rewrite andb_true_r;tauto).
          unfold splitAct;simpl;rewrite Tf;simpl.
          cut (forall β1 β2, (β1,β2)∈ factors β (sizeExpr e) ->
                        [(a, c)] ∙ filter_binding a β1 (e ⋆) · splitAct c a β2 f
                        <=α Σ (map (fun p : Regexp * Regexp => [(a, c)] ∙ fst p · snd p)
                                  (split_binding a β f))).
          -- intros hyp.
             rewrite map_app,map_map;apply Σ_bounded;intros g Ig;simpl_In in Ig;
               destruct Ig as [Ig|Ig];
               apply in_map_iff in Ig as ((g1'&g2')&<-&Ig);apply in_flat_map in Ig as ((β1,β2)&Iβ&Ig);
                 apply in_map_iff in Ig as ((g1&g2)&heq&Ig);
                 symmetry in heq;inversion heq;clear heq;subst; simpl in *.
             ++ rewrite <- (mon_assoc g2 _ f).
                pose proof eq as eq';apply ka_star_left_ind in eq' as ->.
                rewrite act_prod,<- (mon_assoc _ _ _).
                etransitivity;[apply proper_prod_inf;
                               [reflexivity
                               |etransitivity;[|apply (ih β2 a c);try assumption ]]|].
                ** apply Σ_bigger,in_map_iff;exists (g1,g2·f);split;[reflexivity|].
                   simpl;rewrite Tf,Te;simpl;simpl_In;left.
                   apply in_map_iff;exists (g1,g2);tauto.
                ** revert Eβ;apply factors_prod in Iβ as <-;simpl_binding;lia.
                ** clear g1 g2 Ig.
                   apply hyp,Iβ.
             ++ rewrite act_prod,<- (mon_assoc _ _ _).
                transitivity ([(a, c)] ∙ filter_binding a β1 (e ⋆) · splitAct c a β2 f);
                  [apply proper_prod_inf;[reflexivity|apply Σ_bigger,in_map_iff;exists (g1,g2);tauto]|].
                apply hyp,Iβ.
          -- intros β1 β2 Iβ.
             case_eq (test0 (filter_binding a β1 (e⋆)));intro Ts;
               [apply test0_spec,KA_αKA,(αKA_act [(a,c)]) in Ts as -> ;
                replace ([(a,c)]∙e_zero) with zero by reflexivity;
                rewrite left_absorbing;apply zero_minimal|].
             apply test0_false in Ts as (u&Iu).
             apply filter_binding_lang in Iu as (Iu&Eu);[|assumption].
             pose proof (binding_finite_sqExpr_star Bs) as (_&Sq).
             assert (Sqβ1 : square β1)
               by (subst;apply (Sq a),(is_binding_finite_bindings Bs),Iu).
             apply (binding_finite_bound_size a Bs) in Iu.
             rewrite Eu in *;clear u Eu.
             destruct_eqX β2 β;subst.
             ** transitivity ([(a,c)]∙(Σ (map (fun α => filter_binding a α e) (lower_squares β1)))⋆
                                        · splitAct c a β f).
                   --- apply proper_prod_inf;[|reflexivity].
                       rewrite <- act_star.
                       apply αKA_inf_act.
                       apply KA_αKA_inf,filter_binding_star,Bs.
                   --- apply ka_star_left_ind;etransitivity;[|apply ih;try assumption].
                       rewrite Σ_act.
                       unfold act at 1,act_lists.
                       rewrite map_map,Σ_distr_r,map_map;apply Σ_bounded;intros g Ig;
                         apply in_map_iff in Ig as (α&<-&Iα).
                       rewrite Σ_distr_l,map_map.
                       apply Σ_bounded;intros g Ig; apply in_map_iff in Ig as ((g1&g2)&<-&Ig);simpl.
                       rewrite (mon_assoc _ _ _),<-act_prod.
                       apply Σ_bigger,in_map_iff;exists (filter_binding a α e·g1,g2);split;[reflexivity|].
                       simpl;rewrite Te,Tf;simpl;simpl_In;right.
                       apply in_flat_map;exists (α,β);split;[|apply in_map_iff;exists (g1,g2);tauto].
                       apply factors_In.
                       +++ transitivity (size β1);subst.
                           *** apply lower_squares_size,Iα;assumption.
                           *** transitivity (sizeExpr (e⋆));[assumption|reflexivity].
                       +++ apply factors_prod in Iβ as e1.
                           apply (lower_squares_spec _ Sqβ1) in Iα as (_&e2).
                           rewrite <- e1 at 1.
                           rewrite prod_assoc,e2,e1;reflexivity.
                ** destruct (@product_square_close_balanced β1 β2 β)
                    as (N1&N2&N3&t1&t2&t3&->&->&->&L&->&[(->&_)|(->&->&->&->&Eβ1&Hyp)]);
                     try (try eapply factors_prod;eassumption);
                     [exfalso;apply N;reflexivity|].
                   transitivity
                     ([(a, c)] ∙ ((Σ (map (fun α => filter_binding a α e)(lower_squares (N3,true,N3))))⋆
                                     · filter_binding a (N3, true, N3) e
                                     · (Σ (map (fun α => filter_binding a α e)
                                               (lower_squares (N3,false,N3))))⋆)
                               · splitAct c a (N3, false, 0) f).
                   --- apply proper_prod_inf;[|reflexivity].
                       apply αKA_inf_act.
                       apply ax_eq_inf.
                       Opaque lower_squares.
                       Transparent filter_binding.
                       simpl.
                       Opaque filter_binding.
                       unfold is_square,d_binding;simpl.
                       rewrite PeanoNat.Nat.eqb_refl.
                       clear Sqβ1 Eβ L N.
                       simpl_eqX.
                       assert (Σ (map (fun α : nat * bool * nat => filter_binding a α e)
                                      (lower_squares (N3, true, N3)))
                               =α Σ (map (fun α : nat * bool * nat => filter_binding a α e)
                                         ((N3, true, N3) :: lower_squares (N3, false, N3)))) as hyp
                           by (apply algebra.Σ_equivalent;rewrite Eβ1;reflexivity).
                       revert hyp;clear;simpl.
                       set (E:=Σ (map (fun α : nat * bool * nat => filter_binding a α e) (lower_squares (N3, true, N3)))).
                       set (F:=Σ (map (fun α : nat * bool * nat => filter_binding a α e) (lower_squares (N3, false, N3)))).
                       set (G:= filter_binding a (N3, true, N3) e).
                       intros eq.
                       assert (eq': G<=αE) by (rewrite eq;apply inf_cup_left).
                       assert (eq'': F<=αE) by (rewrite eq;apply inf_cup_right).
                       apply ax_inf_PartialOrder;unfold Basics.flip;split;
                         [|rewrite eq'' at 1;reflexivity].
                       rewrite <- (mon_assoc _ _ _).
                       rewrite eq at 2.
                       rewrite star_join.
                       repeat rewrite (semiring_left_distr _ _ _)
                       || rewrite (semiring_right_distr _ _ _)
                       || rewrite <- (mon_assoc _ _ _).
                       rewrite <- star_switch_side.
                       apply inf_join_inf.
                       +++ transitivity (E⋆·G·un).
                           *** rewrite (mon_assoc _ _ _),eq',ka_star_dup at 1.
                               rewrite right_unit.
                               reflexivity.
                           *** rewrite (mon_assoc _ _ _);apply proper_prod_inf;
                                 [reflexivity|apply one_inf_star].
                       +++ rewrite (mon_assoc G _ _).
                           rewrite <- star_switch_side.
                           rewrite eq',eq'' at 1.
                           rewrite (mon_assoc (E⋆) _ _).
                           repeat apply proper_prod_inf;try reflexivity.
                           etransitivity;[|apply ax_eq_inf,ka_star_dup].
                           apply proper_prod_inf;[reflexivity|].
                           etransitivity;[|apply ax_eq_inf;symmetry;apply ka_star_star].
                           apply proper_star_inf.
                           etransitivity;[|apply ax_eq_inf,ka_star_dup].
                           apply proper_prod_inf;[|reflexivity].
                           apply star_incr.
                   --- repeat rewrite act_prod||rewrite act_star.
                       repeat rewrite <- (mon_assoc _ _ _).
                       transitivity ([(a, c)] ∙
                                              (Σ (map (fun α => filter_binding a α e)
                                                      (lower_squares (N3, true, N3))) ⋆) ·
                                              ([(a, c)] ∙ filter_binding a (N3, true, N3) e ·
                                                        (splitAct c a (N3, false, 0) f))).
                       +++ apply proper_prod_inf;[reflexivity|].
                           apply proper_prod_inf;[reflexivity|].
                           apply ka_star_left_ind.
                           etransitivity;[|apply ih;tauto].
                           rewrite Σ_act,Σ_distr_r.
                           unfold act,act_lists;repeat rewrite map_map.
                           apply Σ_bounded;intros g Ig.
                           apply in_map_iff in Ig as (α&<-&Iα);simpl.
                           unfold splitAct;rewrite Σ_distr_l;simpl;rewrite Te,Tf;simpl.
                           rewrite map_app;repeat rewrite map_map.
                           apply Σ_bounded;intros g Ig.
                           apply in_map_iff in Ig as ((g1&g2)&<-&Ig);simpl.
                           rewrite (mon_assoc _ _ _),<-act_prod.
              
                           apply Σ_bigger;simpl_In;right.
                           apply in_map_iff;exists (filter_binding a α e · g1,g2);split;[reflexivity|].
                           apply in_flat_map;exists (α,(N3,false,0));split.
                           *** apply factors_In.
                               ---- transitivity (sizeExpr (e⋆));[|reflexivity].
                                    rewrite <- Iu.
                                    transitivity (size (N3,false,N3));[|reflexivity].
                                    apply lower_squares_size;[reflexivity|assumption].
                               ---- apply Hyp,Iα.
                           *** apply in_map_iff;exists (g1,g2);tauto.
                       +++ transitivity ([(a, c)] ∙
                                              (Σ (map (fun α => filter_binding a α e)
                                                      (lower_squares (N3, true, N3))) ⋆) ·
                                              (splitAct c a (N3, true, 0) f)).
                           *** apply proper_prod_inf;[reflexivity|].
                               etransitivity;[|apply ih;tauto].
                               unfold splitAct;rewrite Σ_distr_l;simpl;rewrite Te,Tf;simpl.
                               rewrite map_app;repeat rewrite map_map.
                               apply Σ_bounded;intros g Ig.
                               apply in_map_iff in Ig as ((g1&g2)&<-&Ig);simpl.
                               rewrite (mon_assoc _ _ _),<-act_prod.
                               apply Σ_bigger;simpl_In;right.
                               apply in_map_iff.
                               exists (filter_binding a (N3,true,N3) e · g1,g2);split;[reflexivity|].
                               apply in_flat_map;exists ((N3,true,N3),(N3,false,0));split.
                               ---- assumption.
                               ---- apply in_map_iff;exists (g1,g2);tauto.
                           *** rewrite act_star.
                               apply ka_star_left_ind.
                               etransitivity;[|apply ih;tauto].
                               rewrite Σ_act,Σ_distr_r.
                               unfold act at 2,act_lists;repeat rewrite map_map.
                               apply Σ_bounded;intros g Ig.
                               apply in_map_iff in Ig as (α&<-&Iα);simpl.
                               unfold splitAct;rewrite Σ_distr_l;simpl;rewrite Te,Tf;simpl.
                               rewrite map_app;repeat rewrite map_map.
                               apply Σ_bounded;intros g Ig.
                               apply in_map_iff in Ig as ((g1&g2)&<-&Ig);simpl.
                               rewrite (mon_assoc _ _ _),<-act_prod.
                               apply Σ_bigger;simpl_In;right.
                               apply in_map_iff;exists (filter_binding a α e · g1,g2);split;[reflexivity|].
                               apply in_flat_map;exists (α,(N3,true,0));split.
                               ---- apply factors_In.
                                    ++++ transitivity (sizeExpr (e⋆));[|reflexivity].
                                         rewrite <- Iu.
                                         transitivity (size (N3,true,N3));[|reflexivity].
                                         apply lower_squares_size;[reflexivity|assumption].
                                    ++++ apply factors_prod in Iβ.
                                         apply lower_squares_spec in Iα as (_&Iα);[|reflexivity].
                                         rewrite <- Iβ at 1;rewrite prod_assoc,Iα;apply Iβ.
                               ---- apply in_map_iff;exists (g1,g2);tauto.
      + assert (eq : e · f <=α e) by apply E.
        assert (ih : forall β a c, c_binding β = 0 -> c # e -> c # f ->
                              splitAct c a β (e · f) <=α splitAct c a β e)
          by (intros β' a' c' CB Fe Ff;unfold ax_inf;etransitivity;[|apply IHE];try assumption;
              [unfold splitAct;simpl;rewrite map_app,algebra.Σ_app;reflexivity
              |rewrite support_join,support_prod;simpl_In;tauto]);clear E IHE.
        assert (c#e /\ c#f) as (Fe&Ff)
            by (revert F1;rewrite support_join,support_prod,support_star;simpl_In;tauto);clear F1 F2.
        cut (splitAct c a β (e · f ⋆) <=α splitAct c a β e);
          [intros hyp;etransitivity;[|apply hyp];unfold splitAct;simpl;
           rewrite map_app,algebra.Σ_app;reflexivity|].
        case_eq (test0 e);intro Te;
          [rewrite splitAct_test0 by (simpl;rewrite Te;reflexivity);apply zero_minimal|].
        case_eq (test0 f);intro Tf.
        * apply ax_eq_inf,KA_αKA,CompletenessKA.
          repeat rewrite splitAct_lang.
          -- apply test0_spec,soundness in Tf.
             intro u;split;intros (u1&u2&->&Iu&?).
             ++ destruct Iu as (v1&v2&E&Iv1&[]&Iv2).
                ** rewrite Iv2 in *;simpl in *; rewrite app_nil_r in *;subst.
                   exists u1,u2;tauto.
                ** destruct Iv2 as (?&?&_&F&_);apply Tf in F;exfalso;apply F.
             ++ exists u1,u2;split;[reflexivity|split;[|assumption]].
                exists (u1++u2),[];split;[rewrite app_nil_r;reflexivity|split;[assumption|]].
                exists 0;reflexivity.
          -- assumption.
          -- eapply is_binding_finite_ax_inf;[apply B2|apply ka_star_right_ind,eq].
        * assert (Bs : is_binding_finite (f⋆))
            by (cut (is_binding_finite (e·f⋆));
                [|eapply is_binding_finite_ax_inf;[apply B2|apply ka_star_right_ind,eq]];
                repeat rewrite <- binding_finite_spec;simpl;rewrite Te;simpl;
                apply binding_finite_spec in B2 as ->;tauto).
          unfold splitAct;simpl;rewrite Te;simpl.
          rewrite map_app,map_map;simpl.
          apply Σ_bounded;intro g;simpl_In.
          intros [Ig|Ig].
          -- apply in_map_iff in Ig as ((g1&g2)&<-&Ig);simpl.
             repeat rewrite (mon_assoc _ _ _).
             transitivity (splitAct c a β e· f⋆).
             ++ apply proper_prod_inf;[|reflexivity].
                apply Σ_bigger,in_map_iff;exists (g1,g2);tauto.
             ++ apply ka_star_right_ind.
                etransitivity;[|apply ih;assumption].
                unfold splitAct;simpl.
                rewrite Σ_distr_r,map_map,Te,Tf;simpl.
                rewrite map_app,map_map,<- algebra.Σ_app.
                etransitivity;[|apply inf_cup_left].
                simpl;apply ax_eq_inf,Σ_map_equiv_α;intros (?&?) _.
                symmetry;apply mon_assoc.
          -- apply in_map_iff in Ig as ((g1&g2)&<-&Ig);simpl.
             apply in_flat_map in Ig as ((β1&β2)&Iβ&Ig);simpl.
             apply in_map_iff in Ig as ((f1&f2)&heq&If);simpl.
             symmetry in heq;inversion heq;clear heq;subst.
             apply in_flat_map in If as ((α1&α2)&Iα&If);simpl.
             apply in_map_iff in If as ((g1&g2)&heq&Ig);simpl.
             symmetry in heq;inversion heq;clear heq;subst.
             simpl in *.
             transitivity ([(a, c)] ∙ (filter_binding a (β1⋅α1) e · g1) · (g2 · f ⋆)).
             ++ apply proper_prod_inf;[|reflexivity].
                apply αKA_inf_act.
                repeat rewrite (mon_assoc _ _ _).
                apply proper_prod_inf;[|reflexivity].
                etransitivity;[|apply filter_binding_αKA_inf,ka_star_right_ind,eq;assumption].
                apply KA_αKA_inf,CompletenessKA_inf.
                intros u (u1&u2&->&Iu1&Iu2).
                rewrite filter_binding_lang in Iu1,Iu2 by assumption.
                apply filter_binding_lang.
                ** revert Te Bs B2;clear.
                   repeat rewrite <- binding_finite_spec;simpl.
                   intros -> -> ->;reflexivity.
                ** split;[exists u1,u2;tauto|].
                   simpl_binding.
                   destruct Iu1 as (_&->),Iu2 as (_&->);reflexivity.
             ++ transitivity (splitAct c a β e· f⋆).
                ** repeat rewrite (mon_assoc _ _ _).
                   apply proper_prod_inf;[|reflexivity].
                   etransitivity;[|apply ih;assumption].
                   case_eq (test0 (filter_binding a (β1⋅α1) e));intro Ts;
                     [rewrite act_prod;repeat rewrite <-(mon_assoc _ _ _);
                      apply test0_spec,KA_αKA,(αKA_act [(a,c)]) in Ts as -> ;
                      replace ([(a,c)]∙e_zero) with zero by reflexivity;
                      rewrite left_absorbing;apply zero_minimal|].
                   apply test0_false in Ts as (u&Iu).
                   apply filter_binding_lang in Iu as (Iu&Eu);[|assumption].
                   apply (binding_finite_bound_size a B2) in Iu.
                   rewrite Eu in *;clear u Eu.
                   unfold splitAct;apply Σ_bigger,in_map_iff.
                   exists (filter_binding a (β1 ⋅ α1) e · g1, g2);split;[reflexivity|].
                   simpl;rewrite Te,Tf;simpl;simpl_In.
                   right;apply in_flat_map;exists (β1⋅α1,α2);split.
                   --- apply factors_In;[assumption|].
                       rewrite <- prod_assoc.
                       apply factors_prod in Iα as ->.
                       apply factors_prod in Iβ as ->;reflexivity.
                   --- apply in_map_iff;exists (g1,g2);tauto.
                ** apply ka_star_right_ind.
                   etransitivity;[|apply ih;assumption].
                   unfold splitAct;simpl.
                   rewrite Σ_distr_r,map_map,Te,Tf;simpl.
                   rewrite map_app,map_map,<- algebra.Σ_app.
                   etransitivity;[|apply inf_cup_left].
                   simpl;apply ax_eq_inf,Σ_map_equiv_α;intros (?&?) _.
                   symmetry;apply mon_assoc.
  Qed.

  Lemma splitAct_join c a β e f :
    splitAct c a β (e ∪ f) =KA splitAct c a β e ∪ splitAct c a β f.
  Proof. symmetry;unfold splitAct;simpl;rewrite map_app;apply algebra.Σ_app. Qed.

  Lemma splitAct_prod c a β e f :
    test0 (e·f) = false ->
    splitAct c a β (e·f)
    =KA (splitAct c a β e · f)
        ∪ Σ (map (fun B =>[(a,c)]∙filter_binding a (fst B) e·splitAct c a (snd B) f)
                 (factors β (sizeExpr e))).
  Proof.
    unfold splitAct;simpl;intros ->.
    rewrite map_app,map_map.
    etransitivity;[symmetry;apply algebra.Σ_app|].
    apply ax_eq_add.
    - etransitivity;[|symmetry;apply Σ_distr_r].
      rewrite map_map;simpl.
      apply Σ_map_equiv.
      intros (g1,g2) _;simpl.
      apply mon_assoc.
    - apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g.
      + rewrite in_map_iff;setoid_rewrite in_flat_map;setoid_rewrite in_map_iff.
        intros ((g1&g2)&<-&(β1&β2)&Iβ&(f1&f2)&heq&If).
        symmetry in heq;inversion heq;clear heq;subst;simpl in *.
        rewrite act_prod;etransitivity;[apply ax_eq_inf;symmetry;apply mon_assoc|].
        transitivity ([(a, c)] ∙ filter_binding a β1 e · splitAct c a β2 f).
        * apply proper_prod_inf;[reflexivity|].
          apply Σ_bigger,in_map_iff;exists (f1,f2);tauto.
        * apply Σ_bigger,in_map_iff;exists (β1,β2);tauto.
      + rewrite in_map_iff.
        intros ((β1&β2)&<-&Iβ).
        etransitivity;[apply ax_eq_inf,Σ_distr_l|].
        rewrite map_map.
        apply Σ_bounded;intros g.
        rewrite in_map_iff.
        intros ((f1&f2)&<-&If);simpl in *.
        etransitivity;[apply ax_eq_inf;apply mon_assoc|].
        rewrite <- act_prod.
        apply Σ_bigger,in_map_iff;exists (filter_binding a β1 e·f1,f2);split;[reflexivity|].
        apply in_flat_map;exists (β1,β2);split;[assumption|].
        apply in_map_iff;exists (f1,f2);tauto.
  Qed.
        
  Lemma splitAct_star c a β e :
    splitAct c a β (e⋆)
    =KA Σ (map (fun B =>[(a,c)]∙filter_binding a (fst B) (e⋆)·splitAct c a (snd B) e)
               (factors β (sizeExpr e)))·e⋆.
  Proof.
    unfold splitAct;simpl.
    etransitivity;[|symmetry;apply Σ_distr_r].
    rewrite map_map.
    apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g.
    - rewrite in_map_iff;setoid_rewrite in_flat_map;setoid_rewrite in_map_iff.
      intros ((g1&g2)&<-&(β1&β2)&Iβ&(f1&f2)&heq&If).
      symmetry in heq;inversion heq;clear heq;subst;simpl in *.
      rewrite act_prod;etransitivity;[apply ax_eq_inf;symmetry;apply mon_assoc|].
      transitivity ([(a, c)] ∙ filter_binding a β1 (e⋆) · splitAct c a β2 e · e⋆).
      + etransitivity;[apply proper_prod_inf;[reflexivity|apply ax_eq_inf;apply mon_assoc]|].
        etransitivity;[|apply ax_eq_inf;apply mon_assoc].
        apply proper_prod_inf;[reflexivity|].
        apply proper_prod_inf;[|reflexivity].
        apply Σ_bigger,in_map_iff;exists (f1,f2);tauto.
      + apply Σ_bigger,in_map_iff;exists (β1,β2);tauto.
    - rewrite in_map_iff.
      intros ((β1&β2)&<-&Iβ).
      etransitivity;[apply proper_prod_inf;[apply ax_eq_inf,Σ_distr_l|reflexivity]|].
      etransitivity;[apply ax_eq_inf,Σ_distr_r|].
      repeat rewrite map_map;simpl.
      apply Σ_bounded;intros g.
      rewrite in_map_iff.
      intros ((f1&f2)&<-&If);simpl in *.
      etransitivity;[apply proper_prod_inf;[apply ax_eq_inf;apply mon_assoc|reflexivity]|].
      rewrite <- act_prod.
      etransitivity;[apply ax_eq_inf;symmetry;apply mon_assoc|].
      apply Σ_bigger,in_map_iff;exists (filter_binding a β1 (e⋆)· f1 ,f2 ·e⋆);split;[reflexivity|].
      apply in_flat_map;exists (β1,β2);split;[assumption|].
      apply in_map_iff;exists (f1,f2);tauto.
  Qed.
  Opaque split_binding.

  Lemma is_binding_finite_splitAct c a β e :
    is_binding_finite e -> is_binding_finite (splitAct c a β e).
  Proof.
    intro Be.
    unfold splitAct;apply is_binding_finite_Σ.
    intros f If;apply in_map_iff in If as ((f1&f2)&<-&If).
    apply split_binding_is_binding_finite in If as (Bf1&Bf2);[|assumption].
    apply (is_binding_finite_act [(a,c)]) in Bf1.
    rewrite <- binding_finite_spec in *;simpl.
    rewrite Bf1,Bf2;simpl.
    apply orb_true_r.
  Qed.

  Lemma splitAct_αKA_inf c a β e f :
    is_binding_finite f -> c_binding β = 0 -> c # e -> c # f ->
    e <=α f -> splitAct c a β e <=α splitAct c a β f.
  Proof.
    intros Bf CB Fe Ff E;eapply splitAct_αKA in E;try eassumption.
    - unfold ax_inf;etransitivity;[symmetry;apply KA_αKA,splitAct_join|];apply E.
    - rewrite support_join;simpl_In;tauto.
  Qed.


End s.