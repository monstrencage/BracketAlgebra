Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp systems.
Require Import factors aeq_facts.
Require Import alpha_regexp closed_languages binding_finite alphaKA.
Require Import filters splits strict_split.

Opaque filter_binding lower_squares splitAct.

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
  
  Lemma 𝗙_perm p (a:atom) (u:list letter) : 𝗙 a (p∙u) = 𝗙 (p∗∙a) u.
  Proof. apply 𝗙_perm. Qed.

  Notation " N ▶ " := ((N,false,0):𝖡) (at level 30).

  Notation 𝔉 := filter_binding.

  Definition BiLowerExpr a N1 f1 b N2 f2 e := Σ (map (fun B => 𝔉 b (snd B) (𝔉 a (fst B) e))
                                                     (pairs (lower_squares (N1,f1,N1))
                                                            (lower_squares (N2,f2,N2)))).

  
  Transparent filter_binding.
  Lemma BiLowerExpr_LowerExpr a N1 f1 b N2 f2 e :
    BiLowerExpr a N1 f1 b N2 f2 e =KA LowerExpr b N2 f2 (LowerExpr a N1 f1 e).
  Proof.
    unfold BiLowerExpr,LowerExpr.
    generalize (lower_squares (N2,f2,N2)).
    generalize (lower_squares (N1,f1,N1)).
    clear N1 N2 f1 f2.
    intros l m;induction l;simpl.
    - symmetry;apply test0_spec;rewrite test0_Σ,forallb_forall.
      intros ? I;apply in_map_iff in I as (?&<-&_);reflexivity.
    - rewrite map_app.
      etransitivity;[symmetry;apply algebra.Σ_app|].
      rewrite IHl;clear IHl.
      etransitivity;[apply algebra.Σ_app|].
      rewrite map_map.
      apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros f;simpl_In.
      + intros [I|I].
        * apply in_map_iff in I as (B&<-&IB);simpl.
          etransitivity;[apply inf_cup_left|].
          apply Σ_bigger,in_map_iff;exists B;split;[reflexivity|assumption].
        * apply in_map_iff in I as (B&<-&IB).
          etransitivity;[apply inf_cup_right|].
          apply Σ_bigger,in_map_iff;exists B;split;[reflexivity|assumption].
      + intro I;apply in_map_iff in I as (B&<-&IB);simpl.
        etransitivity;[|apply ax_eq_inf,algebra.Σ_app].
        apply inf_join_inf.
        * etransitivity;[|apply inf_cup_left].
          apply Σ_bigger,in_map_iff;exists B;tauto.
        * etransitivity;[|apply inf_cup_right].
          apply Σ_bigger,in_map_iff;exists B;tauto.
  Qed.
  Opaque filter_binding.

  Lemma BiLowerExpr_support a N1 f1 b N2 f2 e : ⌊BiLowerExpr a N1 f1 b N2 f2 e⌋ ⊆ ⌊e⌋.
  Proof.
    unfold BiLowerExpr.
    rewrite <- Σ_support.
    intros c Ic.
    apply In_support_list in Ic as (g&Ig&Ic).
    apply in_map_iff in Ig as ((?&?)&<-&_).
    repeat apply filter_binding_support in Ic;tauto.
  Qed.

  Lemma BiLowerExpr_inf a1 N1 f1 a2 N2 f2 e :
    is_binding_finite e -> BiLowerExpr a1 N1 f1 a2 N2 f2 e <=KA e.
  Proof.
    intros Be;apply Σ_bounded;intros g Ig.
    apply in_map_iff in Ig as (β&<-&Iβ).
    etransitivity;[|apply filter_binding_inf,Be].
    apply filter_binding_inf,is_binding_finite_filter_binding,Be.
  Qed.
    
  Lemma BiLowerExpr_is_binding_finite a1 N1 f1 a2 N2 f2 e :
    is_binding_finite e -> is_binding_finite (BiLowerExpr a1 N1 f1 a2 N2 f2 e).
  Proof.
    intros Be;eapply is_binding_finite_ax_inf,KA_αKA_inf,BiLowerExpr_inf;assumption.
  Qed.

  Lemma BiLowerExpr_star_is_binding_finite a1 N1 f1 a2 N2 f2 e :
    is_binding_finite (e⋆) -> is_binding_finite (BiLowerExpr a1 N1 f1 a2 N2 f2 e ⋆).
  Proof.
    intros Be;eapply is_binding_finite_ax_inf,KA_αKA_inf,proper_star_inf,BiLowerExpr_inf.
    - assumption.
    - rewrite <- binding_finite_spec in *;apply andb_true_iff in Be;tauto.
  Qed.

  Lemma BiLowerExpr_ϵ a1 N1 f1 a2 N2 f2 e :
    is_binding_finite e -> ϵ (BiLowerExpr a1 N1 f1 a2 N2 f2 e) = ϵ e.
  Proof.
    unfold BiLowerExpr;intro Be.
    destruct (ϵ_zero_or_un e) as [E|E];rewrite E.
    - apply ϵ_Σ_un.
      exists (𝔉 a2 (0▶) (𝔉 a1 (0▶) e));split.
      + apply in_map_iff;exists (0▶,0▶);split;[reflexivity|].
        apply pairs_spec;split;(apply lower_squares_alt;[reflexivity|]);
        (split;[reflexivity|]).
        * simpl;destruct N1;[tauto|left;lia].
        * simpl;destruct N2;[tauto|left;lia].
      + apply ϵ_spec,filter_binding_lang;[apply is_binding_finite_filter_binding,Be|].
        split;[|reflexivity].
        apply filter_binding_lang;[apply Be|].
        split;[|reflexivity].
        apply ϵ_spec,E.
    - apply ϵ_Σ_zero.
      intros g Ig.
      apply in_map_iff in Ig as (β&<-&Iβ);simpl in *.
      apply filter_binding_ϵ,filter_binding_ϵ,E.
  Qed.

  Lemma BiLowerExpr_test0 a1 N1 f1 a2 N2 f2 e :
    test0 e = true -> test0 (BiLowerExpr a1 N1 f1 a2 N2 f2 e) = true.
  Proof.
    intro T.
    unfold BiLowerExpr.
    rewrite test0_Σ.
    apply forallb_forall;intros g Ig.
    apply in_map_iff in Ig as (β&<-&Iβ);simpl in *.
    apply filter_binding_test0,filter_binding_test0,T.
  Qed.

  Lemma BiLowerExpr_act p a1 N1 f1 a2 N2 f2 e :
    p∙ (BiLowerExpr a1 N1 f1 a2 N2 f2 e)
    = BiLowerExpr (p∙a1) N1 f1 (p∙a2) N2 f2 (p∙e).
  Proof.
    unfold BiLowerExpr.
    rewrite Σ_act.
    unfold act at 1,act_lists.
    rewrite map_map;f_equal.
    apply map_ext.
    intros b;repeat rewrite filter_binding_act;reflexivity.
  Qed.

  Lemma BiLowerExpr_lang a1 N1 f1 a2 N2 f2 e :
    is_binding_finite e ->
    ⟦BiLowerExpr a1 N1 f1 a2 N2 f2 e⟧
      ≃ (fun u => ⟦e⟧ u /\ 𝗙 a1 u ∈ (lower_squares (N1,f1,N1))
               /\ 𝗙 a2 u ∈ (lower_squares (N2,f2,N2))).
  Proof.
    unfold BiLowerExpr; intros Be u;split;intros Iu.
    - apply Σ_lang in Iu as (g&Ig&Iu).
      apply in_map_iff in Ig as ((β1&β2)&<-&Iβ).
      apply filter_binding_lang in Iu as (Iu&->);[|apply is_binding_finite_filter_binding,Be].
      apply filter_binding_lang in Iu as (Iu&->);[|apply Be].
      apply pairs_spec in Iβ as (I1&I2).
      tauto.
    - destruct Iu as (Iu&Eu1&Eu2).
      apply Σ_lang;exists (𝔉 a2 (𝗙 a2 u) (𝔉 a1 (𝗙 a1 u) e));split.
      + apply in_map_iff;exists (𝗙 a1 u,𝗙 a2 u);split.
        * reflexivity.
        * apply pairs_spec;tauto.
      + apply filter_binding_lang;[apply is_binding_finite_filter_binding
                                  |split;[apply filter_binding_lang|]];tauto.
  Qed.
  
  Lemma BiLowerExpr_star_lang a1 N1 f1 a2 N2 f2 e :
    is_binding_finite (e⋆) -> ⟦BiLowerExpr a1 N1 f1 a2 N2 f2 e⋆⟧
                               ≃ (fun u => ⟦e⋆⟧ u /\ 𝗙 a1 u ∈ (lower_squares (N1,f1,N1))
                                        /\ 𝗙 a2 u ∈ (lower_squares (N2,f2,N2))).
  Proof.
    intros Bs.
    assert (Sq : sqExpr e)
      by (eapply sqExpr_inf;[apply binding_finite_sqExpr_star,Bs|simpl;apply star_incr]). 
    unfold BiLowerExpr; intros u;split;intros Iu.
    - assert (h : ⟦BiLowerExpr a1 N1 f1 a2 N2 f2 e⋆⟧≲⟦e⋆⟧)
        by (apply ax_inf_lang_incl,proper_star_inf,BiLowerExpr_inf,Sq).    
      split;[apply h,Iu|clear h].
      destruct Iu as (n&Iu).
      revert u Iu;induction n;intros u Iu.
      + rewrite Iu.
        split;(apply lower_squares_alt;[reflexivity|split;[reflexivity|]]).
        * destruct N1;[|left;simpl;lia].
          right;split;reflexivity.
        * destruct N2;[|left;simpl;lia].
          right;split;reflexivity.
      + destruct Iu as (u1&u2&->&Iu1&Ih).
        * apply IHn in Ih as (I21&I22);clear IHn.
          apply Σ_lang in Iu1 as (g&Ig&Iu).
          apply in_map_iff in Ig as ((β1&β2)&<-&Iβ).
          apply pairs_spec in Iβ as (I11&I12).
          simpl in Iu.
          apply filter_binding_lang in Iu as (Iu&<-);
            [apply filter_binding_lang in Iu as (Iu&<-)|apply is_binding_finite_filter_binding];
            try apply Sq.
          simpl_binding.
          assert (square (𝗙 a1 u1) /\ square (𝗙 a2 u1)
                  /\ square (𝗙 a1 u2) /\ square (𝗙 a2 u2)) as (S11&S12&S21&S22)
              by (rewrite lower_squares_alt in I11,I12,I21,I22 by reflexivity;tauto).
          repeat rewrite <- prod_binding_maxBind by assumption.
          split.
          -- destruct (maxBind_square_disj S11 S21) as [-> | ->];assumption.
          -- destruct (maxBind_square_disj S12 S22) as [-> | ->];assumption.
    - destruct Iu as ((n&Iu)&I1&I2);exists n.
      revert u Iu I1 I2;induction n;intros u.
      + intros -> _;reflexivity.
      + intros (u1&u2&->&Iu1&Iu2).
        simpl_binding.
        intros I1 I2.
        cut (square (𝗙 a1 u1) /\ square (𝗙 a2 u1)
             /\ square (𝗙 a1 u2) /\ square (𝗙 a2 u2));[intros (S11&S12&S21&S22)|].
        * apply lower_squares_prod in I1 as (I11&I12);[|assumption|assumption|reflexivity].
          apply lower_squares_prod in I2 as (I21&I22);[|assumption|assumption|reflexivity].
          -- exists u1,u2;split;[reflexivity|].
             split;[|apply IHn;tauto].
             apply Σ_lang;exists (𝔉 a2 (𝗙 a2 u1) (𝔉 a1 (𝗙 a1 u1) e));split.
             ++ apply in_map_iff;exists (𝗙 a1 u1,𝗙 a2 u1);split;[|apply pairs_spec];tauto.
             ++ apply filter_binding_lang;
                  [apply is_binding_finite_filter_binding
                  |split;[apply filter_binding_lang|]];apply Sq||tauto.
        * repeat split.
          -- eapply is_binding_finite_bindings in Iu1;[|apply Sq].
             apply Sq in Iu1;apply Iu1.
          -- eapply is_binding_finite_bindings in Iu1;[|apply Sq].
             apply Sq in Iu1;apply Iu1.
          -- apply binding_finite_sqExpr_star in Bs as (Bs&Sq').
             apply (Sq' a1).
             apply is_binding_finite_bindings;[apply Bs|exists n;assumption].
          -- apply binding_finite_sqExpr_star in Bs as (Bs&Sq').
             apply (Sq' a2).
             apply is_binding_finite_bindings;[apply Bs|exists n;assumption].
  Qed.

  Lemma BiLowerExpr_αKA a1 N1 f1 a2 N2 f2 e f :
    is_binding_finite f -> e =α f ->
    BiLowerExpr a1 N1 f1 a2 N2 f2 e =α BiLowerExpr a1 N1 f1 a2 N2 f2 f .
  Proof.
    intros Bf E.
    pose proof Bf as Be;apply (is_binding_finite_ax_eq E) in Be.
    apply Σ_map_equiv_α.
    intros β _.
    apply filter_binding_αKA;[apply is_binding_finite_filter_binding|apply filter_binding_αKA];tauto.
  Qed.

  Lemma BiLowerExpr_αKA_inf a1 N1 f1 a2 N2 f2 e f :
    is_binding_finite f -> e <=α f ->
    BiLowerExpr a1 N1 f1 a2 N2 f2 e <=α BiLowerExpr a1 N1 f1 a2 N2 f2 f.
  Proof.
    intros Bf E.
    pose proof Bf as Be;apply (is_binding_finite_ax_eq E) in Be.
    apply Σ_bounded;intros g Ig.
    apply in_map_iff in Ig as (β&<-&Iβ).
    etransitivity;[|apply Σ_bigger,in_map_iff;exists β;split;[reflexivity|assumption]].
    apply filter_binding_αKA_inf;[apply is_binding_finite_filter_binding
                                 |apply filter_binding_αKA_inf];tauto.
  Qed.
 
  Notation Regexp := (@regexp letter).

  Definition TriRange N1 N2 k :=
    pairs (SplitRange N1 k)
          (flat_map (fun B => match B with
                           | (α1,(n,false,0)) => [(α1,n)]
                           | _ => []
                           end)
                    (factors (N2▶) k)).

  Notation " a #? e " := (freshExprB a e) (at level 80).

  Definition FunkyRange N K :=
    flat_map (fun b => factors b K) (lower_squares (N,false,N)).
  
  Fixpoint TriSplit_list a N1 b N2 (e : Regexp) :=
    match e with
    | e_zero | e_un => []
    | ⟪x⟫ => if (𝗳 a x =?= (S N1▶))&&(𝗳 b x =?= (N2▶))
            then [(⟪x⟫,un,un)]
            else []
    | e_add e f => (TriSplit_list a N1 b N2 e) ++ (TriSplit_list a N1 b N2 f)
    | e_prod e f =>
      if (test0 (e · f))
      then []
      else
        (map (fun P => (fst P,snd P·f)) (TriSplit_list a N1 b N2 e))
          ++ (flat_map (fun p => match p with
                              | (b1,b2) =>
                                map (fun P =>
                                       match P with
                                       | ((e1,e2),(f1,f2)) => (e1,e2·f1,f2)
                                       end)
                                    (pairs (splitStrict_list a N1 ((𝔉 b b1 e)))
                                           (split_binding b b2 f))
                              end)
                       (factors (N2,false,0) (sizeExpr e)))
          ++ (flat_map (fun p =>
                          match p with
                          | ((α,n),(β,m)) =>
                            (map (fun P => (𝔉 a α (𝔉 b β e) ·fst(fst P),snd(fst P),snd P))
                                 (TriSplit_list a n b m f))
                          end)
                       (TriRange N1 N2 (sizeExpr e)))
    | e_star e =>
      (map (fun P => (BiLowerExpr a N1 true b N2 false e ⋆·fst (fst P),snd(fst P),snd P·e⋆))
           (TriSplit_list a N1 b N2 e))
        ++ map (fun P =>
                  match P with
                  | ((e1,e2),(f1,f2),(b1,b2)) =>
                    
                    (BiLowerExpr a N1 true b N2 false e ⋆·𝔉 b b1 e1,
                     𝔉 b b2 e2·LowerExpr b N2 false e⋆·f1,
                     f2· e ⋆)
                  end)
        (pairs (pairs (splitStrict_list a N1 e)
                      (split_binding b (N2▶) e))
               (FunkyRange N2 (2*sizeExpr e)))
    end.

    Fixpoint TriSplitAct c a N1 b N2 (e : Regexp) :=
    match e with
    | e_zero | e_un => zero
    | ⟪x⟫ => if (𝗳 a x =?= (S N1▶))&&(𝗳 b x =?= (N2▶))
            then [(a,b);(b,c)]∙⟪x⟫
            else zero
    | e_add e f => (TriSplitAct c a N1 b N2 e) ∪ (TriSplitAct c a N1 b N2 f)
    | e_prod e f =>
      if (test0 (e · f))
      then zero
      else
        ((TriSplitAct c a N1 b N2 e)·f)
          ∪ Σ (map (fun p => match p with
                          | (b1,b2) =>
                            [(b,c)]∙splitActStrict c a N1 ((𝔉 b b1 e))
                                   · splitAct c b b2 f
                          end)
                   (factors (N2,false,0) (sizeExpr e)))
          ∪ Σ (map (fun p =>
                      match p with
                      | ((α,n),(β,m)) =>
                        [(a,b);(b,c)]∙𝔉 a α (𝔉 b β e) · TriSplitAct c a n b m f
                      end)
                   (TriRange N1 N2 (sizeExpr e)))
    | e_star e =>
      ([(a,b);(b,c)]∙BiLowerExpr a N1 true b N2 false e ⋆·TriSplitAct c a N1 b N2 e·e⋆)
        ∪([(a,b);(b,c)]∙(BiLowerExpr a N1 true b N2 false e ⋆)
            ·[(b,c)]∙LowerExpr b N2 false (splitActStrict c a N1 e)
            ·[(b,c)]∙(LowerExpr b N2 false e⋆)
            · splitAct c b (N2▶) e
            · e ⋆)
    end.

  Lemma TriSplitAct_support c a N b M e :
    ⌊TriSplitAct c a N b M e⌋⊆ c::a::b::⌊e⌋.
  Proof.
    revert N M;induction e;intros N M;simpl.
    - apply incl_nil.
    - apply incl_nil.
    - replace (e_add e1) with (join e1) by reflexivity.
      repeat rewrite support_join.
      apply incl_app;[rewrite IHe1|rewrite IHe2];intro;simpl;simpl_In;tauto.
    - destruct (test0 e1 || test0 e2);[apply incl_nil|].
      replace (e_prod e1) with (prod e1) by reflexivity.
      repeat rewrite support_join||rewrite support_prod.
      repeat apply incl_app.
      + rewrite IHe1;intro;simpl;simpl_In;tauto.
      + intro;simpl;simpl_In;tauto.
      + rewrite <- Σ_support.
        intros k Ik.
        apply In_support_list in Ik as (f&If&Ik).
        apply in_map_iff in If as ((?&?)&<-&_).
        rewrite support_prod,support_action in Ik;simpl_In in Ik.
        rewrite In_act_lists in Ik.
        rewrite splitActStrict_support,splitAct_support,filter_binding_support in Ik.
        simpl_In;simpl in Ik.
        destruct Ik as [Ik|Ik];[|tauto].
        revert Ik;unfold act;simpl;unfold_eqX;tauto.
      + rewrite <- Σ_support.
        intros k Ik.
        apply In_support_list in Ik as (f&If&Ik).
        apply in_map_iff in If as (((?&?)&(?&?))&<-&_).
        rewrite support_prod,support_action in Ik;simpl_In in Ik.
        rewrite In_act_lists in Ik.
        repeat rewrite filter_binding_support in Ik.
        rewrite IHe2 in Ik.
        simpl_In;simpl in Ik.
        destruct Ik as [Ik|Ik];[|tauto].
        revert Ik;unfold act;simpl.
        destruct_eqX k a;[tauto|].
        destruct_eqX k b;[tauto|].
        destruct_eqX k c;tauto.
    - replace (e_star e) with (star e) by reflexivity.
      repeat rewrite support_action||rewrite support_join||rewrite support_star||rewrite support_prod.
      intro d;simpl_In.
      repeat rewrite In_act_lists.
      repeat rewrite BiLowerExpr_support||rewrite LowerExpr_support.
      rewrite splitAct_support,splitActStrict_support.
      rewrite IHe.
      unfold act;simpl.
      destruct_eqX d a;[tauto|].
      destruct_eqX d b;[tauto|].
      destruct_eqX d c;[tauto|].
      tauto.
    - destruct (_&&_);[|apply incl_nil].
      intro d;rewrite support_action,In_act_lists.
      unfold act;simpl.
      destruct_eqX d a;[tauto|].
      destruct_eqX d b;[tauto|].
      destruct_eqX d c;tauto.
  Qed.
        
        
        
    
  Lemma TriSplitAct_test0 c a b N1 N2 e : test0 e = true -> test0 (TriSplitAct c a N1 b N2 e) = true.
  Proof.
    revert N1 N2;induction e;simpl;intros.
    - reflexivity.
    - discriminate.
    - apply andb_true_iff in H as (T1&T2).
      simpl;rewrite IHe1,IHe2 by assumption;reflexivity.
    - rewrite H;reflexivity.
    - discriminate.
    - discriminate.
  Qed.

  Lemma TriSplitAct_is_binding_finite c a N b M e :
    is_binding_finite e -> is_binding_finite (TriSplitAct c a N b M e).
  Proof.
    intros Be;repeat rewrite <- binding_finite_spec;revert N M.
    induction_bin_fin e Be;intros N M;simpl.
    - reflexivity.
    - reflexivity.
    - repeat destruct (_=?=_); reflexivity.
    - simpl;apply andb_true_iff;split.
      + apply IHe1.
      + apply IHe2.
    - rewrite T.
      simpl;repeat rewrite andb_true_iff;repeat split.
      + rewrite <- binding_finite_spec in B1,B2;simpl.
        rewrite IHe1,B2.
        apply orb_true_r.
      + rewrite binding_finite_Σ,forallb_forall.
        intros e Ie;apply in_map_iff in Ie as ((β1,β2)&<-&Ie).
        simpl;apply orb_true_iff;right.
        apply andb_true_iff;split.
        * apply binding_finite_spec,is_binding_finite_act,is_binding_finite_splitActStrict.
          apply is_binding_finite_filter_binding,B1.
        * apply binding_finite_spec,is_binding_finite_splitAct,B2.
      + rewrite binding_finite_Σ,forallb_forall.
        intros e Ie;apply in_map_iff in Ie as (((α,n),(β,m))&<-&Ie).
        simpl;apply orb_true_iff;right.
        apply andb_true_iff;split.
        * apply binding_finite_spec,is_binding_finite_act.
          apply is_binding_finite_filter_binding,is_binding_finite_filter_binding,B1.
        * apply IHe2.
    - rewrite T;reflexivity.
    - pose proof Sq as Be.
      apply sqExpr_bindings_finite_star in Be.
      apply andb_true_iff;split.
      + apply orb_true_iff;right.
        apply andb_true_iff;split.
        * apply orb_true_iff;right.
          apply andb_true_iff;split.
          -- cut (is_binding_finite ([(a, b); (b, c)] ∙ BiLowerExpr a N true b M false e⋆));
               [rewrite <- binding_finite_spec;simpl;tauto|].
             rewrite <-act_star;apply is_binding_finite_act.
             eapply is_binding_finite_ax_inf,proper_star_inf,KA_αKA_inf,BiLowerExpr_inf,Sq;assumption.
          -- apply IHe.
        * revert Be;rewrite <- binding_finite_spec;simpl;tauto.
      + apply orb_true_iff;right.
        apply andb_true_iff;split.
        * apply orb_true_iff;right.
          apply andb_true_iff;split.
          -- apply orb_true_iff;right.
             apply andb_true_iff;split.
             ++ apply orb_true_iff;right.
                apply andb_true_iff;split.
                ** cut (is_binding_finite ([(a, b); (b, c)] ∙ BiLowerExpr a N true b M false e⋆));
                     [rewrite <- binding_finite_spec;simpl;tauto|].
                   rewrite <-act_star;apply is_binding_finite_act.
                   eapply is_binding_finite_ax_inf,proper_star_inf,KA_αKA_inf,BiLowerExpr_inf,Sq;
                     assumption.
                ** rewrite binding_finite_spec.
                   apply is_binding_finite_act,LowerExpr_is_binding_finite,
                   is_binding_finite_splitActStrict,Sq.
             ++ cut (is_binding_finite ([(b, c)] ∙ (LowerExpr b M false e⋆)));
                     [rewrite <- binding_finite_spec;simpl;tauto|].
                apply is_binding_finite_act,LowerExpr_star_is_binding_finite,Be.
          -- rewrite binding_finite_spec.
             apply is_binding_finite_splitAct,Sq.
        *  revert Be;rewrite <- binding_finite_spec;simpl;tauto.
  Qed.


  Lemma split_star_strict e u1 u2 :
    ⟦e⋆⟧ (u1++u2) -> u1 <> [] ->
    exists w1 w2 w3 w4 : list letter,
      u1 = w1 ++ w2 /\ w2 <> [] /\ u2 = w3 ++ w4 /\ (⟦ e ⟧ ⋆) w1 /\ ⟦ e ⟧ (w2 ++ w3) /\ (⟦ e ⟧ ⋆) w4.
  Proof.
    intros (n&Iu).
    revert u1 u2 Iu;induction n;intros u2 u3 Iu P.
    +++ apply app_eq_nil in Iu as (->&->);exfalso;apply P;reflexivity.
    +++ destruct Iu as (w1&w2&EE&I1&I2).
        apply Levi in EE as (w&[(->&->)|(->&->)]).
        *** destruct_eqX w (@nil letter).
            ---- subst;rewrite app_nil_r in *;simpl in *.
                 exists [],w1,[],u3;repeat split;try tauto.
                 ++++ exists 0;reflexivity.
                 ++++ rewrite app_nil_r;assumption.
                 ++++ exists n;apply I2.
            ---- apply IHn in I2;[|assumption].
                 destruct I2 as (v1&v2&v3&v4&->&P'&->&(n1&Iv1)&?&?).
                 exists (w1++v1),v2,v3,v4;rewrite app_ass.
                 repeat split;try tauto.
                 exists (S n1),w1,v1;tauto.
        *** exists [],u2,w,w2;simpl.
            repeat split;try tauto.
            ---- exists 0;reflexivity.
            ---- exists n;apply I2.
  Qed.

  (* Definition DBalExpr a e := forall u, ⟦e⟧ u -> a ◁ u. *)
  (* Lemma DBalExpr_join a e1 e2 : DBalExpr a (e1∪e2) -> DBalExpr a e1 /\ DBalExpr a e2. *)
  (* Proof. intros h;split;intros u Iu;apply (h u);[left|right];assumption. Qed. *)
  (* Lemma DBalExpr_prod_left a e1 e2 : test0 e2 = false -> DBalExpr a (e1·e2) -> DBalExpr a e1. *)
  (* Proof. *)
  (*   intros T h u Iu. *)
  (*   apply test0_false in T as (v&Iv). *)
  (*   cut (⟦e1·e2⟧(u++v));[|exists u,v;tauto]. *)
  (*   intros h';apply h in h'. *)
  (*   revert h';unfold close_balanced;simpl_binding;lia. *)
  (* Qed. *)
    
  
  Lemma TriSplitAct_lang c a N b M e :
    is_binding_finite e -> (* freshExpr c e -> *) a<>b -> a<>c -> b<>c ->
    ⟦TriSplitAct c a N b M e⟧
      ≃ (fun u => exists u1 u2 u3, u = [(a,b);(b,c)]∙u1++[(b,c)]∙u2++u3
                           /\ ⟦e⟧ (u1++u2++u3)
                           /\ 𝗙 a u1 = S N▶
                           /\ 𝗙 b (u1++u2) = M▶
                           /\ forall v w, u1 = v++w -> ⎢v⎥ < ⎢u1⎥ -> 𝗙 a v <> S N▶).
  Proof.
    intros Be N1 N2 N3;revert N M;induction_bin_fin e Be;intros N M u;split;simpl.
    - intro F;exfalso;apply F.
    - intros (?&?&?&_&F&_);apply F.
    - intro F;exfalso;apply F.
    - intros ([]&?&?&_&F1&F2&_).
      + discriminate.
      + discriminate.
    - destruct_eqX (𝗳 a x) (S N,false,0);[destruct_eqX (𝗳 b x) (M,false,0)|];
        try (intro F;exfalso;apply F).
      simpl;intros ->.
      exists [x],[],[];rewrite app_nil_r;simpl_binding.
      repeat split;try tauto.
      intros [|l v] w heq;[inversion heq|simpl;lia].
      discriminate.
    - intros (u1&u2&u3&->&heq&E1&E2&Min).
      destruct u1;[discriminate|].
      inversion heq as [[e1 e2]];repeat apply app_eq_nil in e2 as (?&e2);subst.
      revert E1 E2;simpl_binding.
      intros -> ->;simpl_eqX;simpl.
      reflexivity.
    - unfold join,joinLang.
      (* assert (freshExpr c e1 /\ freshExpr c e2) as (F1&F2) *)
      (*     by (unfold freshExpr in *;rewrite <- Fc;simpl;split;intro;simpl_In;tauto). *)
      rewrite (IHe1 N M u),(IHe2 N M u).
      intros [I|I];destruct I as (u1&u2&u3&I);exists u1,u2,u3;tauto. 
    - unfold join,joinLang.
      (* assert (freshExpr c e1 /\ freshExpr c e2) as (F1&F2) *)
      (*     by (unfold freshExpr in *;rewrite <- Fc;simpl;split;intro;simpl_In;tauto). *)
      rewrite (IHe1 N M u),(IHe2 N M u).
      intros (u1&u2&u3&h1&[I|I]&h2);[left|right];exists u1,u2,u3;tauto.
    - rewrite T;simpl.
      (* assert (c # e1 /\ c # e2) as (F1&F2) by (rewrite support_prod in Fc;simpl_In in Fc;tauto). *)
      intros [[I|I]|I].
      + destruct I as (u'&u4&->&I&I4).
        apply IHe1 in I as (u1&u2&u3&->&Ih&E1&E2&Min).
        exists u1,u2,(u3++u4);repeat split.
        * repeat rewrite app_ass;reflexivity.
        * exists (u1++u2++u3),u4;repeat rewrite app_ass;tauto.
        * assumption.
        * assumption.
        * assumption.
      + apply Σ_lang in I as (e&Ie&Iu).
        apply in_map_iff in Ie as ((α1&α2)&<-&Iα).
        destruct Iu as (w1&w2&->&Iw1&Iw2).
        apply act_lang in Iw1.
        apply splitActStrict_lang in Iw1 as (u1&u2&Ew1&Iw1&E1&Min);
          [|apply is_binding_finite_filter_binding,B1].
        rewrite <-(act_bij [(b,c)]),act_p_pinv in Ew1;subst.
        apply filter_binding_lang in Iw1 as (Iw1&E2);[|assumption].
        apply splitAct_lang in Iw2 as (u3&u4&->&Iw2&P&E3);[|assumption].
        exists u1,(u2++u3),u4.
        repeat split.
        * replace [(a,b);(b,c)] with ([(a,b)]++[(b,c)]) by reflexivity.
          rewrite <- action_compose.
          repeat rewrite act_lists_app|| rewrite act_p_pinv||rewrite app_ass.
          f_equal.
          repeat rewrite action_compose.
          apply support_eq_action_eq;intros d Id.
          unfold act;simpl.
          (* assert (Fu1 : c # u1) *)
          (*   by (apply support_lang in Iw1;rewrite <- Iw1,support_list_app in F1;simpl_In in F1;tauto). *)
          destruct_eqX d a;simpl_eqX;[reflexivity|].
          destruct_eqX d c;simpl_eqX;[reflexivity|].
          destruct_eqX d b;simpl_eqX;reflexivity.
        * exists (u1++u2),(u3++u4);repeat rewrite app_ass;tauto.
        * assumption.
        * rewrite <- app_ass,𝗙_app,E2,E3.
          eapply factors_prod,Iα.
        * apply Min.
      + apply Σ_lang in I as (g&Ig&Iu).
        apply in_map_iff in Ig as (((α,n)&(β,m))&<-&I).
        unfold TriRange in I;apply pairs_spec in I as (Iα&Iβ).
        apply in_flat_map in Iβ as ((β1&((?&[])&[]))&Iβ&I);simpl in I;try tauto.
        destruct I as [I|F];[|tauto].
        inversion I;subst;clear I.
        destruct Iu as (u1&u'&->&I1&Iu).
        apply act_lang,filter_binding_lang in I1 as (I1&E1);
          [|apply is_binding_finite_filter_binding,B1].
        apply filter_binding_lang in I1 as (I1&E2); [|apply B1].
        apply IHe2 in Iu as (u2&u3&u4&->&I2&E3&E4&Min).
        clear IHe1 IHe2 .
        exists ([(a,b);(b,c)]∗∙u1++u2),u3,u4;repeat split.
        * rewrite act_lists_app,act_p_pinv.
          repeat rewrite app_ass;f_equal.
        * repeat rewrite app_ass;exists (([(a, b); (b, c)] ∗) ∙ u1),(u2 ++ u3 ++ u4);tauto.
        * rewrite 𝗙_app,E1,E3.
          apply SplitRange_result in Iα;tauto.
        * rewrite app_ass,𝗙_app,E2,E4.
          eapply factors_prod,Iβ.
        * intros v1 v2 Ew Len Ev1.
          apply Levi in Ew as (w&[(Ew&->)|(->&->)]).
          -- rewrite <- (act_bij [(a,b);(b,c)]),act_p_pinv in Ew.
             rewrite Ew in *;clear u1 Ew.
             rewrite act_pinv_p in E1,E2,I1,Len.
             apply SplitRange_result in Iα as (Eα&Minα).
             apply (Minα (𝗙 a w)).
             rewrite <- E1,<-Ev1;simpl_binding;reflexivity.
          -- set (u1' := ([(a, b); (b, c)] ∗) ∙ u1).
             replace (([(a, b); (b, c)] ∗) ∙ u1) with u1' in * by reflexivity.
             clear I1 I2 T B1 B2.
             apply factors_prod in Iβ;clear e2.
             apply SplitRange_result in Iα as (Eα&Minα);clear e1.
             assert (L' : 0<⎢v2⎥) by (repeat rewrite app_length in Len;lia).
             rewrite 𝗙_app,E1 in Ev1.
             apply destr_bind_prod_full in Ev1 as (Ev1&h).
             set (K:=d_binding(𝗙 a w));replace (d_binding(𝗙 a w)) with K in * by reflexivity.
             simpl_binding in E3.
             rewrite Ev1 in E3.
             apply destr_bind_prod_full in Eα as (_&h').
             replace (d_binding (S n,false,0)) with (S n) in * by reflexivity.
             destruct h' as [(h1&h2)| ->].
             ++ rewrite <- h2 in *;clear h2 N.
                apply destr_bind_prod_full in Iβ as (_&h').
                replace (d_binding (m,false,0)) with m in * by reflexivity.
                destruct h as [ (h3&h4) | h3].
                ** replace K with (S n) in * by lia.
                   apply (Min w v2);[reflexivity|solve_length|assumption].
                ** destruct α as ((D,F),C).
                   unfold d_binding in Minα,h3;simpl in *.
                   inversion h3 as [[E5 E6 E7]].
                   rewrite E6 in *;clear F E6.
                   rewrite E7 in *;clear C E7.
                   replace K with (S n) in * by lia.
                   apply (Min w v2);[reflexivity|solve_length|assumption].
             ++ apply (Minα (0,false,S n)).
                unfold prod_binding;reflexivity.
    - (* assert (c # e1 /\ c # e2) as (F1&F2) by (rewrite support_prod in Fc;simpl_In in Fc;tauto). *)
      rewrite T;intros (u1&u2&u3&->&(v1&v2&EE&Iv1&Iv2)&E1&E2&Min).
      levi EE;clear EE;subst.
      + destruct u2.
        * left;left.
          exists ([(a, b); (b, c)] ∙ v1),u3.
          split;[reflexivity|].
          split;[|assumption].
          apply IHe1.
          exists v1,[],[].
          repeat rewrite app_nil_r in *;repeat split.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        * left;right.
          assert (P: l::u2 <> []) by discriminate.
          revert Iv2 E2 P;generalize (l::u2);intros v2 Iv2 E2 P.
          apply Σ_lang;exists ([(b, c)] ∙ splitActStrict c a N (𝔉 b (𝗙 b v1) e1)
                                   · splitAct c b (𝗙 b v2) e2);split.
          -- apply in_map_iff;exists (𝗙 b v1,𝗙 b v2);split;[reflexivity|].
             apply factors_In;[|rewrite <-E2;simpl_binding;reflexivity].
             apply binding_finite_bound_size;tauto.
          -- exists ([(a, b); (b, c)] ∙ v1),([(b, c)] ∙ v2 ++ u3);split;[reflexivity|].
             split.
             ++ apply act_lang,splitActStrict_lang;
                  [apply is_binding_finite_filter_binding,B1|].
                exists v1,[];repeat split.
                ** rewrite app_nil_r.
                   repeat rewrite action_compose.
                   apply support_eq_action_eq.
                   intros d Id.
                   unfold act;simpl.
                   destruct_eqX d b;simpl_eqX;[reflexivity|].
                   destruct_eqX d c;simpl_eqX;[reflexivity|].
                   destruct_eqX d a;simpl_eqX;reflexivity.
                ** rewrite app_nil_r.
                   apply filter_binding_lang;[assumption|];tauto.
                ** assumption.
                ** assumption.
             ++ apply splitAct_lang;[assumption|].
                exists v2,u3;tauto.
      + right;apply Σ_lang.
        rewrite app_comm_cons in Iv2.
        assert (P : a0::w<>[]) by discriminate.
        revert Iv2 E1 E2 Min P;generalize (a0::w);clear a0 w;intros w Iv2 E1 E2 Min P.
        exists ([(a, b); (b, c)] ∙ 𝔉 a (𝗙 a v1) (𝔉 b (𝗙 b v1) e1)
                            · TriSplitAct c a (d_binding (𝗙 a w) -1) b (d_binding(𝗙 b (w++u2))) e2).
        split.
        * apply in_map_iff;exists ((𝗙 a v1,d_binding (𝗙 a w) -1),
                              (𝗙 b v1,d_binding(𝗙 b (w++u2))));split;[reflexivity|].
          apply pairs_spec;split.
          -- apply SplitRange_In.
             ++ assumption.
             ++ apply binding_finite_bound_size;assumption.
             ++ assumption.
             ++ assumption.
          -- apply in_flat_map;exists (𝗙 b v1,𝗙 b (w++u2));simpl;split.
             ++ apply factors_In.
                ** apply binding_finite_bound_size;assumption.
                ** rewrite <-E2;simpl_binding.
                   rewrite prod_assoc;reflexivity.
             ++ remember (𝗙 b (w++u2)) as β.
                rewrite app_ass,𝗙_app,<-Heqβ in E2.
                apply destr_bind_prod_full in E2 as (E2&h2).
                destruct β as ((x,y),z).
                unfold d_binding in E2;simpl in E2;inversion E2;subst.
                unfold d_binding;simpl;tauto.
        * exists ([(a, b); (b, c)] ∙ v1),([(a, b); (b, c)] ∙ w ++ [(b, c)] ∙ u2 ++ u3).
          repeat rewrite act_lists_app||rewrite app_ass;repeat split.
          -- rewrite act_lang,act_pinv_p.
             apply filter_binding_lang;[apply is_binding_finite_filter_binding,B1|].
             split;[|reflexivity].
             apply filter_binding_lang;tauto.
          -- apply IHe2.
             replace (S (d_binding (𝗙 a w) - 1)) with (d_binding (𝗙 a w)).
             ++ exists w,u2,u3;repeat split.
                ** assumption.
                ** rewrite 𝗙_app in E1.
                   apply destr_bind_prod in E1;apply E1.
                ** rewrite app_ass,𝗙_app in E2.
                   apply destr_bind_prod in E2;apply E2.
                ** intros w1 w2 -> Len Ew1.
                   apply (Min (v1++w1) w2).
                   --- repeat rewrite app_ass;reflexivity.
                   --- solve_length.
                   --- simpl_binding.
                       rewrite Ew1.
                       rewrite 𝗙_app in E1.
                       unfold d_binding.
                       rewrite <- (destr_bind_prod E1);apply E1.
             ++ rewrite 𝗙_app,destr_bind_prod_full in E1.
                destruct E1 as (E1&Min').
                destruct (d_binding (𝗙 a w));[|lia].
                exfalso;apply (Min v1 w).
                ** reflexivity.
                ** rewrite <- length_zero_iff_nil in P;solve_length.
                ** destruct Min' as [(FF&_)| ->];[lia|reflexivity].
      + rewrite app_comm_cons in E0;generalize dependent (a0::w);clear a0 w;intros w Iv1 EE.
        levi EE;clear EE;subst.
        * left;left.
          exists ([(a, b); (b, c)] ∙ u1 ++ [(b, c)] ∙ w),v2;rewrite app_ass.
          split;[reflexivity|].
          split;[|assumption].
          apply IHe1.
          exists u1,w,[].
          repeat split.
          -- rewrite app_nil_r;reflexivity.
          -- rewrite app_nil_r;assumption.
          -- assumption.
          -- assumption.
          -- assumption.
        * assert (P : a0::w0 <> []) by discriminate.
          rewrite app_comm_cons in Iv2;generalize dependent (a0::w0);clear a0 w0;intros w' Iv2 E2 P.
          left;right.
          apply Σ_lang;exists ([(b, c)] ∙ splitActStrict c a N (𝔉 b (𝗙 b (u1++w)) e1)
                                   · splitAct c b (𝗙 b w') e2);split.
          -- apply in_map_iff;exists (𝗙 b (u1++w),𝗙 b w');split;[reflexivity|].
             apply factors_In;[apply binding_finite_bound_size;tauto|].
             rewrite <-E2;simpl_binding;rewrite prod_assoc;reflexivity.
          -- exists ([(a, b); (b, c)] ∙ u1++[(b,c)]∙w),([(b, c)] ∙ w' ++ u3).
             repeat rewrite app_ass||rewrite act_lists_app;split;[reflexivity|].
             split.
             ++ apply act_lang,splitActStrict_lang;
                  [apply is_binding_finite_filter_binding,B1|].
                exists u1,w;repeat split.
                ** rewrite act_lists_app,act_pinv_p.
                   f_equal.
                   repeat rewrite action_compose.
                   apply support_eq_action_eq.
                   intros d Id.
                   unfold act;simpl.
                   destruct_eqX d b;simpl_eqX;[reflexivity|].
                   destruct_eqX d c;simpl_eqX;[reflexivity|].
                   destruct_eqX d a;simpl_eqX;reflexivity.
                ** apply filter_binding_lang;[assumption|];tauto.
                ** assumption.
                ** assumption.
             ++ apply splitAct_lang;[assumption|].
                exists w',u3;tauto.
        * rewrite app_comm_cons;generalize dependent (a0::w0);clear a0 w0;intros w' Iv1.
          left;left.
          exists ([(a, b); (b, c)] ∙ u1 ++ [(b, c)] ∙ u2++w'),v2;rewrite app_ass.
          repeat rewrite app_ass;split;[reflexivity|].
          split;[|assumption].
          apply IHe1.
          exists u1,u2,w';tauto.
    - rewrite T;intro h;exfalso;apply h.
    - rewrite T.
      intros (u1&u2&u3&_&I&_).
      assert (I1 : ⟦e1·e2⟧(u1++u2++u3)) by apply I;clear I.
      assert (I2 : test0 (e1·e2) = true) by apply T;clear T.
      apply test0_spec,soundness in I2.
      apply I2 in I1;apply I1.
    - assert (Be : is_binding_finite e) by apply Sq.
      assert (Bs : is_binding_finite (e⋆)) by apply sqExpr_bindings_finite_star,Sq.
      intros [I|I].
      + destruct I as (w&w3&->&(w1&w2&->&Iw1'&Iw2)&Iw3).
        assert (Iw1 : (⟦ [(a, b); (b, c)] ∙ (BiLowerExpr a N true b M false e ⋆)⟧) w1)
          by apply Iw1';clear Iw1'.
        apply act_lang,BiLowerExpr_star_lang in Iw1 as (Iw1&E1&E2);[|assumption].
        apply IHe in Iw2 as (u1&u2&u3&->&Iw2&E3&E4&Min).
        exists ([(a,b);(b,c)]∗∙w1++u1),u2,(u3++w3).
        rewrite act_lists_app,act_p_pinv.
        repeat rewrite app_ass.
        repeat split.
        * pose proof (ka_star_mid_split ⟦e⟧) as h;apply h;clear h.
          exists (([(a, b); (b, c)] ∗) ∙ w1++u1++u2++u3),w3.
          repeat rewrite app_ass.
          split;[reflexivity|split;[|assumption]].
          exists (([(a, b); (b, c)] ∗) ∙ w1),(u1++u2++u3);tauto.
        * simpl_binding.
          rewrite E3.
          apply lower_squares_alt in E1;[|reflexivity];revert E1;clear.
          simpl;generalize (𝗙 a  (([(b, c);(a, b)]) ∙ w1)).
          intros ((K&?)&?).
          unfold square,d_binding;simpl.
          intros (->&hyp);unfold prod_binding.
          destruct_ltb K (S N).
          -- destruct hyp as [hyp|(hyp&_)];lia.
          -- f_equal;f_equal;lia.
        * rewrite 𝗙_app,E4.
          apply lower_squares_prod_destr_false;assumption.
        * intros v1 v2 EE Len Ev1.
          apply Levi in EE as (w&[(EE&->)|(->&->)]).
          -- rewrite EE in *.
             apply lower_squares_alt in E1 as (h1&h2);[|reflexivity].
             revert h2 h1;unfold square;simpl_binding;rewrite Ev1.
             destruct (𝗙 a w) as ((D,F),C);unfold d_binding;simpl.
             intro h;assert (L : C<=N) by (destruct h as [h|(h&_)];lia);clear h.
             simpl_nat;intros ->;lia.
          -- generalize dependent (([(a, b); (b, c)] ∗) ∙ w1);clear w1.
             intros w1 Iw1 E1 _.
             simpl_binding.
             intros EE Len.
             apply destr_bind_prod_full in EE as (Ew1&EE).
             simpl_binding in E3;rewrite Ew1 in E3.
             generalize dependent (d_binding (𝗙 a w)).
             intros K E3 Ew EE.
             apply lower_squares_alt in E1 as (h1&h2);[|reflexivity].
             revert h2 h1;unfold square;simpl_binding. 
             destruct (𝗙 a w1) as ((D,F),C);unfold d_binding;simpl.
             intro h;assert (L : C<S N) by (destruct h as [h|(h&_)];lia);clear h.
             intros ->;unfold d_binding in EE;simpl in EE;simpl_nat.
             destruct EE as [(_&->)|EE];[|inversion EE;lia].
             apply (Min w v2).
             ++ reflexivity.
             ++ solve_length.
             ++ assumption.
      + destruct I as (?&u5&->&(?&u4&->&(?&u3&->&(u1&u2&->&Iu1'&Iu2)&Iu3')&Iu4)&Iu5).
        assert (Iu1 : ⟦ [(a, b); (b, c)] ∙ (BiLowerExpr a N true b M false e ⋆)⟧ u1)
          by apply Iu1';clear Iu1'.
        assert (Iu3 : ⟦ [(b, c)] ∙ (LowerExpr b M false e ⋆)⟧ u3)
          by apply Iu3';clear Iu3'.
        rewrite act_lang in Iu1,Iu2,Iu3.
        apply BiLowerExpr_star_lang in Iu1 as (Iu1&Ea1&Eb1);[|assumption].
        apply LowerExpr_lang in Iu2 as (Iu2&Eu2);[|apply is_binding_finite_splitActStrict,Be].
        apply splitActStrict_lang in Iu2 as (w1&w2&EE&Iu2&Ew1&Min);[|assumption].
        rewrite <- (act_bij [(b,c)]),act_p_pinv in EE;subst.
        apply LowerExpr_star_lang in Iu3 as (Iu3&Eu3);[|assumption].
        apply splitAct_lang in Iu4 as (w3&w4&->&Iu4&P&Ew3);[|assumption].
        exists (([(a, b); (b, c)] ∗) ∙ u1++w1),(w2++([(b, c)] ∗) ∙ u3++w3),(w4++u5).
        repeat split.
        * repeat rewrite act_lists_app||rewrite act_p_pinv||rewrite app_ass.
          f_equal;f_equal.
          rewrite action_compose;apply support_eq_action_eq;intros d Id.
          unfold act;simpl.
          destruct_eqX d b;simpl_eqX;[reflexivity|].
          destruct_eqX d c;simpl_eqX;[reflexivity|].
          destruct_eqX d a;simpl_eqX;reflexivity.
        * cut (⟦e⋆·e·e⋆·e·e⋆⟧≲⟦e⋆⟧).
          -- intro h;apply h;clear h.
             exists ((([(a, b); (b, c)] ∗) ∙ u1 ++ w1) ++ (w2 ++ ([(b, c)] ∗) ∙ u3 ++ w3) ++ w4),u5.
             repeat rewrite app_ass;split;[reflexivity|split;[|assumption]].
             exists ((([(a, b); (b, c)] ∗) ∙ u1 ++ w1) ++ (w2 ++ ([(b, c)] ∗) ∙ u3)),(w3 ++ w4).
             repeat rewrite app_ass;split;[reflexivity|split;[|assumption]].
             exists ((([(a, b); (b, c)] ∗) ∙ u1 ++ w1) ++ w2),(([(b, c)] ∗) ∙ u3).
             repeat rewrite app_ass;split;[reflexivity|split;[|assumption]].
             exists (([(a, b); (b, c)] ∗) ∙ u1),( w1 ++ w2).
             repeat rewrite app_ass;split;[reflexivity|split;[assumption|assumption]].
          -- simpl;etransitivity;[|apply ka_star_mid_split].
             apply proper_prod_inf;[|reflexivity].
             apply proper_prod_inf;[|reflexivity].
             apply ka_star_mid_split.
        * rewrite 𝗙_app,Ew1.
          apply lower_squares_prod_destr_true;assumption.
        * clear IHe.
          (* destruct_eqX b c. *)
          (* -- replace M with 0 in *. *)
          (*    ++ apply αfresh_support. *)
          (*       rewrite app_ass,<-(app_ass w1). *)
          (*       setoid_rewrite support_list_app. *)
          (*       apply support_lang in Iu1 as ->. *)
          (*       setoid_rewrite support_list_app. *)
          (*       apply support_lang in Iu2 as ->. *)
          (*       setoid_rewrite support_list_app. *)
          (*       apply support_lang in Iu3 as ->. *)
          (*       apply support_lang in Iu4;rewrite support_list_app in Iu4. *)
          (*       pose proof (Iu4 c) as Ic. *)
          (*       revert Ic Fc;rewrite support_star;clear;simpl_In;tauto. *)
          (*    ++ apply support_lang in Iu4;rewrite support_list_app in Iu4. *)
          (*       rewrite support_star,<- Iu4 in Fc. *)
          (*       rewrite αfresh_support in Ew3;[|simpl_In in Fc;tauto]. *)
          (*       inversion Ew3;tauto. *)
          -- repeat rewrite 𝗙_app.
             rewrite act_pinv_p in Eu2.
             rewrite Ew3,lower_squares_prod_destr_false;[|assumption].
             rewrite <- prod_assoc,(prod_assoc (𝗙 b w1)).
             rewrite 𝗙_app,𝗙_perm in Eu2;unfold act in Eu2;simpl in Eu2;revert Eu2.
             simpl_eqX;intros.
             rewrite lower_squares_prod_destr_false;[|assumption].
             rewrite lower_squares_prod_destr_false;[|assumption].
             reflexivity.
        * clear IHe Be Bs Eu2 w3 w4 Iu4 P Ew3 u5 Iu5 Eb1 Iu3 Eu3 Iu1.
          generalize dependent (([(a, b); (b, c)] ∗) ∙ u1);clear u1.
          intros u1 Eu1.
          intros v1 v2 EE Len Ev1.
          apply Levi in EE as (w&[(->&->)|(->&->)]).
          -- apply lower_squares_alt in Eu1 as (h1&h2);[|reflexivity].
             revert h2 h1;unfold square;simpl_binding;rewrite Ev1.
             destruct (𝗙 a w) as ((D,F),C);unfold d_binding;simpl.
             intro h;assert (L : C<=N) by (destruct h as [h|(h&_)];lia);clear h.
             simpl_nat;intros ->;lia.
          -- simpl_binding in Ew1;simpl_binding in Ev1.
             apply destr_bind_prod_full in Ev1 as (Ev1&EE).
             apply destr_bind_prod_full in Ew1 as (Ew1&EE').
             generalize dependent (d_binding (𝗙 a w)).
             generalize dependent (d_binding (𝗙 a v2)).
             intros K1 EK1 K2 h1 EK2 h2.
             rewrite EK2 in *.
             apply lower_squares_alt in Eu1 as (h3&h4);[|reflexivity].
             revert h3 h4;unfold square;simpl_binding. 
             destruct (𝗙 a u1) as ((D,F),C);unfold d_binding;simpl.
             intros <-;intro h;assert (L : C<S N) by (destruct h as [h|(h&_)];lia);clear h.
             unfold d_binding in *;simpl in *.
             simpl_nat.
             destruct h2 as [(_&->)|h2].
             ++ apply (Min w v2);[reflexivity|solve_length|assumption].
             ++ inversion h2;lia.
    - intros (u1&u2&u3&->&Iu'&Ea&Eb&Min).
      cut ((exists w1 w2 w3 w4, u1 = w1 ++ w2
                          /\ w2 <> []
                          /\ u3 = w3++w4
                          /\ ⟦e⋆⟧ w1
                          /\ ⟦e⟧ (w2++u2++w3)
                          /\ ⟦e⋆⟧ w4)
           \/ (exists w1 w2 w3 w4 w5 w6 w7,
                 u1 = w1 ++ w2
                 /\ w2 <> []
                 /\ u2 = w3 ++ w4 ++ w5
                 /\ w5 <> []
                 /\ u3 = w6++w7
                 /\ ⟦e⋆⟧ w1
                 /\ ⟦e⟧ (w2++w3)
                 /\ ⟦e⋆⟧ w4
                 /\ ⟦e⟧ (w5++w6)
                 /\ ⟦e⋆⟧ w7)).
      + assert (Be : is_binding_finite e) by apply Sq.
        assert (Bs : is_binding_finite (e⋆)) by apply sqExpr_bindings_finite_star,Sq.
        clear Iu';intros [(w1&w2&w3&w4&->&P&->&I1&I2&I3)
                         |(w1&w2&w3&w4&w5&w6&w7&->&P1&->&P2&->&I1&I2&I3&I4&I5)].
        * left;exists ([(a, b); (b, c)] ∙ (w1 ++ w2) ++ [(b, c)] ∙ u2 ++ w3),w4.
          repeat rewrite app_ass;split;[reflexivity|split;[|assumption]].
          exists ([(a, b); (b, c)] ∙ w1),([(a, b); (b, c)] ∙w2 ++ [(b, c)] ∙ u2 ++ w3).
          rewrite act_lists_app;repeat rewrite app_ass;split;[reflexivity|].
          assert (Sq1: square (𝗙 a w1))
            by (apply sqExpr_star in Sq as (_&Sq);apply (Sq a),is_binding_finite_bindings;assumption).
          assert (Sq2: square (𝗙 b w1))
            by (apply sqExpr_star in Sq as (_&Sq);apply (Sq b),is_binding_finite_bindings;assumption).
          unfold square,d_binding in Sq1,Sq2.
          remember (𝗙 a w1) as β1;remember (𝗙 b w1) as β2.
          destruct β1 as ((K1,ff1),?),β2 as ((K2,ff2),?);simpl in *;subst.
          rewrite app_ass in Eb;rewrite 𝗙_app,destr_bind_prod_full in Ea,Eb.
          destruct Ea as (Ea&Ha),Eb as (Eb&Hb).
          rewrite <- Heqβ1 in Ha;rewrite <-Heqβ2 in Hb.
          replace (d_binding (K2,ff2,K2)) with K2 in * by reflexivity.
          replace (d_binding (K1,ff1,K1)) with K1 in * by reflexivity.
          simpl in *.
          remember (𝗙 a w2) as α1;remember (𝗙 b (w2++u2)) as α2.
          destruct α1 as ((K1',ff1'),X1),α2 as ((K2',ff2'),X2);simpl in *;subst.
          replace (d_binding (K2',ff2',X2)) with K2' in * by reflexivity.
          replace (d_binding (K1',ff1',X1)) with K1' in * by reflexivity.
          inversion Ea;subst;inversion Eb;subst;clear Ea Eb;simpl_nat.
          destruct Ha as [(L&->)|FF];[split|exfalso].
          -- cut  (⟦ [(a, b); (b, c)] ∙ (BiLowerExpr a N true b M false e⋆) ⟧ ([(a, b); (b, c)] ∙ w1));
               [intro I;apply I|].
             rewrite act_lang,act_pinv_p.
             apply BiLowerExpr_star_lang;[assumption|].
             split;[assumption|].
             split.
             ++ apply lower_squares_alt;[reflexivity|].
                rewrite <- Heqβ1;split;[reflexivity|].
                unfold d_binding;simpl;rewrite orb_true_r.
                destruct_eqX K1 N;[right;split;reflexivity|left;lia].
             ++ apply lower_squares_alt;[reflexivity|].
                rewrite <- Heqβ2;split;[reflexivity|].
                unfold d_binding;simpl;rewrite orb_false_r,negb_true_iff.
                destruct Hb as [(Lb&->)|hyp].
                ** left;assumption.
                ** inversion hyp as [[h1 h2 h3]];subst.
                   right;split;reflexivity.
          -- apply IHe.
             exists w2,u2,w3.
             repeat split.
             ++ assumption.
             ++ rewrite <- Heqα1;reflexivity.
             ++ rewrite <- Heqα2.
                destruct Hb as [(_&->)|Hb];[reflexivity|].
                inversion Hb;subst;reflexivity.
             ++ intros v1 v2 -> Len Ev1.
                apply (Min (w1++v1) v2).
                ** rewrite app_ass;reflexivity.
                ** solve_length.
                ** simpl_binding;apply destr_bind_prod_full.
                   rewrite Ev1,<-Heqβ1;unfold d_binding;simpl.
                   split;[reflexivity|].
                   simpl_nat;left;tauto.
          -- inversion FF;subst.
             cut (d_binding (𝗙 a w1) >= S N);[|rewrite <- Heqβ1;unfold d_binding;simpl;lia].
             intros h;apply exists_prefix_destr_binding in h as (v1&v2&->&Ev1).
             rewrite <- length_zero_iff_nil in P;rewrite app_ass in Min.
             apply (Min v1 (v2++w2));[reflexivity|solve_length|assumption].
        * assert ((square (𝗙 b w1)
                  /\ square (𝗙 b (w2++w3))
                  /\ square (𝗙 b w4))
                  /\ 𝗙 b w5 = (M,false,0)
                  /\ 𝗙 b ((w1 ++ w2) ++ w3 ++ w4) ∈ lower_squares (M,false,M)) as Hb.
          -- clear IHe.
             apply (is_binding_finite_bindings Bs b) in I1.
             apply (is_binding_finite_bindings Bs b) in I3.
             apply (is_binding_finite_bindings Be b) in I2.
             pose proof (sqExpr_star Sq) as (_&Sq').
             destruct Sq as (_&Sq).
             apply Sq in I2;apply Sq' in I1;apply Sq' in I3.
             split;[tauto|].
             cut (square (𝗙 b (w1++w2++w3++w4))).
             ++ revert Eb;clear.
                repeat rewrite <- app_ass;generalize (((w1 ++ w2) ++ w3) ++ w4).
                intros w;simpl_binding;intros Ew Sq.
                apply destr_bind_prod_full in Ew as (E1&E2).
                rewrite Sq in E2.
                remember (d_binding(𝗙 b w5)) as K.
                rewrite E1 in *;clear w5 E1 HeqK.
                destruct (𝗙 b w) as ((x,y),z);unfold square,d_binding in *;simpl in *;subst.
                simpl_nat.
                destruct E2 as [(L&->)|E2].
                ** split;[reflexivity|].
                   apply lower_squares_alt;[reflexivity|].
                   split;[reflexivity|].
                   simpl;tauto.
                ** inversion E2;subst.
                   split;[reflexivity|].
                   apply lower_squares_alt;[reflexivity|].
                   split;[reflexivity|].
                   simpl;tauto.
             ++ rewrite <- (app_ass w2).
                generalize dependent (w2++w3).
                revert I1 I3;clear.
                intros S1 S2 w S3.
                unfold square in *;simpl_binding.
                rewrite S1,S2,S3;lia.
          -- destruct Hb as ((Sq1&Sq23&Sq4)&E5&I).
             rewrite app_ass,<-(app_ass w2),𝗙_app,𝗙_app in I.
             apply lower_squares_prod in I as (Iw1&I);[ |assumption
                                                        |revert Sq4 Sq23;generalize (w2++w3);
                                                         clear;intros w;unfold square;simpl_binding;
                                                         intros -> ->;lia
                                                        |reflexivity].
             apply lower_squares_prod in I as (Iw23&Iw4);try reflexivity||assumption.
             assert (square (𝗙 a w1)
                     /\ 𝗙 a w2 = S N▶
                     /\ 𝗙 a w1 ∈ lower_squares (N,true,N)) as Ha.
             ++ apply (is_binding_finite_bindings Bs a) in I1.
                pose proof (sqExpr_star Sq) as (_&Sq').
                apply Sq' in I1.
                split;[tauto|].
                revert I1 Min P1 Ea;clear;simpl_binding.
                remember (𝗙 a w1) as B1.
                destruct B1 as ((K&ff)&?).
                unfold square,d_binding;simpl;intros ->.
                remember (𝗙 a w2) as B2.
                destruct B2 as ((K'&ff')&L').
                intros Min P Ew;apply destr_bind_prod_full in Ew as (E1&E2).
                unfold d_binding in *;simpl in *.
                inversion E1;subst;clear E1;simpl_nat.
                destruct E2 as [(L&->)|E2].
                ** split;[reflexivity|].
                   apply lower_squares_alt;[|split];try reflexivity.
                   simpl;rewrite orb_true_r.
                   destruct_eqX K N;[tauto|left;lia].
                ** inversion E2;subst.
                   exfalso.
                   cut (d_binding (𝗙 a w1) >= S N);[|rewrite <- HeqB1;unfold d_binding;simpl;lia].
                   intros h;apply exists_prefix_destr_binding in h as (v1&v2&->&Ev1).
                   rewrite <- length_zero_iff_nil in P;rewrite app_ass in Min.
                   apply (Min v1 (v2++w2));[reflexivity|solve_length|assumption].
             ++ destruct Ha as (Sq1'&Ew2&Iw1').
                (* destruct_eqX b c;subst. *)
                (* ** replace (cons (a,c)) with (app [(a,c)]) by reflexivity. *)
                (*    repeat rewrite <- action_compose. *)
                (*    assert (Ec : ([(c,c)]:perm)≃[]) by apply perm_a_a_eq_nil. *)
                (*    replace ([(c, c)] ∙ (w1 ++ w2)) *)
                (*      with (w1++w2) by (rewrite Ec,act_nil;reflexivity). *)
                (*    replace ([(c, c)] ∙ (w3 ++ w4++w5)) *)
                (*      with (w3++w4++w5) by (rewrite Ec,act_nil;reflexivity). *)
                (*    replace actReg with act by reflexivity. *)
                (*    left. *)
                (*    exists ([(a, c)] ∙ (w1 ++ w2) ++ w3),(w4 ++ w5 ++ w6++w7). *)
                (*    repeat rewrite app_ass;split;[reflexivity|]. *)
                (*    split. *)
                (*    --- rewrite act_lists_app. *)
                (*        exists ([(a,c)]∙w1),([(a,c)]∙w2++w3). *)
                (*        repeat rewrite app_ass;split;[reflexivity|]. *)
                (*        split. *)
                (*        +++ cut (⟦ [(a, c)] ∙ ([(c, c)] ∙ BiLowerExpr a N true c M false e ⋆) ⟧ *)
                (*                   ([(a, c)] ∙ w1));[intro I;apply I|]. *)
                (*            rewrite act_lang,Ec,act_nil,act_pinv_p. *)
                (*            apply BiLowerExpr_star_lang;repeat split. *)
                (*            *** assumption. *)
                (*            *** assumption. *)
                (*            *** assumption. *)
                (*            *** assumption. *)
                (*        +++ apply IHe;[assumption|]. *)
                (*            exists w2,w3,[]. *)
                (*            replace (cons (a,c)) with (app [(a,c)]) by reflexivity. *)
                (*            repeat rewrite <- action_compose. *)
                (*            split;[rewrite act_nil,app_nil_r;f_equal;[f_equal|]; *)
                (*                   rewrite Ec,act_nil;reflexivity|]. *)
                (*            rewrite app_nil_r;split;[assumption|]. *)
                (*            split;[assumption|]. *)
                (*            split. *)
                (*            *** replace M with 0. *)
                (*                ---- apply αfresh_support. *)
                (*                     apply support_lang in I2 as ->;assumption. *)
                (*                ---- cut ((M,false,0)=ε);[intros hyp;inversion hyp;reflexivity|]. *)
                (*                     rewrite <- E5. *)
                (*                     apply αfresh_support. *)
                (*                     apply support_lang in I4. *)
                (*                     rewrite <- I4,support_list_app in Fc. *)
                (*                     simpl_In in Fc;tauto. *)
                (*            *** intros v1 v2 -> Len Ev. *)
                (*                apply (Min (w1++v1) v2). *)
                (*                ---- rewrite app_ass;reflexivity. *)
                (*                ---- solve_length. *)
                (*                ---- simpl_binding;rewrite Ev. *)
                (*                     apply lower_squares_prod_destr_true;assumption. *)
                (*    --- pose proof (ka_star_mid_split ⟦e⟧) as hyp;apply hyp. *)
                (*        exists (w4++w5++w6),w7. *)
                (*        repeat rewrite app_ass;split;[reflexivity|split;[|assumption]]. *)
                (*        exists w4,(w5++w6);tauto. *)
                (* ** *) right.  
                   exists ([(a, b); (b, c)] ∙ (w1 ++ w2) ++ [(b, c)] ∙ (w3 ++ w4 ++ w5) ++ w6),w7.
                   repeat erewrite app_ass;split;[reflexivity|split;[|assumption]].
                   exists ([(a, b); (b, c)] ∙ (w1 ++ w2) ++ [(b, c)] ∙ (w3 ++ w4)),([(b, c)] ∙ w5 ++ w6).
                   repeat erewrite app_ass||rewrite act_lists_app;split;[reflexivity|split].
                   --- exists ([(a, b); (b, c)] ∙ (w1 ++ w2) ++ [(b, c)] ∙ w3),([(b, c)] ∙ w4).
                       repeat erewrite app_ass||rewrite act_lists_app;split;[reflexivity|split].
                       +++ exists ([(a, b); (b, c)] ∙ w1),([(a, b); (b, c)] ∙ w2 ++ [(b, c)] ∙ w3).
                           repeat erewrite app_ass||rewrite act_lists_app;split;[reflexivity|split].
                           *** cut (⟦[(a, b); (b, c)]∙ (BiLowerExpr a N true b M false e⋆) ⟧
                                      ([(a, b); (b, c)] ∙ w1));[intros I;apply I|].
                               rewrite act_lang,act_pinv_p.
                               apply BiLowerExpr_star_lang;repeat split;try assumption.
                           *** apply act_lang,LowerExpr_lang;
                                 [apply is_binding_finite_splitActStrict,Be|].
                               rewrite act_lists_app,act_pinv_p.
                               split.
                               ---- apply splitActStrict_lang;[assumption|].
                                    exists w2,w3;repeat split.
                                    ++++ f_equal.
                                         rewrite action_compose;apply support_eq_action_eq.
                                         intros d Id.
                                         unfold act;simpl.
                                         destruct_eqX d b;simpl_eqX;[reflexivity|].
                                         destruct_eqX d c;simpl_eqX;[reflexivity|].
                                         destruct_eqX d a;simpl_eqX;reflexivity.
                                    ++++ assumption.
                                    ++++ assumption.
                                    ++++ intros v1 v2 -> Len Ev1.
                                         apply (Min (w1++v1) v2).
                                         **** rewrite app_ass;reflexivity.
                                         **** solve_length.
                                         **** simpl_binding;rewrite Ev1.
                                              apply lower_squares_prod_destr_true;assumption.
                               ---- rewrite 𝗙_app;rewrite 𝗙_perm,𝗙_perm.
                                    unfold act;simpl;simpl_eqX.
                                    rewrite <- 𝗙_app;assumption.
                       +++ cut (⟦[(b, c)]∙ (LowerExpr b M false e⋆) ⟧
                                  ([(b, c)] ∙ w4));[intros I;apply I|].
                           rewrite act_lang,act_pinv_p.
                           apply LowerExpr_star_lang;repeat split;try assumption.
                   --- apply splitAct_lang;[assumption|].
                       exists w5,w6;repeat split;assumption.
      + assert (P: u1 <> []) by (intros ->;discriminate).
        assert (Iu : ⟦e⋆⟧ (u1++u2++u3)) by apply Iu';clear Iu'.
        apply split_star_strict in Iu as (w1&w2&w3&w4&->&P'&EE&I1&I2&I3);[|assumption].
        apply Levi in EE as (w&[(->&->)|(->&->)]).
        * destruct_eqX w (@nil letter).
          -- subst;simpl in *.
             left;exists w1,w2,[],u3.
             repeat split;try tauto.
             repeat rewrite app_nil_r;assumption.
          -- assert (Iu : ⟦e⋆⟧ (w++u3)) by apply I3;clear I3.
             apply split_star_strict in Iu as (v1&v2&v3&v4&->&P''&->&I1'&I2'&I3');[|assumption].
             right;exists w1,w2,w3,v1,v2,v3,v4.
             repeat split;try tauto.
        * left;exists w1,w2,w,w4;repeat split;try tauto.
  Qed.
  
  Lemma TriSplitAct_act p c a N b M e :
    p∙TriSplitAct c a N b M e = TriSplitAct (p∙c) (p∙a) N (p∙b) M (p∙e).
  Proof.
    revert N M;induction e;intros N M;
      replace act with actReg by reflexivity;simpl;
        replace actReg with act by reflexivity;try reflexivity.
    - rewrite IHe1,IHe2;reflexivity.
    - repeat rewrite test0_act.
      repeat rewrite sizeExpr_act.
      destruct (test0 e1 || test0 e2);[reflexivity|].
      repeat rewrite act_join.
      f_equal;[f_equal|].
      + rewrite <- IHe1;reflexivity.
      + clear IHe1 IHe2.
        rewrite Σ_act;f_equal.
        unfold act at 1,act_lists;rewrite map_map.
        apply map_ext.
        intros (α1,α2).
        rewrite act_prod;f_equal.
        * rewrite action_compose,commute_perm_transpose,<-action_compose.
          f_equal.
          rewrite splitActStrict_act;f_equal.
          apply filter_binding_act.
        * apply splitAct_act.
      + rewrite Σ_act;f_equal.
        unfold act at 1,act_lists;rewrite map_map.
        apply map_ext.
        intros ((α1,N1),(α2,N2)).
        rewrite act_prod;f_equal.
        * replace (cons (a,b)) with (app[(a,b)]) by reflexivity.
          rewrite action_compose.
          rewrite <-app_ass, (commute_perm_transpose p).
          rewrite app_ass,(commute_perm_transpose p).
          rewrite <-app_ass,<- action_compose;f_equal.
          rewrite filter_binding_act;f_equal.
          apply filter_binding_act.
        * apply IHe2.
    - rewrite IHe;clear IHe.
      repeat rewrite <- splitAct_act.
      repeat rewrite <- splitActStrict_act.
      repeat rewrite <- LowerExpr_act.
      repeat rewrite <- BiLowerExpr_act.
      replace e_add with join by reflexivity.
      replace e_prod with prod by reflexivity.
      replace e_star with star by reflexivity.
      f_equal.
      + f_equal;f_equal.
        replace (cons (a,b)) with (app[(a,b)]) by reflexivity.
        rewrite action_compose.
        rewrite <-app_ass, (commute_perm_transpose p).
        rewrite app_ass,(commute_perm_transpose p).
        rewrite <-app_ass,<- action_compose;reflexivity.
      + f_equal;f_equal;f_equal.
        * f_equal.
          -- replace (cons (a,b)) with (app[(a,b)]) by reflexivity.
             rewrite action_compose.
             rewrite <-app_ass, (commute_perm_transpose p).
             rewrite app_ass,(commute_perm_transpose p).
             rewrite <-app_ass,<- action_compose;reflexivity.
          -- rewrite action_compose, (commute_perm_transpose p),<-action_compose;reflexivity.
        * rewrite action_compose, (commute_perm_transpose p),<-action_compose;reflexivity.
    - repeat rewrite 𝗳_perm,act_pinv_p.
      destruct (𝗳 a x =?= _ && 𝗳 b x =?= _);[|reflexivity].
        replace (cons (a,b)) with (app[(a,b)]) by reflexivity.
        rewrite action_compose.
        rewrite <-app_ass, (commute_perm_transpose p).
        rewrite app_ass,(commute_perm_transpose p).
        rewrite <-app_ass,<- action_compose;reflexivity.
  Qed.
  
  Lemma TriSplitAct_KA c a N b M e f :
    is_binding_finite f -> a<>b -> a<>c -> b<>c ->
    e =KA f -> TriSplitAct c a N b M e =KA TriSplitAct c a N b M f.
  Proof.
    intros Bf Fe Ff Nab E.
    apply CompletenessKA.
    pose proof Bf as Be.
    apply (is_binding_finite_ax_eq (KA_αKA E)) in Be.
    apply soundness in E.
    repeat rewrite TriSplitAct_lang by assumption.
    intro u;split;intros (u1&u2&u3&->&Iu&hyp);apply E in Iu;exists u1,u2,u3;tauto.
  Qed.

  Lemma TriSplitAct_KA_inf c a N b M e f :
    is_binding_finite f -> a<>b -> a<>c -> b<>c ->
    e <=KA f -> TriSplitAct c a N b M e <=KA TriSplitAct c a N b M f.
  Proof.
    unfold ax_inf;intros Bf N1 N2 N3 Ef.
    rewrite <- (TriSplitAct_KA N M Bf N1 N2 N3 Ef) at 2.
    reflexivity.
  Qed.

  Lemma TriSplitAct_TriSplit_list c a N b M e :
    is_binding_finite e -> a<>b -> a<>c -> b<>c ->
    TriSplitAct c a N b M e =KA Σ(map (fun P => ([(a,b);(b,c)]∙fst(fst P)·[(b,c)]∙snd (fst P)·snd P))
                                      (TriSplit_list a N b M e)).
  Proof.
    intros Be N1 N2 N3;revert N M.
    induction_bin_fin e Be;intros N M.
    - reflexivity.
    - reflexivity.
    - simpl.
      destruct (𝗳 a x =?= (S N, false, 0) && 𝗳 b x =?= (M, false, 0));[|reflexivity].
      simpl.
      etransitivity;[|symmetry;apply right_unit].
      etransitivity;[|symmetry;apply right_unit].
      unfold act at 3;simpl.
      replace e_un with un by reflexivity.
      etransitivity;[|symmetry;apply right_unit].
      reflexivity.
    - simpl;rewrite IHe1,IHe2.
      rewrite map_app;apply algebra.Σ_app.
    - simpl;rewrite T.
      repeat rewrite map_app.
      rewrite IHe1.
      rewrite <- app_ass.
      etransitivity;[|apply algebra.Σ_app].
      apply proper_join;[etransitivity;[|apply algebra.Σ_app];apply proper_join|].
      + etransitivity;[apply Σ_distr_r|].
        repeat rewrite map_map.
        apply Σ_map_equiv.
        intros ((f1,f2),f3) _;simpl.
        symmetry;apply mon_assoc.
      + clear IHe1 IHe2.
        induction (factors (M,false,0) (sizeExpr e1)) as [|(α1,α2) l];
          [reflexivity|].
        simpl.
        rewrite map_app.
        etransitivity;[|apply algebra.Σ_app].
        apply proper_join;[|apply IHl];clear IHl.
        pose proof (splitActStrict_splitStrict_list c a N (𝔉 b α1 e1)) as EE.
        apply (KA_act [(b,c)]) in EE as ->.
        Transparent splitAct.
        unfold splitAct.
        rewrite Σ_act.
        etransitivity;[apply Σ_distr_r|].
        unfold act at 2,act_lists.
        rewrite map_map.
        apply ax_inf_PartialOrder;unfold Basics.flip;split;
          apply Σ_bounded;intros g Ig.
        * apply in_map_iff in Ig as (f&<-&If).
          apply in_map_iff in If as ((f1&f2)&<-&If).
          simpl.
          etransitivity;[apply ax_eq_inf,Σ_distr_l|].
          rewrite map_map.
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
          simpl.
          rewrite act_prod,action_compose;simpl.
          transitivity ((([(a,b); (b, c)] ∙ f1) · ([(b, c)] ∙ (f2 · g1))) · g2).
          -- rewrite act_prod.
             apply ax_eq_inf.
             etransitivity;[apply mon_assoc|].
             apply proper_prod;[|reflexivity].
             etransitivity;[symmetry;apply mon_assoc|].
             apply proper_prod;[|reflexivity].
             erewrite equiv_perm_act;[reflexivity| |reflexivity].
             intro d;unfold act;simpl.
             destruct_eqX d a;simpl_eqX;[reflexivity|].
             destruct_eqX d b;simpl_eqX;[reflexivity|].
             destruct_eqX d c;simpl_eqX;reflexivity.
          -- apply Σ_bigger,in_map_iff.
             exists (f1,f2 ·g1,g2);split;[reflexivity|].
             apply in_map_iff;exists ((f1,f2),(g1,g2));split;[reflexivity|].
             apply pairs_spec;tauto.
        * apply in_map_iff in Ig as (((f1,f2),f3)&<-&If).
          apply in_map_iff in If as (((g1,g2),(h1,h2))&heq&I).
          symmetry in heq;inversion heq;clear heq;subst.
          apply pairs_spec in I as (Ig & Ih).
          simpl.
          transitivity ([(b,c)]∙([(a, c)] ∙ g1 · g2)·
                               Σ (map (fun p  => [(b, c)] ∙ fst p · snd p) (split_binding b α2 e2))).
          -- transitivity ([(b,c)]∙([(a, c)] ∙ g1 · g2)· ([(b,c)]∙ h1 ·h2)).
             ++ etransitivity;[|apply ax_eq_inf;symmetry;apply mon_assoc].
                apply proper_prod_inf;[|reflexivity].
                repeat rewrite act_prod.
                etransitivity;[apply ax_eq_inf,mon_assoc|].
                apply proper_prod_inf;[|reflexivity].
                apply proper_prod_inf;[|reflexivity].
                apply ax_eq_inf.
                rewrite action_compose;simpl.
                erewrite equiv_perm_act;[reflexivity| |reflexivity].
                intro d;unfold act;simpl.
                destruct_eqX d a;simpl_eqX;[reflexivity|].
                destruct_eqX d b;simpl_eqX;[reflexivity|].
                destruct_eqX d c;simpl_eqX;reflexivity.
             ++ apply proper_prod_inf;[reflexivity|].
                apply Σ_bigger,in_map_iff;exists (h1,h2);tauto.
          -- apply Σ_bigger,in_map_iff.
             exists ([(a,c)]∙g1·g2);split;[reflexivity|].
             apply in_map_iff;exists (g1,g2);tauto.
      + clear IHe1;apply ax_inf_PartialOrder;unfold Basics.flip;split;
          apply Σ_bounded;intros g Ig.
        * apply in_map_iff in Ig as (((b1,n1),(b2,n2))&<-&Ib).
          rewrite IHe2.
          etransitivity;[apply ax_eq_inf,Σ_distr_l|].
          rewrite map_map.
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as (((f1,f2),f3)&<-&If).
          simpl.
          etransitivity;[apply ax_eq_inf,mon_assoc|].
          etransitivity;[apply proper_prod_inf;[apply ax_eq_inf,mon_assoc|reflexivity]|].
          rewrite <- act_prod.
          apply Σ_bigger,in_map_iff.
          exists (𝔉 a b1 (𝔉 b b2 e1) · f1, f2, f3).
          split;[reflexivity|].
          apply in_flat_map;exists ((b1,n1),(b2,n2));split;[assumption|].
          apply in_map_iff;exists (f1,f2,f3);tauto.
        * apply in_map_iff in Ig as (((f1,f2),f3)&<-&If).
          apply in_flat_map in If as (((b1,n1),(b2,n2))&Ib&If).
          apply in_map_iff in If as (((g1,g2),g3)&heq&Ig).
          symmetry in heq;inversion heq;clear heq;subst;simpl.
          replace (cons (a,b)) with (app[(a,b)]) by reflexivity.
          rewrite act_prod.
          rewrite <- (action_compose g1).
          etransitivity;[apply ax_eq_inf;symmetry;apply mon_assoc|].
          etransitivity;[apply ax_eq_inf;symmetry;apply mon_assoc|].
          etransitivity;[apply proper_prod_inf;[reflexivity|apply ax_eq_inf,mon_assoc]|].
          rewrite action_compose;simpl.
          transitivity  ([(a, b); (b, c)] ∙ 𝔉 a b1 (𝔉 b b2 e1) ·  TriSplitAct c a n1 b n2 e2).
          -- apply proper_prod_inf;[reflexivity|].
             rewrite IHe2.
             apply Σ_bigger,in_map_iff.
             exists (g1,g2,g3);tauto.
          -- apply Σ_bigger,in_map_iff.
             exists ((b1,n1),(b2,n2));tauto.
    - simpl;rewrite T;reflexivity.
    - simpl.
      repeat rewrite map_app.
      etransitivity;[|apply algebra.Σ_app].
      apply proper_join.
      + rewrite IHe.
        etransitivity;[apply proper_prod;[apply Σ_distr_l|reflexivity]|].
        etransitivity;[apply Σ_distr_r|].
        repeat rewrite map_map.
        apply Σ_map_equiv.
        intros ((f1,f2),f3) _;simpl.
        etransitivity;[symmetry;apply mon_assoc|].
        rewrite act_prod.
        etransitivity;[|apply mon_assoc].
        etransitivity;[|apply mon_assoc].
        apply proper_prod;[reflexivity|].
        etransitivity;[symmetry;apply mon_assoc|].
        symmetry;apply mon_assoc.
      + unfold splitAct.
        etransitivity;[apply proper_prod;[apply Σ_distr_l|reflexivity]|].
        etransitivity;[apply Σ_distr_r|].
        repeat rewrite map_map.
        clear IHe;apply ax_inf_PartialOrder;unfold Basics.flip;split;
          apply Σ_bounded;intros g Ig.
        * apply in_map_iff in Ig as ((g1&g2)&<-&Ig).
          unfold LowerExpr at 1;simpl.
          rewrite Σ_act.
          unfold act at 2,act_lists.
          etransitivity;[apply proper_prod_inf;[apply proper_prod_inf;
                                                [apply proper_prod_inf;
                                                 [apply ax_eq_inf,Σ_distr_l|]|]|];reflexivity|].
          etransitivity;[apply proper_prod_inf;[apply proper_prod_inf;
                                                [apply ax_eq_inf,Σ_distr_r|]|];reflexivity|].
          etransitivity;[apply proper_prod_inf; [apply ax_eq_inf,Σ_distr_r|];reflexivity|].
          etransitivity;[apply ax_eq_inf,Σ_distr_r|].
          repeat rewrite map_map.
          apply Σ_bounded;intros f If.
          apply in_map_iff in If as (α&<-&Iα).
          etransitivity.
          -- apply ax_eq_inf.
             apply proper_prod;[|reflexivity].
             apply proper_prod;[|reflexivity].
             apply proper_prod;[|reflexivity].
             apply proper_prod;[reflexivity|].
             etransitivity.
             ++ apply KA_act.
                apply filter_binding_KA.
                ** apply is_binding_finite_splitActStrict,Sq.
                ** apply splitActStrict_splitStrict_list.
             ++ rewrite filter_binding_act,Σ_act.
                rewrite filter_binding_Σ.
                unfold act at 2,act_lists.
                repeat rewrite map_map.
                reflexivity.
          -- etransitivity;[apply proper_prod_inf;[apply proper_prod_inf;
                                                   [apply proper_prod_inf;
                                                    [apply ax_eq_inf,Σ_distr_l|]|]|];reflexivity|].
             etransitivity;[apply proper_prod_inf;[apply proper_prod_inf;
                                                   [apply ax_eq_inf,Σ_distr_r|]|];reflexivity|].
             etransitivity;[apply proper_prod_inf; [apply ax_eq_inf,Σ_distr_r|];reflexivity|].
             etransitivity;[apply ax_eq_inf,Σ_distr_r|].
             repeat rewrite map_map.
             apply Σ_bounded;intros f If.
             apply in_map_iff in If as ((f1&f2)&<-&If).
             simpl.
             rewrite <- filter_binding_act.
             Transparent filter_binding.
             simpl.
             Opaque filter_binding.
             rewrite Σ_act.
             etransitivity;[apply proper_prod_inf;[apply proper_prod_inf;
                                                   [apply proper_prod_inf;
                                                    [apply ax_eq_inf,Σ_distr_l|]|]|];reflexivity|].
             etransitivity;[apply proper_prod_inf;[apply proper_prod_inf;
                                                   [apply ax_eq_inf,Σ_distr_r|]|];reflexivity|].
             etransitivity;[apply proper_prod_inf; [apply ax_eq_inf,Σ_distr_r|];reflexivity|].
             etransitivity;[apply ax_eq_inf,Σ_distr_r|].
             unfold act at 4,act_lists.
             repeat rewrite map_map.
             apply Σ_bounded;intros h Ih.
             apply in_map_iff in Ih as ((α1&α2)&<-&Iα').
             simpl.
             non_zero (𝔉 b α1 ([(a, c)] ∙ f1));[|non_zero f2].
             ++ replace actReg with act by reflexivity.
                rewrite test0_act.
                repeat rewrite orb_true_iff;tauto.
             ++ replace actReg with act by reflexivity.
                rewrite (test0_act [(b,c)] (filter_binding _ _ f2)),
                (filter_binding_test0 T0),orb_true_r.
                reflexivity.
             ++ apply factors_prod in Iα'.
                cut (size α1 <= 2*sizeExpr e).
                ** intros Sz.
                   transitivity (([(a,b);(b,c)]∙(BiLowerExpr a N true b M false e ⋆ · 𝔉 b α1 f1))
                                   · ([(b,c)]∙(𝔉 b α2 f2 · LowerExpr b M false e ⋆ · g1))
                                   · (g2 · e ⋆)).
                   --- apply ax_eq_inf.
                       rewrite <- (act_p_pinv [(a,c)] b) at 5.
                       rewrite <- filter_binding_act.
                       unfold act at 4;simpl;simpl_eqX.
                       repeat rewrite act_prod;repeat rewrite action_compose;simpl.
                       etransitivity;[symmetry;repeat apply mon_assoc||apply proper_prod||reflexivity|].
                       etransitivity;[symmetry;repeat apply mon_assoc||apply proper_prod||reflexivity|].
                       etransitivity;[symmetry;repeat apply mon_assoc||apply proper_prod||reflexivity|].
                       etransitivity;[symmetry;repeat apply mon_assoc||apply proper_prod||reflexivity|].
                       etransitivity;[symmetry;repeat apply mon_assoc||apply proper_prod||reflexivity|].
                       etransitivity;[|repeat apply mon_assoc||apply proper_prod||reflexivity].
                       etransitivity;[|repeat apply mon_assoc||apply proper_prod||reflexivity].
                       etransitivity;[|repeat apply mon_assoc||apply proper_prod||reflexivity].
                       etransitivity;[|repeat apply mon_assoc||apply proper_prod||reflexivity].
                       apply proper_prod;[reflexivity|].
                       apply proper_prod;[|reflexivity].
                       erewrite equiv_perm_act;[reflexivity| |reflexivity].
                       intro d;unfold act;simpl.
                       destruct_eqX d a;simpl_eqX;[reflexivity|].
                       destruct_eqX d b;simpl_eqX;[reflexivity|].
                       destruct_eqX d c;simpl_eqX;reflexivity.
                   --- apply Σ_bigger,in_map_iff.
                       exists ((f1,f2),(g1,g2),(α1,α2)).
                       split;[reflexivity|].
                       repeat rewrite pairs_spec;repeat split.
                       +++ assumption.
                       +++ assumption.
                       +++ unfold FunkyRange.
                           apply in_flat_map;exists α.
                           split;[assumption|].
                           apply factors_In;simpl in *;tauto.
                ** destruct (test0_false T) as (u1'&Iu1);destruct (test0_false T0) as (u2&Iu2).
                   destruct Sq as (Be&Sq).
                   apply filter_binding_lang in Iu1 as (Iu1&Eu1).
                   --- apply act_lang in Iu1.
                       rewrite <- (act_p_pinv [(a,c)] u1') in Eu1.
                       generalize dependent ([(a,c)]∗∙u1').
                       intros u1 Iu1 Eu1.
                       rewrite 𝗙_perm in Eu1.
                       unfold act in Eu1;simpl in Eu1;revert Eu1;simpl_eqX;intros <-.
                       pose proof (splitStrict_list_lang Be If Iu1 Iu2) as Iu.
                       transitivity (weight u1).
                       +++ transitivity (sum (fun a => size (𝗙 a u1)) [b]).
                           *** simpl;lia.
                           *** rewrite (weight_incr_sup [b]).
                               apply sum_incl_ND.
                               ---- intro x;simpl_In;simpl;tauto.
                               ---- apply NoDup_cons,NoDup_nil;simpl;tauto.
                       +++ rewrite is_binding_finite_memory_bound in Be.
                           apply (Be u1 u2 Iu).
                   --- clear H.
                       rewrite is_binding_finite_act.
                       apply is_binding_finite_splitStrict_list in If;tauto.
        * apply in_map_iff in Ig as ((((f1,f2)&(g1,g2))&(α1&α2))&<-&Ig);simpl.
          repeat rewrite pairs_spec in Ig;destruct Ig as ((If&Ig)&Iα).
          unfold FunkyRange in Iα;apply in_flat_map in Iα as (α&Iα&Eα).
          apply factors_prod in Eα.
          transitivity ((((([(a, b); (b, c)] ∙ (BiLowerExpr a N true b M false e ⋆))
                             · [(b, c)] ∙ LowerExpr b M false (splitActStrict c a N e))
                            · [(b, c)] ∙ (LowerExpr b M false e ⋆)) · ([(b, c)] ∙ g1 · g2))·e ⋆);
            [|apply Σ_bigger,in_map_iff;exists (g1,g2);tauto].
          repeat rewrite act_prod.
          etransitivity;[apply ax_eq_inf;
                         repeat apply mon_assoc||apply proper_prod||reflexivity|].
          etransitivity;[apply ax_eq_inf;
                         repeat apply mon_assoc||apply proper_prod||reflexivity|].
          etransitivity;[apply ax_eq_inf;
                         repeat apply mon_assoc||apply proper_prod||reflexivity|].
          etransitivity;[apply ax_eq_inf;
                         repeat apply mon_assoc||apply proper_prod||reflexivity|].
          etransitivity;[|apply ax_eq_inf;symmetry;
                          repeat apply mon_assoc||apply proper_prod||reflexivity].
          apply proper_prod_inf;[|reflexivity].
          apply proper_prod_inf;[|reflexivity].
          apply proper_prod_inf;[|reflexivity].
          apply proper_prod_inf;[|reflexivity].
          etransitivity;[apply ax_eq_inf;symmetry;
                         repeat apply mon_assoc||apply proper_prod||reflexivity|].
          apply proper_prod_inf;[reflexivity|].
          transitivity ([(b, c)] ∙ (𝔉 b α ([(a,c)]∙f1 · f2))).
          -- transitivity ([(b, c)] ∙ (𝔉 b α1 ([(a,c)]∙f1) · 𝔉 b α2 f2)).
             ++ rewrite <- (act_p_pinv [(a,c)] b) at 7.
                rewrite <-filter_binding_act.
                unfold act at 5;simpl;simpl_eqX.
                rewrite act_prod,action_compose;simpl.
                apply proper_prod_inf;[|reflexivity].
                erewrite equiv_perm_act;[reflexivity| |reflexivity].
                intro d;unfold act;simpl.
                destruct_eqX d a;simpl_eqX;[reflexivity|].
                destruct_eqX d b;simpl_eqX;[reflexivity|].
                destruct_eqX d c;simpl_eqX;reflexivity.                
             ++ cut (𝔉 b α1 ([(a, c)] ∙ f1) · 𝔉 b α2 f2 <=KA  𝔉 b α ([(a, c)] ∙ f1 · f2));
                  [intros E;apply (KA_act [(b,c)]) in E;apply E|].
                Transparent filter_binding.
                simpl.
                Opaque filter_binding.
                non_zero (𝔉 b α1 ([(a, c)] ∙ f1)).
                apply Σ_bigger,in_map_iff.
                exists (α1,α2);simpl;split;[reflexivity|].
                apply factors_In;[|assumption].
                rewrite sizeExpr_act.
                rewrite <- (act_p_pinv [(a,c)] b),<-filter_binding_act,test0_act in T.
                unfold act in T;simpl in T;simpl_eqX.
                apply test0_false in T as (u&Iu).
                apply filter_binding_lang in Iu as (Iu&<-).
                ** apply binding_finite_bound_size;[|assumption].
                   apply is_binding_finite_splitStrict_list in If;[tauto|apply Sq].
                ** apply is_binding_finite_splitStrict_list in If;[tauto|apply Sq].
          -- cut (𝔉 b α ([(a, c)] ∙ f1 · f2) <=KA LowerExpr b M false (splitActStrict c a N e));
               [intros E;apply (KA_act [(b,c)]) in E;apply E|].
             transitivity (𝔉 b α (splitActStrict c a N e)).
             ++ cut ([(a, c)] ∙ f1 · f2 <=KA splitActStrict c a N e).
                ** intros E;unfold ax_inf in E;symmetry in E.
                   eapply filter_binding_KA in E as ->.
                   --- Transparent filter_binding.
                       simpl;apply inf_cup_left.
                       Opaque filter_binding.
                   --- apply is_binding_finite_splitActStrict,Sq.
                ** rewrite splitActStrict_splitStrict_list.
                   apply Σ_bigger,in_map_iff.
                   exists (f1,f2);tauto.
             ++ apply Σ_bigger,in_map_iff.
                exists α;tauto.
  Qed.

  Lemma TriSplit_list_facts a N b M e f1 f2 f3 :
    is_binding_finite e -> 
    (f1,f2,f3) ∈ (TriSplit_list a N b M e) ->
    is_binding_finite f1
    /\ is_binding_finite f2
    /\ is_binding_finite f3
    /\ ⟦f1·f2·f3⟧≲⟦e⟧
    /\ (forall u, ⟦f1⟧ u -> 𝗙 a u = S N▶
                     /\ (forall v w : list letter, u = v ++ w -> ⎢ v ⎥ < ⎢ u ⎥ -> 𝗙 a v <> S N▶))
    /\ (forall u, ⟦f1·f2⟧ u -> 𝗙 b u = M▶)
    /\ ⌊f1·f2·f3⌋ ⊆ ⌊e⌋.
  Proof.
    intros Be;repeat rewrite <- binding_finite_spec.
    revert N M f1 f2 f3;induction_bin_fin e Be;intros N M f1 f2 f3;simpl.
    - tauto.
    - tauto.
    - unfold_eqX;simpl;try tauto.
      intros [heq|FF];[|tauto].
      symmetry in heq;inversion heq;clear heq;subst.
      split;[|split;[|split;[|split;[|split;[|split]]]]].
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + intros u (?&?&->&(?&?&->&->&->)&->).
        reflexivity.
      + intros u Iu.
        replace u with [x] by apply Iu;simpl_binding.
        split;[assumption|].
        intros [] ? EE;[|simpl;lia].
        intros _;discriminate.
      + intros u (?&?&->&->&->);simpl_binding;assumption.
      + repeat rewrite support_prod.
        repeat apply incl_app;apply incl_nil||reflexivity.
    - rewrite support_join.
      simpl_In;intros [I|I];[apply IHe1 in I|apply IHe2 in I];
        (split;[|split;[|split;[|split;[|split;[|split]]]]]);try tauto.
      + intros u Iu;left;apply I,Iu.
      + apply incl_appl;tauto.
      + intros u Iu;right;apply I,Iu.
      + apply incl_appr;tauto.
    - rewrite T;simpl.
      simpl_In.
      intros [I|[I|I]].
      + apply in_map_iff in I as (((g1,g2)&g3)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        apply IHe1 in Ig as (Bg1&Bg2&Bg3&L1&L2&L3&hS).
        split;[|split;[|split;[|split;[|split;[|split]]]]];try tauto.
        * simpl;rewrite Bg3;apply binding_finite_spec in B2 as ->.
          apply orb_true_r.
        * intros ? (?&?&->&(u1&u2&->&Iu1&Iu2)&(u3&u4&->&I3&I4)).
          exists (u1++u2++u3),u4.
          repeat rewrite app_ass;repeat split.
          -- apply L1;exists (u1++u2),u3;split;[rewrite app_ass;reflexivity|].
             split;[exists u1,u2|];tauto.
          -- assumption.
        * repeat rewrite support_prod.
          rewrite <- hS.
          repeat rewrite support_prod.
          repeat rewrite app_ass;reflexivity.
      + clear IHe1 IHe2.
        apply in_flat_map in I as ((α1,α2)&Iα&I).
        apply in_map_iff in I as (((g1,g2)&(h1,h2))&heq&I).
        symmetry in heq;inversion heq;clear heq;subst.
        apply pairs_spec in I as (Ig&Ih).
        pose proof (is_binding_finite_splitStrict_list (is_binding_finite_filter_binding b α1 B1) Ig)
          as (Bg1&Bg2).
        pose proof (split_binding_is_binding_finite B2 Ih)
          as (Bh1&Bh2).
        split;[|split;[|split;[|split;[|split;[|split]]]]].
        * apply binding_finite_spec;assumption.
        * simpl;rewrite orb_true_iff,andb_true_iff.
          right;split;apply binding_finite_spec;assumption.
        * apply binding_finite_spec;assumption.
        * intros ? (?&u4&->&(u1&?&->&Iu1&u2&u3&->&Iu2&Iu3)&Iu4).
          exists (u1++u2),(u3++u4).
          repeat rewrite app_ass;split;[reflexivity|].
          split.
          -- eapply ax_inf_lang_incl;[apply filter_binding_inf,B1|].
             eapply splitStrict_list_lang;try eassumption.
             apply is_binding_finite_filter_binding,B1.
          -- destruct (split_binding_lang B2 Ih Iu3 Iu4) as (Iu&_);tauto.
        * intros u Iu.
          eapply splitStrict_list_binding;[|eassumption|eassumption].
          apply is_binding_finite_filter_binding,B1.
        * intros u (u1&?&->&Iu1&u2&u3&->&Iu2&Iu3).
          rewrite <- app_ass,𝗙_app.
          eapply split_binding_bindings in Iu3 as ->;[| |eassumption];[|assumption].
          cut (⟦𝔉 b α1 e1⟧ (u1++u2)).
          -- intro Iu;apply filter_binding_lang in Iu as (_&->);[|assumption].
             eapply factors_prod,Iα.
          -- eapply splitStrict_list_lang;try eassumption.
             apply is_binding_finite_filter_binding,B1.
        * repeat rewrite support_prod.
          apply splitStrict_list_support in Ig;[|apply is_binding_finite_filter_binding,B1].
          rewrite filter_binding_support in Ig;rewrite <- Ig.
          apply split_binding_support in Ih as <-;repeat rewrite support_prod.
          repeat rewrite app_ass;reflexivity.
      + apply in_flat_map in I as (((α1,n1),(α2&n2))&Iα&I).
        unfold TriRange in Iα.
        apply pairs_spec in Iα as (Iα1&Iα2).
        apply in_flat_map in Iα2 as ((?&((?&[])&[]))&E2&I');try (simpl in *;tauto).
        destruct I' as [I'|FF];[|simpl in FF;tauto].
        inversion I';clear I';subst.
        apply SplitRange_result in Iα1 as (E1&Min).
        apply factors_prod in E2.
        apply in_map_iff in I as (((g1&g2)&g3)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        apply IHe2 in Ig as (Bg1&Bg2&Bg3&L1&L2&L3&hS).
        split;[|split;[|split;[|split;[|split;[|split]]]]].
        * simpl;rewrite Bg1,andb_true_r,orb_true_iff.
          right;apply binding_finite_spec.
          apply is_binding_finite_filter_binding,is_binding_finite_filter_binding,B1.
        * assumption.
        * assumption.
        * intros ? (?&u4&->&(?&u3&->&(u1&u2&->&Iu1&Iu2)&Iu3)&Iu4).
          exists u1,(u2++u3++u4);repeat rewrite app_ass.
          repeat split.
          -- apply filter_binding_lang in Iu1 as (Iu1&_);[|apply is_binding_finite_filter_binding,B1].
             apply filter_binding_lang in Iu1 as (Iu1&_);tauto.
          -- eapply L1;exists (u2++u3),u4;rewrite app_ass;repeat split;[exists u2,u3|];tauto.
        * intros ? (u1&u2&->&Iu1&Iu2).
          simpl_binding.
          apply filter_binding_lang in Iu1 as (Iu1&Eu1);[|apply is_binding_finite_filter_binding,B1].
          apply L2 in Iu2 as (Eu2&Min').
          split;[rewrite Eu1,Eu2;assumption|].
          clear IHe1 IHe2 B1 B2 T Bg1 Bg2 Bg3 L1 L2 L3 hS Iu1.
          intros v1 v2 EE Len Ev1.
          apply Levi in EE as (w&[(->&->)|(->&->)]).
          -- simpl_binding in Eu1.
             apply (Min (𝗙 a w)).
             rewrite <- Eu1,Ev1;reflexivity.
          -- apply (Min' w v2);[reflexivity|solve_length|].
             clear Len.
             simpl_binding in Eu2.
             simpl_binding in Ev1.
             rewrite Eu1 in *;clear u1 Eu1 E2 α2 n2 M Min' Min.
             apply destr_bind_prod_full in Eu2 as (Ev2&h1).
             revert Ev2 h1;set (K:= d_binding(𝗙 a v2));intros.
             apply destr_bind_prod_full in Ev1 as (Ew&h2).
             revert Ew h2;set (N':= d_binding(𝗙 a w));intros.
             rewrite Ew in *.
             apply destr_bind_prod_full in E1 as (_&h3).
             destruct α1 as ((D,F),C).
             unfold d_binding in *;simpl in *.
             simpl_nat.
             destruct_eqX N' (S n1);[reflexivity|].
             destruct h1 as [(h1&h1')|h1];[|inversion h1;reflexivity].
             destruct h2 as [(h2&h2')|h2];[|inversion h2];
               (destruct h3 as [(h3&h3')|h3];[|inversion h3]);lia.
        * intros ? (?&u3&->&(u1&u2&->&Iu1&Iu2)&Iu3).
          rewrite app_ass,𝗙_app.
          cut (⟦g1·g2⟧(u2++u3));[|exists u2,u3;tauto].
          intros Iu;apply L3 in Iu as ->.
           apply filter_binding_lang in Iu1 as (Iu1&_);[|apply is_binding_finite_filter_binding,B1].
           apply filter_binding_lang in Iu1 as (_&->);tauto.
        * repeat rewrite support_prod.
          repeat rewrite filter_binding_support.
          rewrite <- hS.
          repeat rewrite support_prod.
          repeat rewrite app_ass;reflexivity. 
    - rewrite T;simpl;tauto.
    - simpl_In.
      intros [I|I].
      + apply in_map_iff in I as (((g1,g2)&g3)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        apply IHe in Ig as (Bg1&Bg2&Bg3&L1&L2&L3&hS).
        split;[|split;[|split;[|split;[|split;[|split]]]]].
        * apply sqExpr_star in Sq as (Bs&_).
          apply (BiLowerExpr_star_is_binding_finite a N true b M false),
          binding_finite_spec in Bs.
          simpl in *;rewrite Bs,Bg1;apply orb_true_r.
        * assumption.
        * apply sqExpr_star in Sq as (Bs&_).
          apply binding_finite_spec in Bs.
          simpl in *;rewrite Bs,Bg3;apply orb_true_r.
        * intros ? (?&?&->&(?&u3&->&(u1&u2&->&Iu1&Iu2)&Iu3)&u4&u5&->&Iu4&Iu5).
          apply sqExpr_star in Sq as (Bs&_).
          pose proof (ka_star_mid_split ⟦e⟧) as h;apply h;clear h.
          exists (u1++u2++u3++u4),u5;repeat rewrite app_ass.
          repeat split;[|assumption].
          exists u1,(u2++u3++u4);repeat rewrite app_ass.
          repeat split.
          -- apply BiLowerExpr_star_lang in Iu1 as (Iu1&_);tauto.
          -- eapply L1;exists (u2++u3),u4;rewrite app_ass;repeat split;[exists u2,u3|];tauto.
        * intros ? (u1&u2&->&Iu1&Iu2).
          simpl_binding.
          apply sqExpr_star in Sq as (Bs&_).
          apply BiLowerExpr_star_lang in Iu1 as (_&Iu1&_);[|assumption].
          apply L2 in Iu2 as (Eu2&Min).
          split;[rewrite Eu2;apply lower_squares_prod_destr_true;tauto|].
          intros v1 v2 EE Len Ev1.
          clear IHe Bs Bg1 Bg2 Bg3 L1 L2 L3 hS.
          apply Levi in EE as (w&[(->&->)|(->&->)]).
          -- apply lower_squares_alt in Iu1 as (E2&E3);[|reflexivity].
             revert E2 E3;unfold square;simpl_binding.
             rewrite Ev1;simpl;simpl_nat.
             intros -> [h|(h&_)];lia.
          -- apply (Min w v2);[reflexivity|solve_length|].
             apply lower_squares_alt in Iu1 as (E2&E3);[|reflexivity].
             clear Min Len.
             simpl_binding in Eu2.
             simpl_binding in Ev1.
             apply destr_bind_prod_full in Eu2 as (Ev2&h1).
             revert Ev2 h1;set (K:= d_binding(𝗙 a v2));intros.
             apply destr_bind_prod_full in Ev1 as (Ew&h2).
             revert Ew h2;set (N':= d_binding(𝗙 a w));intros.
             rewrite Ew in *.
             destruct (𝗙 a u1) as ((D,F),C).
             unfold square,d_binding in *;simpl in *.
             subst;clear Ev2 Ew.
             f_equal;f_equal.
             assert (L: D<=N) by lia;clear E3.
             destruct h1 as [(h1&h1')|h1];[|inversion h1;reflexivity].
             destruct h2 as [(h2&h2')|h2];[|inversion h2];lia.
        * intros ? (?&u3&->&(u1&u2&->&Iu1&Iu2)&Iu3).
          rewrite app_ass,𝗙_app.
          cut (⟦g1·g2⟧(u2++u3));[|exists u2,u3;tauto].
          intros Iu;apply L3 in Iu as ->.
          apply sqExpr_star in Sq as (Bs&_).
          apply BiLowerExpr_star_lang in Iu1 as (_&Iu1);[|assumption].
          apply lower_squares_prod_destr_false;tauto.
        * transitivity ⌊e·e·e⌋;[|repeat rewrite support_prod;repeat apply incl_app;reflexivity].
          repeat rewrite support_prod||rewrite support_star.
          rewrite <- hS at 3.
          repeat rewrite support_prod.
          repeat rewrite <- app_ass.
          repeat apply incl_app_Proper;try reflexivity.
          clear.
          unfold BiLowerExpr.
          rewrite <- Σ_support.
          repeat apply incl_app;try reflexivity.
          intros c Ic;apply In_support_list in Ic as (f&If&Ic).
          apply in_map_iff in If as (?&<-&_).
          repeat apply filter_binding_support in Ic;assumption.
      + clear IHe.
        pose proof Sq as Bs;apply sqExpr_star in Bs as (Bs &_).
        pose proof Sq as Be;destruct Be as (Be &_).
        apply in_map_iff in I as ((((g1,g2)&(h1,h2))&(α1,α2))&heq&I).
        symmetry in heq;inversion heq;clear heq;subst.
        apply pairs_spec in I as (I&Iα).
        apply pairs_spec in I as (Ig&Ih).
        unfold FunkyRange in Iα;apply in_flat_map in Iα as (α&Iα&Eα).
        apply factors_prod in Eα.
        pose proof (is_binding_finite_splitStrict_list Be Ig)
          as (Bg1&Bg2).
        pose proof (split_binding_is_binding_finite Be Ih)
          as (Bh1&Bh2).
        split;[|split;[|split;[|split;[|split;[|split]]]]].
        * apply (BiLowerExpr_star_is_binding_finite a N true b M false),binding_finite_spec in Bs.
          eapply is_binding_finite_filter_binding,binding_finite_spec in Bg1;simpl in *;
            rewrite Bg1,Bs;apply orb_true_r.
        * apply (LowerExpr_star_is_binding_finite b M false),binding_finite_spec in Bs.
          eapply is_binding_finite_filter_binding,binding_finite_spec in Bg2.
          eapply binding_finite_spec in Bh1.
          simpl in *;rewrite Bg2,Bh1,Bs;repeat rewrite orb_true_r;tauto.
        * eapply binding_finite_spec in Bh2.
          eapply binding_finite_spec in Bs.
          simpl in *;rewrite Bs,Bh2;apply orb_true_r.
        * intros ? (?&?&->&(?&?&->&(u1&u2&->&Iu1&Iu2)&?&u5&->&(u3&u4&->&Iu3&Iu4)&Iu5)
                    &u6&u7&->&Iu6&Iu7).
          pose proof (ka_star_mid_split ⟦e⟧) as h;apply h.
          exists (u1++u2++u3++u4++u5++u6),u7.
          repeat rewrite app_ass;split;[reflexivity|].
          split;[|assumption].
          exists (u1++u2++u3++u4),(u5++u6).
          repeat rewrite app_ass;split;[reflexivity|].
          split.
          -- apply h;clear h.
             exists (u1++u2++u3),u4.
             repeat rewrite app_ass;split;[reflexivity|].
             split.
             ++ exists u1,(u2++u3).
                repeat rewrite app_ass;split;[reflexivity|].
                split.
                ** apply BiLowerExpr_star_lang in Iu1;tauto.
                ** apply filter_binding_lang in Iu2 as (Iu2&_);[|assumption].
                   apply filter_binding_lang in Iu3 as (Iu3&_);[|assumption].
                   eapply splitStrict_list_lang;eassumption.
             ++ apply LowerExpr_star_lang in Iu4;tauto.
          -- destruct (split_binding_lang Be Ih Iu5 Iu6) as (Iu&_);tauto.
        * intros u (u1&u2&->&Iu1&Iu2).
          simpl_binding.
          apply BiLowerExpr_star_lang in Iu1 as (_&Iu1&_);[|assumption].
          apply filter_binding_lang in Iu2 as (Iu2&_);[|assumption].
          eapply splitStrict_list_binding in Iu2 as (Eu2&Min);[| |eassumption];[|assumption].
          split;[rewrite Eu2;apply lower_squares_prod_destr_true,Iu1|].
          clear Ig Ih Bs Be Bg1 Bg2 Bh1 Bh2 α α1 α2 Iα Eα M g1 g2 h1 h2 Sq e.
          intros v1 v2 EE Len Ev1.
          apply Levi in EE as (w&[(->&->)|(->&->)]).
          -- apply lower_squares_alt in Iu1 as (E2&E3);[|reflexivity].
             revert E2 E3;unfold square;simpl_binding.
             rewrite Ev1;simpl;simpl_nat.
             intros -> [h|(h&_)];lia.
          -- apply (Min w v2);[reflexivity|solve_length|].
             apply lower_squares_alt in Iu1 as (E2&E3);[|reflexivity].
             clear Min Len.
             simpl_binding in Eu2.
             simpl_binding in Ev1.
             apply destr_bind_prod_full in Eu2 as (Ev2&h1).
             revert Ev2 h1;set (K:= d_binding(𝗙 a v2));intros.
             apply destr_bind_prod_full in Ev1 as (Ew&h2).
             revert Ew h2;set (N':= d_binding(𝗙 a w));intros.
             rewrite Ew in *.
             destruct (𝗙 a u1) as ((D,F),C).
             unfold square,d_binding in *;simpl in *.
             subst;clear Ev2 Ew.
             f_equal;f_equal.
             assert (L: D<=N) by lia;clear E3.
             destruct h1 as [(h1&h1')|h1];[|inversion h1;reflexivity].
             destruct h2 as [(h2&h2')|h2];[|inversion h2];lia.
        * intros ? (?&?&->&(u1&u2&->&Iu1&Iu2)&?&u5&->&(u3&u4&->&Iu3&Iu4)&Iu5).
          simpl_binding.
          apply filter_binding_lang in Iu2 as (_&->);[|assumption].
          apply filter_binding_lang in Iu3 as (_&->);[|assumption].
          apply BiLowerExpr_star_lang in Iu1 as (_&_&Iu1);[|assumption].
          eapply split_binding_bindings in Iu5 as ->;[| |eassumption];[|assumption].
          apply LowerExpr_star_lang in Iu4 as (_&Iu4);[|assumption].
          repeat rewrite <- prod_assoc.
          rewrite lower_squares_prod_destr_false;[|assumption].
          rewrite (prod_assoc α1),Eα.
          rewrite lower_squares_prod_destr_false;[|assumption].
          rewrite lower_squares_prod_destr_false;[|assumption].
          reflexivity.
        * transitivity ⌊e·e·e·e·e⌋;[|repeat rewrite support_prod;repeat apply incl_app;reflexivity].
          repeat rewrite support_prod||rewrite support_star.
          apply splitStrict_list_support in Ig;[|assumption].
          rewrite <- Ig at 3.
          apply split_binding_support in Ih.
          rewrite <- Ih at 4.
          repeat rewrite support_prod.
          repeat rewrite <- app_ass.
          repeat rewrite filter_binding_support.
          repeat apply incl_app_Proper;try reflexivity;clear.
          -- unfold BiLowerExpr.
             rewrite <- Σ_support.
             repeat apply incl_app;try reflexivity.
             intros c Ic;apply In_support_list in Ic as (f&If&Ic).
             apply in_map_iff in If as (?&<-&_).
             repeat apply filter_binding_support in Ic;assumption.
          -- unfold LowerExpr.
             repeat rewrite support_star.
             rewrite <- Σ_support.
             repeat apply incl_app;try reflexivity.
             intros c Ic;apply In_support_list in Ic as (f&If&Ic).
             apply in_map_iff in If as (?&<-&_).
             apply filter_binding_support in Ic;assumption.
  Qed.

  
  Lemma TriSplitAct_fresh c a N b e :
    is_binding_finite e -> a<>b -> a<>c -> b<>c -> c # e -> freshExpr b e ->
    TriSplitAct c a N b 0 e =α splitActStrict b a N ([(b,c)]∙e).
  Proof.
    intros Be N1 N2 N3 Fc F.
    apply ax_inf_PartialOrder;unfold Basics.flip;split.
    - etransitivity;[apply ax_eq_inf,KA_αKA,TriSplitAct_TriSplit_list;tauto|].
      apply Σ_bounded;intros g Ig.
      apply in_map_iff in Ig as (((f1,f2),f3)&<-&If).
      simpl.
      transitivity (([(a, b); (b, c)] ∙ f1 · [(b, c)] ∙ f2) · [(b,c)]∙ f3).
      + non_zero f1.
        non_zero f2.
        apply ax_eq_inf;repeat apply proper_prod;try reflexivity.
        apply ax_eq_ax,αKA_αα.
        intros u3 Iu3.
        apply test0_false in T as (u1&Iu1).
        apply test0_false in T0 as (u2&Iu2).
        eapply TriSplit_list_facts in If as (_&_&_&hLang&_&hb&hS);[|assumption].
        split.
        * cut (⟦e⟧ (u1++u2++u3) /\ ⟦f1·f2⟧ (u1++u2)).
          -- intros (h1&h2).
             apply hb in h2.
             apply (is_binding_finite_bindings Be b),F in h1 as [h1|FF];[|simpl in FF;tauto].
             rewrite <- app_ass,𝗙_app,h2,prod_unit_l in h1.
             symmetry in h1;apply h1.
          -- split;[|exists u1,u2;tauto].
             apply hLang;exists (u1++u2),u3.
             rewrite app_ass;split;[reflexivity|split;[|assumption]].
             exists u1,u2;tauto.
        * apply αfresh_support.
          apply support_lang in Iu3 as ->.
          rewrite support_prod in hS;rewrite <- hS in Fc.
          simpl_In in Fc;tauto.
      + apply KA_αKA_inf,CompletenessKA_inf.
        intros u (?&u3&->&(u1&u2&->&Iu1&Iu2)&Iu3).
        rewrite act_lang in Iu1,Iu2,Iu3.
        apply splitActStrict_lang;[apply is_binding_finite_act,Be|].
        exists ([(a,b)]∗∙u1),(u2++u3).
        rewrite act_p_pinv;repeat rewrite app_ass;split;[reflexivity|].
        apply TriSplit_list_facts in If as (_&_&_&hLang&Ha&Hb&Sup);[|assumption].
        repeat split.
        * rewrite act_lang.
          repeat rewrite act_lists_app.
          rewrite action_compose,<-inverse_app.
          apply hLang;eexists;eexists;split;[|split;[eexists;eexists;split;[|split;eassumption];
                                                     reflexivity
                                                    |eassumption]].
          repeat rewrite app_ass;simpl;reflexivity.
        * apply Ha in Iu1;revert Iu1.
          repeat rewrite 𝗙_perm;unfold act;simpl;simpl_eqX.
          tauto.
        * apply Ha in Iu1 as (_&Iu1);intros v1 v2 EE Len Ev1.
          apply (Iu1 ([(b,c)]∗∙v1) ([(b,c)]∗∙v2)).
          -- replace (cons (a,b)) with (app[(a,b)]) by reflexivity.
             rewrite inverse_app,<-action_compose,EE.
             apply act_lists_app.
          -- solve_length.
          -- rewrite <- Ev1,𝗙_perm;unfold act;simpl;simpl_eqX;reflexivity.
    - apply KA_αKA_inf,CompletenessKA_inf.
      intros u Iu.
      apply TriSplitAct_lang;try tauto.
      apply splitActStrict_lang in Iu;[|apply is_binding_finite_act,Be].
      destruct Iu as (u1&u2&->&Iu&E1&Min).
      rewrite act_lang,act_lists_app in Iu.
      exists ([(b,c)]∗∙u1),([(b,c)]∗∙u2),[];repeat split.
      + replace (cons (a,b)) with (app[(a,b)]) by reflexivity.
        repeat rewrite <-action_compose.
        repeat rewrite act_p_pinv;rewrite act_nil,app_nil_r.
        reflexivity.
      + rewrite app_nil_r;assumption.
      + rewrite 𝗙_perm;unfold act;simpl;simpl_eqX;assumption.
      + apply (is_binding_finite_bindings Be b) in Iu.
        apply F in Iu as [<-|FF];[reflexivity|simpl in FF;tauto].
      + intros v1 v2 EE Len.
        apply (act_bij [(b,c)]) in EE.
        rewrite act_p_pinv in EE.
        rewrite act_lists_app in EE.
        apply Min in EE;[|solve_length].
        revert EE;rewrite 𝗙_perm;unfold act;simpl;simpl_eqX;tauto.
  Qed.
    
      
    
  Lemma TriSplitAct_αα c a N b M e a1 a2 :
    is_binding_finite e -> a<>b -> a<>c -> b<>c -> c # e -> c # ([(a1,a2)]∙e) ->
    (forall u, ⟦e⟧ u -> a1 #α u /\ a2 #α u) ->
    TriSplitAct c a N b M e =α TriSplitAct c a N b M ([(a1,a2)]∙e).
  Proof.
    intros Be N1 N2 N3 F1 F2 F.
    case_in a [a1;a2].
    - transitivity zero;[|symmetry];apply KA_αKA,test0_spec,not_false_is_true;intros Iu;
        apply test0_false in Iu as (u&Iu);apply TriSplitAct_lang in Iu;try assumption.
      + destruct Iu as (u1&u2&u3&->&Iu&Eu&_).
        cut (a ◁ (u1++u2++u3));unfold close_balanced.
        * simpl_binding;rewrite Eu.
          unfold d_binding at 1;simpl;lia.
        * cut (a #α (u1++u2++u3));[intros ->;reflexivity|].
          destruct I as [<-|[<-| FF]];try inversion FF.
          -- apply F in Iu;tauto.
          -- apply F in Iu;tauto.
      + destruct Iu as (u1&u2&u3&->&Iu&Eu&_).
        apply act_lang in Iu.
        rewrite <- (act_pinv_p ([(a1,a2)]∗) a),<-𝗙_perm in Eu.
        rewrite act_lists_app in Iu.
        cut ([(a1, a2)] ∗ ∙a ◁ ([(a1, a2)] ∗ ∙u1++[(a1, a2)] ∗ ∙(u2++u3)));unfold close_balanced.
        * simpl_binding;simpl in *;rewrite Eu.
          unfold d_binding at 1;simpl;lia.
        * cut ([(a1, a2)] ∗ ∙a #α ([(a1, a2)] ∗ ∙u1++[(a1, a2)] ∗ ∙(u2++u3)));[intros ->;reflexivity|].
          apply F in Iu as (Ia1&Ia2).
          clear Be Eu F.
          generalize dependent (([(a1, a2)] ∗) ∙ u1 ++ ([(a1, a2)] ∗) ∙ (u2 ++ u3)).
          clear u1 u2 u3;intros w E1 E2.
          unfold act;simpl;unfold_eqX;try assumption.
          destruct I as [<-|[<-|FF]];simpl in *;tauto.
      + apply is_binding_finite_act,Be.
    - revert F2;rewrite support_action,In_act_lists.
      unfold act at 1;simpl.
      unfold_eqX;subst;intros F2.
      + rewrite action_invariant;[reflexivity|].
        apply elements_inv_act.
        intros d;rewrite support_list_atoms.
        simpl;intros Id [<-|[<-|FF]];tauto.
      + rewrite action_invariant;[reflexivity|].
        apply elements_inv_act.
        intros d;rewrite support_list_atoms.
        simpl;intros Id [<-|[<-|FF]];tauto.
      + case_in b [a1;a2].
        * destruct M.
          -- repeat rewrite TriSplitAct_fresh;try tauto.
             ++ apply splitActStrict_αKA.
                ** repeat apply is_binding_finite_act;assumption.
                ** rewrite support_action,In_act_lists.
                   unfold act;simpl;simpl_eqX;tauto.
                ** rewrite action_compose,support_action,In_act_lists.
                   unfold act;simpl;simpl_eqX;tauto.
                ** apply αKA_act.
                   apply ax_eq_ax,αKA_αα,F.
             ++ repeat apply is_binding_finite_act;assumption.
             ++ rewrite support_action,In_act_lists.
                unfold act;simpl;simpl_eqX;tauto.
             ++ intros d.
                rewrite bindings_act.
                unfold act;simpl.
                destruct I0 as [<-|[<-|FF]];simpl_eqX.
                ** intros Id;left.
                   apply bindings_witness in Id as (u&Iu&<-).
                   apply F in Iu as (_&->);reflexivity.
                ** unfold_eqX;intros Id;left; apply bindings_witness in Id as (u&Iu&<-);
                     apply F in Iu as (->&_);reflexivity.
                ** simpl in FF;tauto.
             ++ intros d.
                destruct I0 as [<-|[<-|FF]];simpl_eqX.
                ** intros Id;left.
                   apply bindings_witness in Id as (u&Iu&<-).
                   apply F in Iu as (->&_);reflexivity.
                ** intros Id;left; apply bindings_witness in Id as (u&Iu&<-).
                   apply F in Iu as (_&->);reflexivity.
                ** simpl in FF;tauto.
          -- transitivity zero;[|symmetry];apply KA_αKA,test0_spec,not_false_is_true;intros Iu;
               apply test0_false in Iu as (u&Iu);
               apply TriSplitAct_lang in Iu as (u1&u2&u3&Eu&Iu&_&Eb&_);try tauto.
             ++ cut (d_binding (𝗙 b (u1++u2++u3)) = 0).
                ** rewrite <- app_ass,𝗙_app,Eb;simpl_binding.
                   unfold d_binding at 1;simpl;lia.
                ** apply F in Iu as (FF1&FF2).
                   destruct I0 as [<-|[<-|FF]];[| |simpl in FF;tauto].
                   --- rewrite FF1;reflexivity.
                   --- rewrite FF2;reflexivity.
             ++ cut (d_binding (𝗙 b (u1++u2++u3)) = 0).
                ** rewrite <- app_ass,𝗙_app,Eb;simpl_binding.
                   unfold d_binding at 1;simpl;lia.
                ** apply act_lang,F in Iu as (FF1&FF2).
                   destruct I0 as [<-|[<-|FF]];[| |simpl in FF;tauto].
                   --- revert FF2;unfold fresh__α.
                       rewrite 𝗙_perm;unfold act;simpl;simpl_eqX.
                       unfold_eqX;intros ->;reflexivity.
                   --- revert FF1;unfold fresh__α.
                       rewrite 𝗙_perm;unfold act;simpl;simpl_eqX.
                       intros ->;reflexivity.
             ++ apply is_binding_finite_act,Be.
        * transitivity([(a1,a2)]∙TriSplitAct c a N b M e).
          -- apply ax_eq_ax,αKA_αα.
             intros u Iu.
             apply TriSplitAct_lang in Iu as (u1&u2&u3&->&Iu&_);try tauto.
             unfold fresh__α;simpl_binding.
             repeat rewrite 𝗙_perm.
             unfold act;simpl in *;simpl_eqX.
             repeat rewrite <- 𝗙_app;apply F,Iu.
          -- rewrite TriSplitAct_act.
             unfold act;simpl in *;simpl_eqX.
             reflexivity.
  Qed.
        
                  
  Lemma TriSplitAct_αKA c a N b M e f :
    is_binding_finite f -> a<>b -> a<>c -> b<>c -> c # e -> c # f ->
    e =α f -> TriSplitAct c a N b M e =α TriSplitAct c a N b M f.
  Proof.
    intros B2 N1 N2 N3 F1 F2 eq.
    pose proof B2 as B1;apply (is_binding_finite_ax_eq eq) in B1.
    revert a b c F1 F2 N1 N2 N3 N M;induction eq;intros a b c F1 F2 N1 N2 N3 N M.
    - reflexivity.
    - symmetry;apply IHeq;tauto.
    - destruct (exists_fresh (a::b::⌊e⌋++⌊f⌋++⌊g⌋)) as (d&Id).
      assert (a<>d /\ b<>d /\ d # e /\ d # f /\ d # g) as (N4&N5&Fe&Ff&Fg) by (simpl_In in Id;tauto);
        clear Id.
      rewrite <- (act_pinv_p [(c,d)] _).
      rewrite <- (act_pinv_p [(c,d)] (TriSplitAct c a N b M e)).
      apply αKA_act.
      repeat rewrite TriSplitAct_act.
      unfold act at 1 2 3 5 6 7;simpl;simpl_eqX.
      rewrite action_invariant,action_invariant.
      + etransitivity;[apply IHeq1|apply IHeq2];try tauto.
        * apply (is_binding_finite_ax_eq eq1);tauto.
        * apply (is_binding_finite_ax_eq eq1);tauto.
      + apply map_eq_id;intros k Ik.
        apply elements_inv_act_atom;simpl;intros [<-|[<-|F]];tauto.
      + apply map_eq_id;intros k Ik.
        apply elements_inv_act_atom;simpl;intros [<-|[<-|F]];tauto.
    - assert (Te : test0 (e·e') = test0 (f·f'))
        by (apply test0_αKA;rewrite eq1,eq2;reflexivity).
      assert (c # e /\ c # e' /\ c # f /\ c # f') as (Fe&Fe'&Ff&Ff')
        by (rewrite support_prod in F1,F2;simpl_In in *;tauto);clear F1 F2.
      simpl in *;case_eq (test0 f||test0 f');[intros E;rewrite E in Te;rewrite Te;reflexivity|].
      intros Tf;rewrite Tf in Te;rewrite Te.
      apply orb_false_iff in Te as (Te&Te').
      apply orb_false_iff in Tf as (Tf&Tf').
      rewrite <- binding_finite_spec in B1,B2;simpl in B1,B2;
        rewrite Te,Te' in B1;rewrite Tf,Tf' in B2;simpl in B1,B2;
        repeat rewrite andb_true_iff in B1,B2||rewrite binding_finite_spec in B1,B2.
      destruct B1 as (Be&Be').
      destruct B2 as (Bf&Bf').
      pose proof (IHeq1 Bf Be a b c Fe Ff N1 N2 N3) as IH1.
      pose proof (IHeq2 Bf' Be' a b c Fe' Ff' N1 N2 N3) as IH2.
      clear IHeq1 IHeq2.
      apply ax_inf_PartialOrder;unfold Basics.flip;simpl;split;
        repeat apply inf_join_inf.
      + etransitivity;[|apply inf_cup_left].
        etransitivity;[|apply inf_cup_left].
        rewrite IH1,eq2;reflexivity.
      + etransitivity;[|apply inf_cup_left].
        etransitivity;[|apply inf_cup_right].
        clear IH1 IH2;apply Σ_bounded;intros g Ig.
        apply in_map_iff in Ig as ((β,n)&<-&I).
        etransitivity.
        * apply ax_eq_inf,proper_prod.
          -- apply αKA_act.
             apply splitActStrict_αKA,filter_binding_αKA,eq1.
             ++ apply is_binding_finite_filter_binding;assumption.
             ++ rewrite filter_binding_support;assumption.
             ++ rewrite filter_binding_support;assumption.
             ++ assumption.
          -- apply splitAct_αKA,eq2.
             ++ assumption.
             ++ apply factors_prod,destr_bind_prod in I as ->;reflexivity.
             ++ assumption.
             ++ assumption.
        * non_zero (𝔉 b β f);[apply orb_true_iff;left;apply splitActStrict_test0;assumption|].
          apply Σ_bigger,in_map_iff;exists (β,n);split;[reflexivity|].
          apply factors_prod in I.
          apply factors_In;[|assumption].
          apply test0_false in T as (u&Iu).
          apply filter_binding_lang in Iu as (Iu&<-);[|assumption].
          apply binding_finite_bound_size;tauto.
      + etransitivity;[|apply inf_cup_right].
        clear IH1;apply Σ_bounded;intros g Ig.
        apply in_map_iff in Ig as (((β1,n1),(β2,n2))&<-&I).
        unfold TriRange in I.
        apply pairs_spec in I as (I1&I2).
        apply in_flat_map in I2 as ((?&((?,[]),[]))&I2&heq);try destruct heq as [heq|heq];
          inversion heq;clear heq;subst.
        apply SplitRange_result in I1 as (E1&Min).
        apply factors_prod in I2.
        etransitivity.
        * apply ax_eq_inf,proper_prod.
          -- apply αKA_act.
             apply filter_binding_αKA,filter_binding_αKA,eq1.
             ++ apply is_binding_finite_filter_binding;assumption.
             ++ assumption.
          -- apply IH2.
        * non_zero (𝔉 a β1 (𝔉 b β2 f)).
          apply Σ_bigger,in_map_iff.
          exists ((β1,n1),(β2,n2));split;[reflexivity|].
          apply test0_false in T as (u&Iu).
          apply filter_binding_lang in Iu as (Iu&Ea);
            [|apply is_binding_finite_filter_binding;assumption].
          apply filter_binding_lang in Iu as (Iu&Eb);[|assumption].
          pose proof Iu as Sza;pose proof Iu as Szb.
          apply (binding_finite_bound_size a Bf) in Sza;rewrite Ea in Sza.
          apply (binding_finite_bound_size b Bf) in Szb;rewrite Eb in Szb.
          clear u Iu Ea Eb.
          apply pairs_spec;split.
          -- apply SplitRange_In';tauto.
          -- apply in_flat_map;exists (β2,(n2,false,0));split;[|simpl;tauto].
             apply factors_In;tauto.
      + etransitivity;[|apply inf_cup_left].
        etransitivity;[|apply inf_cup_left].
        rewrite IH1,eq2;reflexivity.
      + etransitivity;[|apply inf_cup_left].
        etransitivity;[|apply inf_cup_right].
        clear IH1 IH2;apply Σ_bounded;intros g Ig.
        apply in_map_iff in Ig as ((β,n)&<-&I).
        etransitivity.
        * apply ax_eq_inf,proper_prod;symmetry.
          -- apply αKA_act.
             apply splitActStrict_αKA,filter_binding_αKA,eq1.
             ++ apply is_binding_finite_filter_binding;assumption.
             ++ rewrite filter_binding_support;assumption.
             ++ rewrite filter_binding_support;assumption.
             ++ assumption.
          -- apply splitAct_αKA,eq2.
             ++ assumption.
             ++ apply factors_prod,destr_bind_prod in I as ->;reflexivity.
             ++ assumption.
             ++ assumption.
        * non_zero (𝔉 b β e);[apply orb_true_iff;left;apply splitActStrict_test0;assumption|].
          apply Σ_bigger,in_map_iff;exists (β,n);split;[reflexivity|].
          apply factors_prod in I.
          apply factors_In;[|assumption].
          apply test0_false in T as (u&Iu).
          apply filter_binding_lang in Iu as (Iu&<-);[|assumption].
          apply binding_finite_bound_size;tauto.
      + etransitivity;[|apply inf_cup_right].
        clear IH1;apply Σ_bounded;intros g Ig.
        apply in_map_iff in Ig as (((β1,n1),(β2,n2))&<-&I).
        unfold TriRange in I.
        apply pairs_spec in I as (I1&I2).
        apply in_flat_map in I2 as ((?&((?,[]),[]))&I2&heq);try destruct heq as [heq|heq];
          inversion heq;clear heq;subst.
        apply SplitRange_result in I1 as (E1&Min).
        apply factors_prod in I2.
        etransitivity.
        * apply ax_eq_inf,proper_prod;symmetry.
          -- apply αKA_act.
             apply filter_binding_αKA,filter_binding_αKA,eq1.
             ++ apply is_binding_finite_filter_binding;assumption.
             ++ assumption.
          -- apply IH2.
        * non_zero (𝔉 a β1 (𝔉 b β2 e)).
          apply Σ_bigger,in_map_iff.
          exists ((β1,n1),(β2,n2));split;[reflexivity|].
          apply test0_false in T as (u&Iu).
          apply filter_binding_lang in Iu as (Iu&Ea);
            [|apply is_binding_finite_filter_binding;assumption].
          apply filter_binding_lang in Iu as (Iu&Eb);[|assumption].
          pose proof Iu as Sza;pose proof Iu as Szb.
          apply (binding_finite_bound_size a Be) in Sza;rewrite Ea in Sza.
          apply (binding_finite_bound_size b Be) in Szb;rewrite Eb in Szb.
          clear u Iu Ea Eb.
          apply pairs_spec;split.
          -- apply SplitRange_In';tauto.
          -- apply in_flat_map;exists (β2,(n2,false,0));split;[|simpl;tauto].
             apply factors_In;tauto.
    - rewrite <- binding_finite_spec in B1,B2;simpl in B1,B2;
        repeat rewrite andb_true_iff in B1,B2||rewrite binding_finite_spec in B1,B2.
      rewrite support_join in F1,F2;simpl_In in *.
     simpl;rewrite IHeq1,IHeq2;try tauto.
     reflexivity.
    - pose proof B1 as Be.
      pose proof B2 as Bf.
      rewrite <- binding_finite_spec in Be,Bf;simpl in Be,Bf;
        repeat rewrite andb_true_iff in Be,Bf||rewrite binding_finite_spec in Be,Bf.
      destruct Be as (Be&_),Bf as (Bf&_).
      rewrite support_star in F1,F2.
      pose proof (IHeq Bf Be a b c F1 F2 N1 N2 N3) as IH;clear IHeq.
      simpl.
      repeat rewrite act_prod||rewrite act_join||rewrite act_star.
      repeat apply proper_prod || apply proper_join || apply proper_star.
      + apply αKA_act,BiLowerExpr_αKA;tauto.
      + apply IH.
      + apply eq.
      + apply αKA_act,BiLowerExpr_αKA;tauto.
      + apply αKA_act,LowerExpr_αKA.
        * apply is_binding_finite_splitActStrict,Bf.
        * apply splitActStrict_αKA;tauto.
      + apply αKA_act,LowerExpr_αKA;tauto.
      + apply splitAct_αKA;tauto.
      + apply eq.
    - destruct H as [a1 a2 e hyp|e f h].
      + apply TriSplitAct_αα;tauto.
      + apply KA_αKA,TriSplitAct_KA,ax_eq_ax,h;tauto.
    - destruct H as [e f|e f].
      + assert (leq : e · f <=α f) by apply eq;clear eq.
        assert (Fe : c # e) by (rewrite support_join,support_prod,support_star in F1;
                                simpl_In in F1;tauto).
        pose proof F2 as Ff;clear F1 F2.
        cut (TriSplitAct c a N b M (e⋆·f)<=αTriSplitAct c a N b M f);[intro h;apply h|].
        non_zero f.
        assert (is_binding_finite (e⋆) /\ is_binding_finite e) as (Bs&Be)
            by (repeat rewrite <- binding_finite_spec in *;apply not_true_iff_false in T;
                simpl in *;repeat rewrite andb_true_iff in *||rewrite orb_true_iff in *;tauto).
        pose proof B2 as Bf;clear B1 B2.
        assert (IH: forall N M, TriSplitAct c a N b M (e·f) <=α TriSplitAct c a N b M f)
          by (intros N' M';apply IHeq;try tauto;
              [repeat rewrite <- binding_finite_spec in *;simpl in *;
               rewrite Be,Bf,orb_true_r;reflexivity
              |rewrite support_join,support_prod;simpl_In;tauto]);clear IHeq.
        case_eq (test0 e);intros T';
          [apply KA_αKA_inf,TriSplitAct_KA_inf;try tauto;
           apply test0_spec in T' as ->;apply ax_eq_inf;transitivity (𝟭·f);
           [apply ax_eq_prod,ax_eq_refl;apply ka_zero_star|apply left_unit]|].
        simpl in *;rewrite T' in IH;rewrite T in *;simpl in *.
        repeat rewrite (semiring_left_distr _ _ _)
        || rewrite (semiring_right_distr _ _ _)
        || apply inf_join_inf.
        * repeat rewrite <- (mon_assoc _ _ _).
          rewrite (ka_star_left_ind leq).
          etransitivity.
          -- apply proper_prod_inf;[reflexivity|].
             etransitivity;[|apply IH].
             rewrite <- inf_cup_left.
             apply inf_cup_left.
          -- apply ka_star_left_ind.
             unfold BiLowerExpr;rewrite Σ_act,Σ_distr_r;unfold act,act_lists;repeat rewrite map_map.
             apply Σ_bounded;intros ? I;apply in_map_iff in I as ((α,β)&<-&I).
             apply pairs_spec in I as (Iα&Iβ);simpl.
             rewrite <- IH at 2.
             rewrite <- inf_cup_right.
             transitivity ([(a, b); (b, c)] ∙ 𝔉 a α (𝔉 b β e) · TriSplitAct c a N b M f).
             ++ apply proper_prod_inf;[|reflexivity].
                apply αKA_inf_act.
                apply KA_αKA_inf,CompletenessKA_inf.
                intros u Iu;repeat rewrite filter_binding_lang in *
                  by (try apply is_binding_finite_filter_binding;tauto);tauto.
             ++ non_zero (𝔉 a α (𝔉 b β e)).
                apply Σ_bigger,in_map_iff.
                exists ((α,N),(β,M));split;[reflexivity|].
                apply test0_false in T0 as (u&Iu).
                apply filter_binding_lang in Iu as (Iu&E1);
                  [|apply is_binding_finite_filter_binding,Be].
                apply filter_binding_lang in Iu as (Iu&E2);[|apply Be].
                pose proof (binding_finite_bound_size a Be Iu) as Sα;
                  pose proof (binding_finite_bound_size b Be Iu) as Sβ;
                  rewrite E1 in Sα;rewrite E2 in Sβ;clear u Iu E1 E2.
                apply pairs_spec;split.
                ** apply SplitRange_In'.
                   --- assumption.
                   --- apply lower_squares_prod_destr_true,Iα.
                   --- intros (([],?),?);unfold prod_binding;simpl;intros <- ;
                         rewrite lower_squares_alt in Iα by reflexivity;
                         unfold square,d_binding in Iα;simpl in *;lia.
                ** apply in_flat_map;exists (β,M▶);split;[|simpl;tauto].
                   apply factors_In;[assumption|].
                   apply lower_squares_prod_destr_false,Iβ.
        * repeat rewrite <- (mon_assoc _ _ _).
          rewrite (ka_star_left_ind leq).
          etransitivity.
          -- apply proper_prod_inf;[reflexivity|].
             apply proper_prod_inf;[reflexivity|].
             apply proper_prod_inf;[reflexivity|].
             transitivity (splitAct c b (M,false,0) (e·f)).
             ++ unfold splitAct;simpl.
                rewrite T,T';simpl.
                rewrite map_app,map_map,<-algebra.Σ_app,<-inf_cup_left.
                rewrite Σ_distr_r,map_map;simpl.
                apply ax_eq_inf,Σ_map_equiv_α.
                intros (e1,e2) _;simpl;symmetry;apply mon_assoc.
             ++ apply splitAct_αKA_inf,leq;try tauto.
                rewrite support_prod;simpl_In;tauto.
          -- etransitivity.
             ++ apply proper_prod_inf;[reflexivity|].
                apply proper_prod_inf;[reflexivity|].
                rewrite act_star;apply ka_star_left_ind.
                transitivity (splitAct c b (M,false,0) (e·f)).
                ** unfold splitAct;simpl.
                   rewrite T,T';simpl.
                   rewrite map_app,<-algebra.Σ_app,<-inf_cup_right.
                   unfold LowerExpr.
                   rewrite Σ_act,Σ_distr_r;simpl.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as (g'&<-&Ig').
                   apply In_act_lists,in_map_iff in Ig'.
                   destruct Ig' as (β&EE&Iβ).
                   rewrite <- (act_bij [(b,c)]),act_p_pinv in EE;subst.
                   non_zero (𝔉 b β e).
                   apply test0_false in T0 as (u&Iu).
                   apply filter_binding_lang in Iu as (Iu&Eu);[|assumption].
                   apply (binding_finite_bound_size b Be) in Iu as Sβ;rewrite Eu in Sβ;clear u Eu Iu.
                   rewrite Σ_distr_l,map_map.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as ((f1&f2)&<-&If).
                   simpl;rewrite (mon_assoc _ _ _),<-act_prod.
                   apply Σ_bigger,in_map_iff;exists (𝔉 b β e · f1, f2);split;[reflexivity|].
                   apply in_flat_map;exists (β,M▶);split.
                   --- apply factors_In;[assumption|].
                       apply lower_squares_prod_destr_false,Iβ.
                   --- apply in_map_iff;exists (f1,f2);tauto.
                ** apply splitAct_αKA_inf,leq;try tauto.
                   rewrite support_prod;simpl_In;tauto.
             ++ etransitivity.
                ** apply proper_prod_inf;[reflexivity|].
                   etransitivity;[|apply (IH N M)].
                   rewrite <- inf_cup_left,<-inf_cup_right.
                   unfold LowerExpr.
                   rewrite Σ_act,Σ_distr_r;simpl.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as (g'&<-&Ig').
                   apply In_act_lists,in_map_iff in Ig'.
                   destruct Ig' as (β&EE&Iβ).
                   rewrite <- (act_bij [(b,c)]),act_p_pinv in EE;subst.
                   etransitivity.
                   --- apply proper_prod_inf;[|reflexivity].
                       apply αKA_inf_act.
                       apply KA_αKA_inf,CompletenessKA_inf.
                       intros u Iu.
                       apply filter_binding_lang in Iu as (Iu&Eu);
                         [|apply is_binding_finite_splitActStrict,Be].
                       apply splitActStrict_lang in Iu as (u1&u2&->&Iu&Ea);[|assumption].
                       revert Eu;simpl_binding;rewrite 𝗙_perm;unfold act at 1;simpl;simpl_eqX.
                       rewrite <-𝗙_app;intros Eu.
                       apply splitActStrict_lang;[apply is_binding_finite_filter_binding,Be|].
                       exists u1,u2;split;[reflexivity|].
                       split;[|apply Ea].
                       apply filter_binding_lang;[|split;[|apply Eu]];assumption.
                   --- non_zero (𝔉 b β e);[rewrite splitActStrict_test0;tauto|].
                       apply test0_false in T0 as (u&Iu).
                       apply filter_binding_lang in Iu as (Iu&Eu);[|assumption].
                       apply (binding_finite_bound_size b Be) in Iu as Sβ;rewrite Eu in Sβ;
                         clear u Eu Iu.
                       apply Σ_bigger,in_map_iff;exists (β,M▶);split;[reflexivity|].
                       apply factors_In;[assumption|].
                       apply lower_squares_prod_destr_false,Iβ.
                ** rewrite act_star;apply ka_star_left_ind.
                   rewrite <- IH at 2.
                   rewrite <- inf_cup_right.
                   unfold BiLowerExpr;rewrite Σ_act,Σ_distr_r.
                   unfold act at 1,act_lists.
                   repeat rewrite map_map.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as ((α,β)&<-&I).
                   apply pairs_spec in I as (Iα&Iβ);simpl.
                   etransitivity.
                   --- apply proper_prod_inf;[|reflexivity].
                       apply αKA_inf_act.
                       apply KA_αKA_inf,CompletenessKA_inf.
                       intros u Iu.
                       apply filter_binding_lang in Iu as (Iu&Eub);
                         [|apply is_binding_finite_filter_binding,Be].
                       apply filter_binding_lang in Iu as (Iu&Eua);[|assumption].
                       apply filter_binding_lang;[apply is_binding_finite_filter_binding,Be|].
                       split;[|apply Eua].
                       apply filter_binding_lang;[apply Be|].
                       split;[assumption|apply Eub].
                   --- non_zero (𝔉 a α (𝔉 b β e)).
                       apply test0_false in T0 as (u&Iu).
                       apply filter_binding_lang in Iu as (Iu&Eua);
                         [|apply is_binding_finite_filter_binding,Be].
                       apply filter_binding_lang in Iu as (Iu&Eub);[|assumption].
                       apply (binding_finite_bound_size b Be) in Iu as Sβ;rewrite Eub in Sβ.
                       apply (binding_finite_bound_size a Be) in Iu as Sα;rewrite Eua in Sα.
                       clear u Eua Eub Iu.
                       apply Σ_bigger,in_map_iff;exists ((α,N),(β,M));split;[reflexivity|].
                       apply pairs_spec;split.
                       +++ apply SplitRange_In';[assumption|apply lower_squares_prod_destr_true,Iα|].
                           intros (([],?),?);unfold prod_binding;simpl;intros <-.
                           *** apply lower_squares_alt in Iα as (Eα&h);[|reflexivity].
                               unfold square,d_binding in *;simpl in *;subst.
                               lia.
                           *** apply lower_squares_alt in Iα as (Eα&h);[|reflexivity].
                               unfold square,d_binding in *;simpl in *;subst.
                               lia.
                       +++ apply in_flat_map;exists (β,M▶);split;[|simpl;tauto].
                           apply factors_In;[assumption|].
                           apply lower_squares_prod_destr_false,Iβ.
        * apply Σ_bounded;intros g I.
          apply in_map_iff in I as ((β1,β2)&<-&Iβ).
          destruct β1 as ((K&ff)&?);simpl in *;subst.
          apply factors_prod,destr_bind_prod_full in Iβ as (->&h).
          unfold d_binding in *.
          destruct β2 as ((K'&?)&?);simpl in *.
          non_zero (𝔉 b (K, ff, n) (e ⋆));[rewrite splitActStrict_test0;tauto|].
          apply binding_finite_sqExpr_star in Bs as (Bs&Sq).
          apply test0_false in T0 as (u&Iu).
          apply filter_binding_lang in Iu as (Iu&Eb);[|assumption].
          apply (is_binding_finite_bindings Bs b),Sq in Iu.
          rewrite Eb in Iu.
          unfold square,d_binding in Iu;simpl in Iu;subst;clear Eb u.
          assert (K' = M) as -> by (destruct h as [h|h];[|inversion h];lia).
          assert (h' : K < M \/ K = M /\ ff = false) by (destruct h as [h|h];[|inversion h];tauto);
            clear h.
          etransitivity.
          -- apply proper_prod_inf;[|reflexivity].
             apply αKA_inf_act.
             apply KA_αKA_inf,CompletenessKA_inf.
             intros u Iu;apply splitActStrict_lang in Iu as (u1&u2&->&Iu&Ea);
               [|apply is_binding_finite_filter_binding,Bs].
             apply filter_binding_lang in Iu as (Iu&Eb);[|assumption].
             apply (@LowerExpr_lang _ _ _ _ b M false);[apply is_binding_finite_splitActStrict,Bs|].
             split;[apply splitActStrict_lang;
                    [|exists u1,u2;split;[reflexivity|split;[eassumption|]]]|].
             ++ assumption.
             ++ apply Ea.
             ++ rewrite 𝗙_app,𝗙_perm.
                unfold act;simpl;simpl_eqX.
                rewrite <- 𝗙_app.
                apply lower_squares_alt;[reflexivity|].
                rewrite Eb in *.
                split;[reflexivity|].
                simpl.
                rewrite orb_false_r,negb_true_iff;assumption.
          -- clear K h' ff b0 n0;simpl.
             transitivity ([(b, c)] ∙ ([(a, c)] ∙ (BiLowerExpr a N true b M false e ⋆)
                                                · LowerExpr b M false (splitActStrict c a N e)
                                                · LowerExpr b M false e ⋆)
                                    · splitAct c b (M, false, 0) f).
             ++ clear IH.
                apply proper_prod_inf;[|reflexivity].
                apply αKA_inf_act.
                apply KA_αKA_inf,CompletenessKA_inf.
                intros u Iu.
                apply LowerExpr_lang in Iu as ((u'&u3&->&(u1&u''&->&Iu1&Iu)&Iu3)&Ib).
                ** rewrite<- act_star in Iu1.
                   apply act_lang,LowerExpr_star_lang in Iu1 as (Iu1&Ia1);[|assumption].
                   apply splitActStrict_lang in Iu as (v1&v2&->&Iu2&Ea2);[|assumption].
                   simpl_binding in Ib.
                   pose proof (is_binding_finite_bindings Bs b Iu1) as Sq1;apply Sq in Sq1.
                   pose proof (is_binding_finite_bindings Bs b Iu3) as Sq3;apply Sq in Sq3.
                   assert (Sq2 : ⟦e⋆⟧(v1++v2)) by (now exists 1,(v1++v2),[];rewrite app_nil_r;repeat split).
                   apply (is_binding_finite_bindings Bs b) in Sq2;apply Sq in Sq2.
                   rewrite 𝗙_perm in Sq1;unfold act in Sq1;simpl in Sq1;revert Sq1;simpl_eqX;intro.
                   revert Ib;rewrite 𝗙_perm;unfold act at 1;intro;simpl in Ib;
                     revert Ib;simpl_eqX;rewrite <- 𝗙_app;intro.
                   apply lower_squares_prod in Ib as (Ib&Ib4);try reflexivity||assumption;
                     [|rewrite <- prod_binding_maxBind by assumption;apply maxBind_square;assumption].
                   apply lower_squares_prod in Ib as (Ib1&Ib2);try reflexivity||assumption.
                   exists (u1 ++ [(a, c)] ∙ v1 ++ v2),u3;split;[reflexivity|].
                   split.
                   --- exists u1,([(a,c)]∙v1++v2);split;[reflexivity|].
                       split.
                       +++ apply act_lang,BiLowerExpr_star_lang;[assumption|].
                           split;[assumption|].
                           split;[assumption|].
                           rewrite 𝗙_perm;unfold act;simpl;simpl_eqX;assumption.
                       +++ apply LowerExpr_lang;[apply is_binding_finite_splitActStrict,Be|].
                           rewrite 𝗙_app,𝗙_perm;unfold act at 2;simpl;simpl_eqX.
                           rewrite <- 𝗙_app.
                           split;[|assumption].
                           apply splitActStrict_lang;[assumption|].
                           exists v1,v2;tauto.
                   --- apply LowerExpr_star_lang;[assumption|].
                       tauto.
                ** clear Iu H u f T leq Ff Bf.
                   pose proof (LowerExpr_star_is_binding_finite a N true Bs) as BL.
                   rewrite <- (is_binding_finite_act [(a,c)]),act_star in BL.
                   pose proof (is_binding_finite_splitActStrict c a N Be) as BS.
                   rewrite <- binding_finite_spec in *;simpl in *.
                   rewrite BS,Bs,BL.
                   repeat rewrite orb_true_iff||rewrite andb_true_iff;tauto.
             ++ repeat rewrite act_prod||rewrite act_star.
                repeat rewrite <- (mon_assoc _ _ _).
                etransitivity;[apply proper_prod_inf;[|rewrite ka_star_left_ind];try reflexivity|].
                ** etransitivity;[|apply splitAct_αKA_inf,leq;
                                   try (rewrite support_prod;simpl_In);tauto].
                   apply KA_αKA_inf,CompletenessKA_inf.
                   intros u (u1&u2&->&Iu1&Iu2).
                   apply act_lang,LowerExpr_lang in Iu1 as (Iu1&Eu1);[|assumption].
                   apply splitAct_lang in Iu2 as (v1&v2&->&Iu2&Pu2&Eu2);[|assumption].
                   apply splitAct_lang;[rewrite <- binding_finite_spec in *;simpl in *;
                                        rewrite Be,Bf,orb_true_r;reflexivity|].
                   exists ([(b,c)]∗∙u1++v1),v2.
                   rewrite act_lists_app,act_p_pinv,app_ass.
                   split;[reflexivity|].
                   split;[|split].
                   --- exists ([(b,c)]∗∙u1),(v1++v2).
                       rewrite app_ass;tauto.
                   --- intro EE;apply app_eq_nil in EE;tauto.
                   --- simpl_binding;rewrite Eu2.
                       apply lower_squares_prod_destr_false,Eu1.
                ** etransitivity;[apply proper_prod_inf;[reflexivity|etransitivity;
                                                                     [|apply (IH N M)]]|].
                   --- rewrite <- inf_cup_left,<- inf_cup_right.
                       unfold LowerExpr;rewrite Σ_act.
                       unfold act at 1,act_lists;rewrite map_map,Σ_distr_r,map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (β&<-&Iβ).
                       destruct_leb (size β) (sizeExpr e).
                       +++ etransitivity;[|apply Σ_bigger,in_map_iff;exists (β,M▶);
                                           split;[reflexivity
                                                 |apply factors_In;
                                                  [assumption
                                                  |apply lower_squares_prod_destr_false,Iβ]]].
                           apply proper_prod_inf;[|reflexivity].
                           apply αKA_inf_act,KA_αKA_inf,CompletenessKA_inf.
                           intros u Iu.
                           apply filter_binding_lang in Iu as (Iu&Eb);
                             [|apply is_binding_finite_splitActStrict,Be].
                           apply splitActStrict_lang in Iu as (u1&u2&->&Iu&Ea);[|assumption].
                           apply splitActStrict_lang;[apply is_binding_finite_filter_binding,Be|].
                           exists u1,u2;split;[reflexivity|];split;[|assumption].
                           clear Ea.
                           apply filter_binding_lang;[assumption|split;[assumption|]].
                           rewrite <- Eb;simpl_binding.
                           rewrite 𝗙_perm;unfold act;simpl;simpl_eqX;reflexivity.
                       +++ etransitivity;[|apply zero_minimal].
                           apply ax_eq_inf,KA_αKA,test0_spec.
                           simpl;rewrite test0_act.
                           apply orb_true_iff;left.
                           apply not_false_is_true;intros Tu.
                           apply test0_false in Tu as (u&Iu).
                           apply filter_binding_lang in Iu as (Iu&Eb);
                             [|apply is_binding_finite_splitActStrict,Be].
                           apply splitActStrict_lang in Iu as (u1&u2&->&Iu&Ea);[|assumption].
                           revert Eb;simpl_binding;rewrite 𝗙_perm;unfold act;simpl;simpl_eqX.
                           rewrite <- 𝗙_app;intro.
                           apply (binding_finite_bound_size b Be) in Iu;rewrite Eb in *;lia.
                   --- repeat rewrite act_star.
                       apply ka_star_left_ind;rewrite <- IH at 2.
                       rewrite <- inf_cup_right.
                       unfold BiLowerExpr.
                       repeat rewrite Σ_act;unfold act at 1 2,act_lists.
                       rewrite Σ_distr_r;repeat rewrite map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as ((α,β)&<-&I);simpl.
                       apply pairs_spec in I as (Iα,Iβ).
                       non_zero (𝔉 b β(𝔉 a α e)).
                       apply test0_false in T0 as (u&Iu).
                       apply filter_binding_lang in Iu as (Iu&E2);
                         [|apply is_binding_finite_filter_binding,Be].
                       apply filter_binding_lang in Iu as (Iu&E1);[|apply Be].
                       pose proof (binding_finite_bound_size a Be Iu) as Sα;
                         pose proof (binding_finite_bound_size b Be Iu) as Sβ;
                         rewrite E1 in Sα;rewrite E2 in Sβ;clear u Iu E1 E2.
                       transitivity ([(a, b); (b, c)] ∙ 𝔉 a α (𝔉 b β e) · TriSplitAct c a N b M f).
                       +++ apply proper_prod_inf;[|reflexivity].
                           rewrite action_compose.
                           etransitivity;[apply αKA_inf_act
                                         |erewrite support_eq_action_eq;[reflexivity|]].
                           *** apply KA_αKA_inf,CompletenessKA_inf.
                               intros u Iu;repeat rewrite filter_binding_lang in *
                                 by (try apply is_binding_finite_filter_binding;tauto);tauto.
                           *** intros d.
                               repeat rewrite filter_binding_support.
                               intros Id;unfold act;simpl.
                               destruct_eqX d a;subst;[simpl_eqX;reflexivity|].
                               destruct_eqX d c;subst;[simpl_eqX;reflexivity|].
                               destruct_eqX d b;subst;[simpl_eqX;reflexivity|].
                               simpl_eqX;reflexivity.
                       +++ apply Σ_bigger,in_map_iff.
                           exists ((α,N),(β,M));split;[reflexivity|].
                           apply pairs_spec;split.
                           *** apply SplitRange_In';[assumption| |].
                               ---- apply lower_squares_prod_destr_true,Iα.
                               ---- intros (([],?),?);unfold prod_binding;simpl;intros <- ;
                                      rewrite lower_squares_alt in Iα by reflexivity;
                                      unfold square,d_binding in *;simpl in *;lia.
                           *** apply in_flat_map;exists (β,M▶);split;[|simpl;tauto].
                               apply factors_In;[assumption|].
                               apply lower_squares_prod_destr_false,Iβ.
        * apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as (((α,N'),(β,M'))&<-&I).
          unfold TriRange in I;apply pairs_spec in I as (Iα&Iβ).
          apply SplitRange_result in Iα as (Eα&Minα).
          apply in_flat_map in Iβ as ((?&((?&[])&[]))&Eβ&h);simpl in h;try tauto.
          destruct h as [h|h];[|tauto].
          inversion h;subst;clear h.
          apply factors_prod in Eβ.
          non_zero (𝔉 a α (𝔉 b β (e⋆))).
          apply test0_false in T0 as (u&Iu).
          apply filter_binding_lang in Iu as (Iu&E1);
            [|apply is_binding_finite_filter_binding,Bs].
          apply filter_binding_lang in Iu as (Iu&E2);[|apply Bs].
          pose proof (binding_finite_bound_size a Bs Iu) as Sα;
            pose proof (binding_finite_bound_size b Bs Iu) as Sβ.
          apply binding_finite_sqExpr_star in Bs as (Bs&Sq).
          pose proof (is_binding_finite_bindings Bs a Iu) as Sqα.
          pose proof (is_binding_finite_bindings Bs b Iu) as Sqβ.
          rewrite E1 in *;rewrite E2 in *;clear u Iu E1 E2.
          apply Sq in Sqα;apply Sq in Sqβ.
          assert (α ∈ lower_squares (S N',false,S N')
                  /\ β ∈ lower_squares (M',false,M')) as (Iα&Iβ).
          -- split;rewrite lower_squares_alt by reflexivity;split;try assumption.
             ++ apply destr_bind_prod_full in Eα.
                unfold square,d_binding in *;simpl in *.
                rewrite Sqα in *.
                destruct Eα as (_&[(h1&h2)|h]).
                ** left;lia.
                ** subst;simpl in *;inversion Sqα;tauto.
             ++ apply destr_bind_prod_full in Eβ.
                unfold square,d_binding in *;simpl in *.
                rewrite Sqβ in *.
                destruct Eβ as (_&[(h1&h2)|h]).
                ** left;lia.
                ** subst;simpl in *;inversion Sqβ;tauto.
          -- clear Sqα Sqβ.
             assert (N' = N /\ M' = M) as (->&->).
             ++ split.
                ** apply destr_bind_prod_full in Eα as (_&h).
                   apply lower_squares_alt in Iα as (EE&_);[|reflexivity].
                   destruct α as ((K&ff)&?);unfold square,d_binding in *;simpl in *;subst.
                   destruct h as [h|h];[lia|].
                   inversion h;lia.
                ** apply destr_bind_prod_full in Eβ as (_&h).
                   apply lower_squares_alt in Iβ as (EE&_);[|reflexivity].
                   destruct β as ((K&ff)&?);unfold square,d_binding in *;simpl in *;subst.
                   destruct h as [h|h];[lia|].
                   inversion h;lia.
             ++ rewrite lower_squares_false in Iα;destruct Iα as [<-|Iα].
                ** exfalso;apply (Minα (0,false,S N));reflexivity.
                ** transitivity ([(a, b); (b, c)] ∙ BiLowerExpr b M false a N true e ⋆
                                                  · TriSplitAct c a N b M f).
                   --- apply proper_prod_inf;[|reflexivity].
                       rewrite <- act_star.
                       apply αKA_inf_act.
                       apply KA_αKA_inf,CompletenessKA_inf.
                       intros u Iu;repeat rewrite filter_binding_lang in Iu
                         by (try apply is_binding_finite_filter_binding;tauto).
                       apply BiLowerExpr_star_lang;[assumption|].
                       destruct Iu as ((Iu&->)&->);tauto.
                   --- clear α β Eα Eβ Sα Sβ Iα Iβ Minα.
                       apply ka_star_left_ind.
                       unfold BiLowerExpr.
                       rewrite Σ_act;unfold act,act_lists.
                       rewrite Σ_distr_r;repeat rewrite map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as ((β&α)&<-&I).
                       apply pairs_spec in I as (Iβ&Iα);simpl.
                       rewrite <- IH at 2.
                       rewrite <- inf_cup_right.
                       non_zero (𝔉 a α (𝔉 b β e)).
                       apply test0_false in T0 as (u&Iu).
                       apply filter_binding_lang in Iu as (Iu&E1);
                         [|apply is_binding_finite_filter_binding,Be].
                       apply filter_binding_lang in Iu as (Iu&E2);[|apply Be].
                       pose proof (binding_finite_bound_size a Be Iu) as Sα;
                         pose proof (binding_finite_bound_size b Be Iu) as Sβ;
                         rewrite E1 in Sα;rewrite E2 in Sβ;clear u Iu E1 E2.
                       
                       apply Σ_bigger,in_map_iff;exists ((α,N),(β,M));split;[reflexivity|].
                       apply pairs_spec;split.
                       +++ apply SplitRange_In';[assumption| |].
                           *** apply lower_squares_prod_destr_true,Iα.
                           *** intros (([],?)&?);unfold prod_binding;simpl;intros <- ;
                                 rewrite lower_squares_alt in Iα by reflexivity;
                                 unfold square,d_binding in *;simpl in *;destruct Iα as (->&h);lia.
                       +++ apply in_flat_map;exists (β,M▶);split;[|simpl;tauto].
                           apply factors_In;[assumption|].
                           apply lower_squares_prod_destr_false,Iβ.
      + assert (leq : e · f <=α e) by apply eq;clear eq.
        assert (Ff : c # f) by (rewrite support_join,support_prod,support_star in F1;
                                simpl_In in F1;tauto).
        pose proof F2 as Fe;clear F1 F2.
        cut (TriSplitAct c a N b M (e·f⋆)<=αTriSplitAct c a N b M e);[intro h;apply h|].
        non_zero e.
        assert (is_binding_finite (f⋆) /\ is_binding_finite f) as (Bs&Bf)
            by (repeat rewrite <- binding_finite_spec in *;apply not_true_iff_false in T;
                simpl in *;repeat rewrite andb_true_iff in *||rewrite orb_true_iff in *;
                revert B1 T;clear; intuition).
        pose proof B2 as Be;clear B1 B2.
        assert (IH: forall N M, TriSplitAct c a N b M (e·f) <=α TriSplitAct c a N b M e)
          by (intros N' M';apply IHeq;try tauto;
              [repeat rewrite <- binding_finite_spec in *;simpl in *;
               rewrite Be,Bf,orb_true_r;reflexivity
              |rewrite support_join,support_prod;simpl_In;tauto]);clear IHeq.
        case_eq (test0 f);intros T';
          [apply KA_αKA_inf,TriSplitAct_KA_inf;try tauto;
           apply test0_spec in T' as ->;apply ax_eq_inf;transitivity (e·𝟭);
           [apply ax_eq_prod,ka_zero_star;reflexivity|apply right_unit]|].
        simpl in *;rewrite T' in IH;rewrite T in *;simpl in *.
        repeat apply inf_join_inf.
        * apply ka_star_right_ind.
          rewrite <- IH at 2.
          repeat rewrite <- inf_cup_left.
          reflexivity.
        * apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((β1,β2)&<-&Iβ).
          pose proof (factors_prod Iβ) as Eβ.
          apply destr_bind_prod_full in Eβ as (Eβ2&Hβ).
          destruct β2 as ((K&?)&?);unfold d_binding in Eβ2;inversion Eβ2;clear Eβ2;simpl in *;subst.
          replace (d_binding(K,false,0)) with K in * by reflexivity.
          transitivity ([(b, c)] ∙ splitActStrict c a N (𝔉 b β1 e)
                                 · [(b,c)]∙ (LowerExpr b K false f) ⋆
                                 · splitAct c b (K,false,0) f · f⋆).
          -- repeat rewrite <- (mon_assoc _ _ _).
             apply proper_prod_inf;[reflexivity|].
             clear Iβ Hβ β1 M IH e leq T Be Fe N.
             apply KA_αKA_inf,CompletenessKA_inf.
             intros u Iu.
             apply splitAct_lang in Iu as (u1&u2&->&Iu&Pu&Eu);[|assumption].
             apply split_star_strict in Iu as (w1&w2&w3&w4&->&Pw2&->&I1&I2&I3);[|assumption].
             rewrite act_lists_app;rewrite app_ass,<-(app_ass _ w3).
             assert (Sq : ⟦f⋆⟧ w1) by apply I1.
             apply (is_binding_finite_bindings Bs b) in Sq.
             apply binding_finite_sqExpr_star in Bs as (Bs&Sqf);apply Sqf in Sq.
             simpl_binding in Eu;apply destr_bind_prod_full in Eu as (Eβ2&Eu). 
             remember (𝗙 b w2) as β2;destruct β2 as ((N,?)&?).
             remember (𝗙 b w1) as β1;destruct β1 as ((M,ff)&?).
             unfold square,d_binding in *;simpl in Eu,Sq;inversion Eβ2;clear Eβ2;subst;simpl_nat.
             exists ([(b,c)]∙w1),(([(b,c)]∙w2++w3)++w4);split;[reflexivity|split].
             ++ rewrite <-act_star,act_lang,act_pinv_p.
                apply LowerExpr_star_lang;[assumption|].
                split;[apply I1|].
                apply lower_squares_alt;[reflexivity|rewrite <- Heqβ1];simpl.
                split;[reflexivity|].
                destruct Eu as [(L&->)|Eu];[tauto|].
                inversion Eu;subst.
                right;split;reflexivity.
             ++ exists ([(b,c)]∙w2++w3),w4;split;[reflexivity|split;[|assumption]].
                apply splitAct_lang;[assumption|].
                exists w2,w3;rewrite <- Heqβ2.
                repeat split; try assumption.
                destruct Eu as [(_&->)|EE];[|inversion EE];reflexivity.
          -- rewrite <- act_star,<- act_prod.
             destruct Hβ as [(h1&h2)| ->].
             ++ set (B := prj1 ((fun p => snd p =?= (K▶)) :> factors (M,false,0) (sizeExpr e))).
                transitivity ((([(b,c)]∙(Σ (map (fun β => splitActStrict c a N (𝔉 b β e)) B)
                                           · LowerExpr b K false f ⋆))
                                 · splitAct c b (K, false, 0) f) · f ⋆).
                ** repeat (apply proper_prod_inf;[|reflexivity]).
                   apply αKA_inf_act.
                   apply proper_prod_inf;[|reflexivity].
                   apply Σ_bigger,in_map_iff.
                   exists β1;split;[reflexivity|].
                   apply in_map_iff;exists (β1,K▶);split;[reflexivity|].
                   simpl_In;split;[assumption|].
                   simpl_eqX;reflexivity.
                ** clear β1 Iβ h1 h2; etransitivity.
                   --- repeat (apply proper_prod_inf;[|reflexivity]).
                       apply αKA_inf_act.
                       apply ka_star_right_ind.
                       rewrite Σ_distr_r,map_map.
                       apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as (β1&<-&Iβ1).
                       unfold LowerExpr;rewrite Σ_distr_l,map_map.
                       apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as (β2&<-&Iβ2).
                       transitivity (splitActStrict c a N (𝔉 b (β1 ⋅ β2) e)).
                       +++ etransitivity;[|apply splitActStrict_αKA_inf,filter_binding_αKA_inf,leq].
                           *** clear IH;apply KA_αKA_inf,CompletenessKA_inf;intros u Iu.
                               destruct Iu as (?&u3&->&Iu&Iu3).
                               apply splitActStrict_lang in Iu as (u1&u2&->&Iu&Eu1&Min);
                                 [|apply is_binding_finite_filter_binding,Be].
                               apply filter_binding_lang in Iu as (Iu&Eu');[|assumption]. 
                               apply filter_binding_lang in Iu3 as (Iu3&Eu3);[|assumption].
                               apply splitActStrict_lang;
                                 [apply is_binding_finite_filter_binding;
                                  revert T T' Be Bf;clear;repeat rewrite <- binding_finite_spec;
                                  simpl;intros -> -> -> ->;reflexivity|].
                               exists u1,(u2++u3);rewrite app_ass;repeat split;try assumption.
                               apply filter_binding_lang;
                                 [revert T T' Be Bf;clear;repeat rewrite <- binding_finite_spec;
                                  simpl;intros -> -> -> ->;reflexivity|].
                               split.
                               ---- exists (u1++u2),u3;rewrite <- app_ass;tauto.
                               ---- rewrite <- app_ass,𝗙_app,Eu',Eu3;reflexivity.
                           *** apply is_binding_finite_filter_binding,Be.
                           *** rewrite filter_binding_support,support_prod;simpl_In;tauto.
                           *** rewrite filter_binding_support;simpl_In;tauto.
                           *** assumption.
                       +++ non_zero (𝔉 b (β1 ⋅ β2) e);[apply splitActStrict_test0,T0|].
                           apply Σ_bigger,in_map_iff;exists (β1⋅β2);split;[reflexivity|].
                           unfold B in Iβ1;apply in_map_iff in Iβ1 as ((?&?)&EE'&I).
                           simpl_In in I.
                           destruct I as (I&EE).
                           rewrite eqX_correct in EE;simpl in EE,EE';subst.
                           apply in_map_iff;exists (β1⋅β2,K▶).
                           split;[reflexivity|];simpl_In.
                           split;[|apply eqX_correct;reflexivity].
                           apply factors_In.
                           *** apply test0_false in T0 as (u&Iu).
                               apply filter_binding_lang in Iu as (Iu&<-);[|assumption].
                               apply binding_finite_bound_size,Iu;assumption.
                           *** apply destr_bind_prod_full;split;[reflexivity|].
                               simpl_binding.
                               apply lower_squares_alt in Iβ2 ;[|reflexivity].
                               apply factors_prod,destr_bind_prod_full in I as (_&h).
                               destruct β1 as ((d1,f1),c1),β2 as ((d2,f2),c2).
                               unfold square,d_binding in *;simpl in *.
                               destruct Iβ2 as (->&h').
                               rewrite orb_false_r,negb_true_iff in h'.
                               destruct h as [(h1&h2)|h].
                               ---- destruct h' as [h'|(->&->)].
                                    ++++ lia.
                                    ++++ unfold prod_binding;destruct_ltb c1 K;[lia|].
                                         rewrite h2;right;reflexivity.
                               ---- inversion h;subst;clear h.
                                    unfold prod_binding.
                                    destruct_ltb K d2;[|lia].
                                    destruct_ltb d2 K;simpl.
                                    ++++ destruct h' as [h'|(->&->)];[lia|].
                                         right;reflexivity.
                                    ++++ right;simpl_nat;reflexivity.
                   --- rewrite Σ_act,Σ_distr_r,Σ_distr_r.
                       unfold act,act_lists.
                       repeat rewrite map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (β&<-&Iβ).
                       etransitivity.
                       +++ apply proper_prod_inf;[|reflexivity].
                           etransitivity;[|apply (IH N M)].
                           rewrite <- inf_cup_left,<-inf_cup_right.
                           apply Σ_bigger,in_map_iff.
                           exists (β,K▶);split;[reflexivity|].
                           unfold B in Iβ;apply in_map_iff in Iβ as ((?&?)&EE'&I).
                           simpl_In in I.
                           destruct I as (I&EE).
                           rewrite eqX_correct in EE;simpl in EE,EE';subst.
                           assumption.
                       +++ apply ka_star_right_ind.
                           rewrite <- (IH N M) at 2.
                           rewrite <- inf_cup_left,<-inf_cup_left;reflexivity.
             ++ etransitivity.
                ** apply proper_prod_inf;[|reflexivity].
                   apply proper_prod_inf;[|reflexivity].
                   apply αKA_inf_act,ka_star_right_ind.
                   etransitivity;[|apply splitActStrict_αKA_inf,filter_binding_αKA_inf,leq].
                   --- apply KA_αKA_inf,CompletenessKA_inf;clear IH.
                       intros u (u1&u2&->&Iu1&Iu2).
                       apply splitActStrict_lang in Iu1 as (v1&v2&->&Iu1&hv);
                         [|apply is_binding_finite_filter_binding,Be].
                       apply filter_binding_lang in Iu1 as (Iu1&Eu1);[|assumption].
                       apply LowerExpr_lang in Iu2 as (Iu2&Eu2);[|assumption].
                       apply splitActStrict_lang;
                         [apply is_binding_finite_filter_binding;
                          revert Be Bf T T';clear;repeat rewrite <- binding_finite_spec;simpl;
                          intros -> -> -> ->;reflexivity|].
                       exists v1,(v2++u2);rewrite app_ass;repeat split.
                       +++ apply filter_binding_lang;
                             [revert Be Bf T T';clear;repeat rewrite <- binding_finite_spec;simpl;
                              intros -> -> -> ->;reflexivity|];split.
                           *** exists (v1++v2),u2;rewrite app_ass;tauto.
                           *** simpl_binding in *.
                               rewrite prod_assoc,Eu1.
                               rewrite lower_squares_alt in Eu2 by reflexivity.
                               destruct (𝗙 b u2) as ((t&ff)&?);unfold square,d_binding in *;simpl in *.
                               destruct Eu2 as (->&h).
                               rewrite orb_false_r,negb_true_iff in h.
                               destruct h as [L|(->&->)].
                               ---- unfold prod_binding.
                                    destruct_ltb t K;[lia|].
                                    destruct_ltb K t;[|lia].
                                    simpl_nat;reflexivity.
                               ---- unfold prod_binding.
                                    destruct_ltb K K;[|lia];reflexivity.
                       +++ tauto.
                       +++ tauto.
                   --- apply is_binding_finite_filter_binding,Be.
                   --- rewrite filter_binding_support,support_prod;simpl_In;tauto.
                   --- rewrite filter_binding_support;tauto.
                   --- assumption.
                ** etransitivity.
                   --- apply proper_prod_inf;[|reflexivity].
                       etransitivity;[|apply (IH N M)].
                       rewrite <- inf_cup_left.
                       rewrite <- inf_cup_right.
                       apply Σ_bigger,in_map_iff;exists ((M,false,K),K▶);split;[reflexivity|].
                       assumption.
                   --- apply ka_star_right_ind.
                       etransitivity;[|apply (IH N M)].
                       rewrite <- inf_cup_left.
                       rewrite <- inf_cup_left.
                       reflexivity.
        * apply Σ_bounded;intros g Ig;apply in_map_iff in Ig as (((α,N'),(β,M'))&<-&I).
          repeat rewrite act_prod||rewrite act_join||rewrite semiring_left_distr
          ||rewrite semiring_right_distr.
          apply inf_join_inf.
          -- set (B := map (fun p => (fst(fst p),fst(snd p)))
                           ((fun p => snd (fst p) =?= N' && snd (snd p) =?= M')
                              :> (TriRange N M (sizeExpr e)))).
             set (e' := Σ(map (fun p => 𝔉 a (fst p) (𝔉 b (snd p) e)) B)).
             transitivity ((([(a,b);(b,c)]∙e'·[(a, b); (b, c)] ∙ BiLowerExpr a N' true b M' false f ⋆)
                              · TriSplitAct c a N' b M' f) · f ⋆).
             ++ repeat rewrite (mon_assoc _ _ _).
                repeat (apply proper_prod_inf;[|reflexivity]).
                apply αKA_inf_act,Σ_bigger,in_map_iff.
                exists (α,β);split;[reflexivity|].
                apply in_map_iff;exists ((α,N'),(β,M'));split;[reflexivity|].
                simpl_In;split;[assumption|].
                simpl_eqX;reflexivity.
             ++ clear α β I.
                transitivity (([(a,b);(b,c)]∙e'·TriSplitAct c a N' b M' f) · f ⋆).
                ** repeat (apply proper_prod_inf;[|reflexivity]).
                   rewrite <-act_star,<- act_prod.
                   apply αKA_inf_act,ka_star_right_ind.
                   unfold e';rewrite Σ_distr_r,map_map;apply Σ_bounded.
                   intros g Ig;apply in_map_iff in Ig as ((α,β)&<-&I);simpl.
                   unfold BiLowerExpr;rewrite Σ_distr_l,map_map;apply Σ_bounded.
                   intros g Ig;apply in_map_iff in Ig as ((α',β')&<-&I');simpl.
                   apply pairs_spec in I' as (Iα'&Iβ').
                   transitivity (𝔉 a (α⋅α') (𝔉 b (β⋅β') e)).
                   --- clear IH.
                       etransitivity;[|apply filter_binding_αKA_inf,filter_binding_αKA_inf,leq;
                                       [apply is_binding_finite_filter_binding|];assumption].
                       apply KA_αKA_inf,CompletenessKA_inf.
                       intros ? (u1&u2&->&I1&I2).
                       apply filter_binding_lang in I1 as (I1&Ea1);
                         [|apply is_binding_finite_filter_binding,Be].
                       apply filter_binding_lang in I1 as (I1&Eb1);
                         [|apply Be].
                       apply filter_binding_lang in I2 as (I2&Eb2);
                         [|apply is_binding_finite_filter_binding,Bf].
                       apply filter_binding_lang in I2 as (I2&Ea2);
                         [|apply Bf].
                       apply filter_binding_lang;
                         [apply is_binding_finite_filter_binding;
                          revert T T' Be Bf;clear;repeat rewrite <- binding_finite_spec;
                          simpl;intros -> -> -> ->;reflexivity|].
                       split;[apply filter_binding_lang;
                              [revert T T' Be Bf;clear;repeat rewrite <- binding_finite_spec;
                               simpl;intros -> -> -> ->;reflexivity|];split|].
                       +++ exists u1,u2;tauto.
                       +++ simpl_binding;rewrite Eb1,Eb2;reflexivity.
                       +++ simpl_binding;rewrite Ea1,Ea2;reflexivity.
                   --- non_zero (𝔉 a (α ⋅ α') (𝔉 b (β ⋅ β') e)).
                       apply Σ_bigger,in_map_iff;exists (α⋅α',β⋅β');split;[reflexivity|].
                       apply test0_false in T0 as (u&Iu).
                       apply filter_binding_lang in Iu as (Iu&Ea);
                         [|apply is_binding_finite_filter_binding,Be].
                       apply filter_binding_lang in Iu as (Iu&Eb);
                         [|apply Be].
                       apply (binding_finite_bound_size a Be) in Iu as Sa.
                       apply (binding_finite_bound_size b Be) in Iu as Sb.
                       rewrite Ea in Sa;rewrite Eb in Sb;clear u Iu Ea Eb.
                       revert Sa Sb Iα' Iβ' I;clear.
                       unfold B;intros.
                       apply in_map_iff in I as (((xa,ya),(xb,yb))&heq&I).
                       simpl in heq;inversion heq;clear heq;subst.
                       apply filter_In in I as (I&E).
                       apply andb_true_iff in E as (Ea&Eb).
                       rewrite eqX_correct in Ea,Eb;simpl in Ea,Eb;subst.
                       apply in_map_iff;exists ((α⋅α',N'),(β⋅β',M'));split;[reflexivity|].
                       apply filter_In;split;
                         [|apply andb_true_iff;split;apply eqX_correct;reflexivity].
                       unfold TriRange in I;apply pairs_spec in I as (Ia&Ib).
                       apply in_flat_map in Ib as ((x&((y&[])&[]))&Eb&heq);
                         try destruct heq as [heq|heq];inversion heq;simpl in *;
                           tauto||subst;clear heq.
                       apply factors_prod in Eb.
                       apply SplitRange_result in Ia as (Ea&Mina).
                       apply pairs_spec;split.
                       +++ apply SplitRange_In';[assumption| |].
                           *** rewrite <- prod_assoc.
                               rewrite lower_squares_prod_destr_true;tauto.
                           *** revert Iα' Ea Mina;clear;intros Iα' Ea Mina.
                               destruct α as ((D&ff)&C).
                               destruct α' as ((D'&ff')&C').
                               apply destr_bind_prod_full in Ea as (_&h).
                               apply lower_squares_alt in Iα' as (Ea'&h');[|reflexivity].
                               unfold square,d_binding in *;simpl in *;subst.
                               rewrite orb_true_r in h'.
                               assert (L: D'<=N') by lia;clear h'.
                               destruct h as [(L'&E)|E].
                               ---- unfold prod_binding at 1.
                                    intros (([]&?)&?);simpl.
                                    ++++ unfold prod_binding.
                                         destruct_ltb C D';[destruct_ltb D' C|];
                                           intro heq;inversion heq;clear heq;subst.
                                         **** lia.
                                         **** lia.
                                         **** lia.
                                    ++++ unfold prod_binding.
                                         destruct_ltb C D';[destruct_ltb D' C|];
                                           intro heq;inversion heq;clear heq;subst.
                                         **** lia.
                                         **** lia.
                                         **** lia.
                               ---- inversion E;subst.
                                    exfalso;apply (Mina (0,false,S N'));reflexivity.
                       +++ apply in_flat_map;exists (β⋅β',M'▶);split;[|now left].
                           apply factors_In;[assumption|].
                           rewrite <- prod_assoc,lower_squares_prod_destr_false,Eb;tauto.
                ** transitivity (TriSplitAct c a N b M e · f ⋆).
                   --- apply proper_prod_inf;[|reflexivity].
                       rewrite <- (IH N M),<-inf_cup_right.
                       unfold e';rewrite Σ_act,Σ_distr_r.
                       unfold act at 1,act_lists;repeat rewrite map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as ((α,β)&<-&I);simpl.
                       apply Σ_bigger,in_map_iff;exists ((α,N'),(β,M'));split;[reflexivity|].
                       unfold B in I.
                       apply in_map_iff in I as (((xa,ya),(xb,yb))&heq&I).
                       simpl in heq;inversion heq;clear heq;subst.
                       apply filter_In in I as (I&E).
                       apply andb_true_iff in E as (Ea&Eb).
                       rewrite eqX_correct in Ea,Eb;simpl in Ea,Eb;subst.
                       assumption.
                   --- apply ka_star_right_ind.
                       rewrite <- (IH N M) at 2.
                       rewrite <- inf_cup_left,<-inf_cup_left;reflexivity.
          -- repeat rewrite (mon_assoc _ _ _).
             set (B := map (fun p => (fst(fst p),fst(snd p)))
                           ((fun p => snd (fst p) =?= N' && snd (snd p) =?= M')
                              :> (TriRange N M (sizeExpr e)))).
             set (e' := Σ(map (fun p => 𝔉 a (fst p) (𝔉 b (snd p) e)) B)).
             transitivity (((((([(a,b);(b,c)]∙e'·[(a,b);(b,c)]∙BiLowerExpr a N' true b M' false f ⋆))
                                · [(b, c)] ∙ LowerExpr b M' false (splitActStrict c a N' f))
                               · [(b, c)] ∙ (LowerExpr b M' false f ⋆))
                              · splitAct c b (M', false, 0) f) ·  f ⋆).
             ++ repeat (apply proper_prod_inf;[|reflexivity]).
                apply αKA_inf_act,Σ_bigger,in_map_iff.
                exists (α,β);split;[reflexivity|].
                apply in_map_iff;exists ((α,N'),(β,M'));split;[reflexivity|].
                simpl_In;split;[assumption|].
                simpl_eqX;reflexivity.
             ++ clear α β I.
                transitivity ((((([(a,b);(b,c)]∙e')
                                   · [(b, c)] ∙ LowerExpr b M' false (splitActStrict c a N' f))
                                  · [(b, c)] ∙ (LowerExpr b M' false f ⋆))
                                 · splitAct c b (M', false, 0) f) ·  f ⋆).
                ** repeat (apply proper_prod_inf;[|reflexivity]).
                   rewrite <-act_star,<- act_prod.
                   apply αKA_inf_act,ka_star_right_ind.
                   unfold e';rewrite Σ_distr_r,map_map;apply Σ_bounded.
                   intros g Ig;apply in_map_iff in Ig as ((α,β)&<-&I);simpl.
                   unfold BiLowerExpr;rewrite Σ_distr_l,map_map;apply Σ_bounded.
                   intros g Ig;apply in_map_iff in Ig as ((α',β')&<-&I');simpl.
                   apply pairs_spec in I' as (Iα'&Iβ').
                   transitivity (𝔉 a (α⋅α') (𝔉 b (β⋅β') e)).
                   --- clear IH.
                       etransitivity;[|apply filter_binding_αKA_inf,filter_binding_αKA_inf,leq;
                                       [apply is_binding_finite_filter_binding|];assumption].
                       apply KA_αKA_inf,CompletenessKA_inf.
                       intros ? (u1&u2&->&I1&I2).
                       apply filter_binding_lang in I1 as (I1&Ea1);
                         [|apply is_binding_finite_filter_binding,Be].
                       apply filter_binding_lang in I1 as (I1&Eb1);
                         [|apply Be].
                       apply filter_binding_lang in I2 as (I2&Eb2);
                         [|apply is_binding_finite_filter_binding,Bf].
                       apply filter_binding_lang in I2 as (I2&Ea2);
                         [|apply Bf].
                       apply filter_binding_lang;
                         [apply is_binding_finite_filter_binding;
                          revert T T' Be Bf;clear;repeat rewrite <- binding_finite_spec;
                          simpl;intros -> -> -> ->;reflexivity|].
                       split;[apply filter_binding_lang;
                              [revert T T' Be Bf;clear;repeat rewrite <- binding_finite_spec;
                               simpl;intros -> -> -> ->;reflexivity|];split|].
                       +++ exists u1,u2;tauto.
                       +++ simpl_binding;rewrite Eb1,Eb2;reflexivity.
                       +++ simpl_binding;rewrite Ea1,Ea2;reflexivity.
                   --- non_zero (𝔉 a (α ⋅ α') (𝔉 b (β ⋅ β') e)).
                       apply Σ_bigger,in_map_iff;exists (α⋅α',β⋅β');split;[reflexivity|].
                       apply test0_false in T0 as (u&Iu).
                       apply filter_binding_lang in Iu as (Iu&Ea);
                         [|apply is_binding_finite_filter_binding,Be].
                       apply filter_binding_lang in Iu as (Iu&Eb);
                         [|apply Be].
                       apply (binding_finite_bound_size a Be) in Iu as Sa.
                       apply (binding_finite_bound_size b Be) in Iu as Sb.
                       rewrite Ea in Sa;rewrite Eb in Sb;clear u Iu Ea Eb.
                       revert Sa Sb Iα' Iβ' I;clear.
                       unfold B;intros.
                       apply in_map_iff in I as (((xa,ya),(xb,yb))&heq&I).
                       simpl in heq;inversion heq;clear heq;subst.
                       apply filter_In in I as (I&E).
                       apply andb_true_iff in E as (Ea&Eb).
                       rewrite eqX_correct in Ea,Eb;simpl in Ea,Eb;subst.
                       apply in_map_iff;exists ((α⋅α',N'),(β⋅β',M'));split;[reflexivity|].
                       apply filter_In;split;
                         [|apply andb_true_iff;split;apply eqX_correct;reflexivity].
                       unfold TriRange in I;apply pairs_spec in I as (Ia&Ib).
                       apply in_flat_map in Ib as ((x&((y&[])&[]))&Eb&heq);
                         try destruct heq as [heq|heq];inversion heq;simpl in *;
                           tauto||subst;clear heq.
                       apply factors_prod in Eb.
                       apply SplitRange_result in Ia as (Ea&Mina).
                       apply pairs_spec;split.
                       +++ apply SplitRange_In';[assumption| |].
                           *** rewrite <- prod_assoc.
                               rewrite lower_squares_prod_destr_true;tauto.
                           *** revert Iα' Ea Mina;clear;intros Iα' Ea Mina.
                               destruct α as ((D&ff)&C).
                               destruct α' as ((D'&ff')&C').
                               apply destr_bind_prod_full in Ea as (_&h).
                               apply lower_squares_alt in Iα' as (Ea'&h');[|reflexivity].
                               unfold square,d_binding in *;simpl in *;subst.
                               rewrite orb_true_r in h'.
                               assert (L: D'<=N') by lia;clear h'.
                               destruct h as [(L'&E)|E].
                               ---- unfold prod_binding at 1.
                                    intros (([]&?)&?);simpl.
                                    ++++ unfold prod_binding.
                                         destruct_ltb C D';[destruct_ltb D' C|];
                                           intro heq;inversion heq;clear heq;subst.
                                         **** lia.
                                         **** lia.
                                         **** lia.
                                    ++++ unfold prod_binding.
                                         destruct_ltb C D';[destruct_ltb D' C|];
                                           intro heq;inversion heq;clear heq;subst.
                                         **** lia.
                                         **** lia.
                                         **** lia.
                               ---- inversion E;subst.
                                    exfalso;apply (Mina (0,false,S N'));reflexivity.
                       +++ apply in_flat_map;exists (β⋅β',M'▶);split;[|now left].
                           apply factors_In;[assumption|].
                           rewrite <- prod_assoc,lower_squares_prod_destr_false,Eb;tauto.
                ** unfold e';rewrite Σ_act;unfold act at 1,act_lists.
                   repeat rewrite Σ_distr_r.
                   repeat rewrite map_map.
                   clear e'.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as ((α&β)&<-&I).
                   unfold B in I;clear B.
                   apply in_map_iff in I as (((xa,ya),(xb,yb))&heq&I).
                   simpl in heq;inversion heq;clear heq;subst.
                   apply filter_In in I as (I&E).
                   apply andb_true_iff in E as (Ea&Eb).
                   rewrite eqX_correct in Ea,Eb;simpl in Ea,Eb;subst;simpl.
                   set (B:= prj1 ((fun p => snd p =?= (M'▶)) :> factors (M▶) (sizeExpr e))).
                   transitivity (((Σ(map(fun β => [(b,c)]∙splitActStrict c a N (𝔉 b β e)) B)
                                    · [(b, c)] ∙ (LowerExpr b M' false f ⋆))
                                    · splitAct c b (M', false, 0) f) · f ⋆).
                   --- repeat (apply proper_prod_inf;[|reflexivity]).
                       unfold LowerExpr;rewrite Σ_act,Σ_distr_l.
                       unfold act at 2,act_lists;repeat rewrite map_map.
                       apply Σ_bounded;intros g Ig.
                       apply in_map_iff in Ig as (β'&<-&Iβ').
                       transitivity ([(b, c)] ∙ splitActStrict c a N (𝔉 b (β⋅β') e)).
                       +++ etransitivity;
                             [|apply αKA_inf_act,splitActStrict_αKA_inf,filter_binding_αKA_inf,leq].
                           *** apply KA_αKA_inf,CompletenessKA_inf;clear IH.
                               intros ? (u1&u'&->&Iu1&Iu).
                               rewrite act_lang in *.
                               apply filter_binding_lang in Iu1 as (Iu1&Ea1);
                                 [|apply is_binding_finite_filter_binding,Be].
                               apply filter_binding_lang in Iu1 as (Iu1&Eb1);
                                 [|apply Be].
                               apply filter_binding_lang in Iu as (Iu&Eb2);
                                 [|apply is_binding_finite_splitActStrict,Bf].
                               apply splitActStrict_lang in Iu as (u2&u3&EE&Iu&Ea2&Mina);[|assumption].
                               rewrite <-(act_bij [(b,c)]),act_p_pinv in EE.
                               replace u' with ([(b, c)] ∙ ([(a, c)] ∙ u2 ++ u3))
                                 in * by assumption;clear EE u'.
                               revert Eb1 Ea1 Eb2;repeat (rewrite 𝗙_perm;simpl_binding).
                               repeat rewrite action_compose.
                               unfold act at 1 2 3 4;simpl;simpl_eqX;intros.
                               apply splitActStrict_lang;
                                 [apply is_binding_finite_filter_binding;
                                  revert T T' Be Bf;clear;repeat rewrite <- binding_finite_spec;
                                  simpl;intros -> -> -> ->;reflexivity|].
                               exists ([(a,c)]∗∙([(b,c)]∙u1)++u2),u3;repeat split.
                               ---- repeat rewrite act_lists_app.
                                    replace ([(b,c)]∙u3) with ([(b,c)]∗∙u3) by reflexivity.
                                    replace ([(b,c)]∙([(a, c)] ∙ u2)) with ([(b,c)]∗∙([(a, c)] ∙ u2))
                                      by reflexivity.
                                    repeat rewrite act_p_pinv.
                                    rewrite app_ass;reflexivity.
                               ---- apply filter_binding_lang;
                                      [revert T T' Be Bf;clear;repeat rewrite <- binding_finite_spec;
                                       simpl;intros -> -> -> ->;reflexivity|].
                                    split.
                                    ++++ exists (([(a, b); (b, c)] ∗) ∙ u1),(u2++u3);repeat split.
                                         **** repeat rewrite app_ass.
                                              f_equal.
                                              rewrite action_compose;simpl.
                                              apply support_eq_action_eq.
                                              intros d Id;unfold act;simpl.
                                              destruct_eqX d b;simpl_eqX;try reflexivity.
                                              destruct_eqX d a;simpl_eqX;try reflexivity.
                                              destruct_eqX d c;simpl_eqX;try reflexivity.
                                         **** assumption.
                                         **** assumption.
                                    ++++ simpl_binding;repeat (rewrite 𝗙_perm;simpl_binding).
                                         unfold act;simpl;simpl_eqX.
                                         rewrite <-Eb1,<-Eb2.
                                         symmetry;apply prod_assoc.
                               ---- simpl_binding;repeat (rewrite 𝗙_perm;simpl_binding).
                                    unfold act;simpl;simpl_eqX.
                                    rewrite Ea1,Ea2.
                                    unfold TriRange in I.
                                    apply pairs_spec in I as (I1&I2).
                                    apply in_flat_map in I2 as ((?&((?,[]),[]))&I2&heq);
                                      try destruct heq as [heq|heq];inversion heq;clear heq;subst.
                                    apply SplitRange_result in I1 as (E1&Min).
                                    tauto.
                               ---- intros v w EE Len Ev.
                                    apply Levi in EE as (w'&[(EE&->)|(->&->)]).
                                    ++++ rewrite action_compose,<-(act_bij([(a,c);(b,c)]∗)),
                                         act_pinv_p in EE.
                                         rewrite EE in *;clear u1 EE.
                                         unfold TriRange in I.
                                         apply pairs_spec in I as (I1&I2).
                                         apply in_flat_map in I2 as ((?&((?,[]),[]))&I2&heq);
                                           try destruct heq as [heq|heq];inversion heq;clear heq;subst.
                                         apply SplitRange_result in I1 as (E1&Min).
                                         apply (Min (𝗙 b (([(a, c); (b, c)] ∗) ∙ w'))).
                                         simpl_binding;repeat (rewrite 𝗙_perm;simpl_binding).
                                         unfold act;simpl;simpl_eqX.
                                         rewrite Ev;reflexivity.
                                    ++++ apply (Mina w' w).
                                         **** reflexivity.
                                         **** solve_length.
                                         **** clear Len Mina.
                                              revert Ev Ea2.
                                              simpl_binding.
                                              simpl_binding;repeat (rewrite 𝗙_perm;simpl_binding).
                                              unfold act;simpl;simpl_eqX.
                                              repeat rewrite destr_bind_prod_full.
                                              destruct (𝗙 a w') as ((K&?)&?);unfold d_binding;simpl.
                                              intros (EE&h1).
                                              inversion EE;clear EE;subst.
                                              destruct (𝗙 a w) as ((K'&?)&?).
                                              intros (EE&h2).
                                              inversion EE;clear EE;subst.
                                              simpl in *.
                                              destruct h2 as [(L2&E)|h2];[|inversion h2;reflexivity].
                                              exfalso.
                                              destruct (𝗙 b u1) as ((D,ff),C);simpl in h1.
                                              unfold TriRange in I.
                                              apply pairs_spec in I as (I1&I2).
                                              apply in_flat_map in I2 as ((?&((?,[]),[]))&I2&heq);
                                                try destruct heq as [heq|heq];inversion heq;clear heq;subst.
                                              apply SplitRange_result in I1 as (E1&Min).
                                              apply destr_bind_prod_full in E1 as (_&E1).
                                              unfold d_binding in E1;simpl in E1.
                                              destruct E1 as [(L1&E1)|E1].
                                              ----- destruct h1 as [(L3&E3)|E3].
                                              +++++ lia.
                                              +++++ inversion E3;subst.
                                              lia.
                                              ----- inversion E1;subst.
                                              destruct h1 as [(L3&E3)|E3].
                                              +++++ lia.
                                              +++++ inversion E3;subst.
                                              lia.
                           *** apply is_binding_finite_filter_binding,Be.
                           *** rewrite filter_binding_support,support_prod;simpl_In;tauto.
                           *** rewrite filter_binding_support;simpl_In;tauto.
                           *** assumption.
                       +++ non_zero(𝔉 b (β ⋅ β') e);[apply splitActStrict_test0,T0|].
                           apply test0_false in T0 as (u&Iu).
                           apply filter_binding_lang in Iu as (Sb&Eu);[|assumption].
                           apply (binding_finite_bound_size b Be) in Sb;rewrite Eu in Sb;clear u Eu.
                           apply Σ_bigger,in_map_iff;exists (β⋅β');split;[reflexivity|].
                           apply in_map_iff;exists (β⋅β',M'▶);split;[reflexivity|].
                           apply filter_In;split;[|apply eqX_correct;reflexivity].
                           apply factors_In;[assumption|].
                           rewrite <- prod_assoc,lower_squares_prod_destr_false;[|assumption].
                           unfold TriRange in I.
                           apply pairs_spec in I as (I1&I2).
                           apply in_flat_map in I2 as ((?&((?,[]),[]))&I2&heq);
                             try destruct heq as [heq|heq];inversion heq;clear heq;subst.
                           eapply factors_prod,I2.
                   --- clear α β I; etransitivity.
                       +++ apply proper_prod_inf;[|reflexivity].
                           apply proper_prod_inf;[|reflexivity].
                           rewrite act_star;apply ka_star_right_ind.
                           replace (Σ (map (fun β0 => [(b, c)] ∙ splitActStrict c a N (𝔉 b β0 e)) B))
                             with ([(b, c)] ∙ Σ (map (fun β0 => splitActStrict c a N (𝔉 b β0 e)) B))
                             by (rewrite Σ_act;unfold act at 1,act_lists;rewrite map_map;reflexivity).
                           rewrite <- act_prod;apply αKA_inf_act.
                           transitivity (Σ (map (fun β0 => splitActStrict c a N (𝔉 b β0 (e·f))) B)).
                           *** rewrite Σ_distr_r,map_map;apply Σ_bounded;intros g Ig.
                               apply in_map_iff in Ig as (β&<-&Iβ).
                               unfold LowerExpr.
                               rewrite Σ_distr_l,map_map;apply Σ_bounded;intros g Ig.
                               apply in_map_iff in Ig as (β'&<-&Iβ').
                               assert (B' : is_binding_finite (e·f))
                                 by (revert Be Bf T T';clear;
                                     repeat rewrite <- binding_finite_spec;simpl;
                                     intros -> -> -> ->;reflexivity).
                               transitivity (splitActStrict c a N (𝔉 b (β⋅β') (e · f))).
                               ---- apply KA_αKA_inf,CompletenessKA_inf.
                                    intros ? (u&u3&->&I&I3).
                                    apply splitActStrict_lang in I as (u1&u2&->&Iu&Eu);
                                      [|apply is_binding_finite_filter_binding,Be].
                                    rewrite filter_binding_lang in Iu, I3 by assumption.
                                    rewrite app_ass.
                                    apply splitActStrict_lang;
                                      [apply is_binding_finite_filter_binding,B'|].
                                    exists u1,(u2++u3);split;[reflexivity|].
                                    split;[|assumption].
                                    apply filter_binding_lang;[assumption|].
                                    split.
                                    ++++ exists (u1++u2),u3;rewrite app_ass;tauto.
                                    ++++ simpl_binding in *.
                                         rewrite prod_assoc.
                                         destruct Iu as (_&->),I3 as (_&->).
                                         reflexivity.
                               ---- non_zero  (𝔉 b (β ⋅ β') e).
                                    ++++ rewrite splitActStrict_test0;[reflexivity|].
                                         apply not_false_is_true;intros Tf.
                                         apply test0_false in Tf as (u&Iu).
                                         apply filter_binding_lang in Iu as (Iu&Eu);
                                           [|assumption].
                                         apply αKA_lang_inf in leq.
                                         assert (Iu' : cl_α ⟦ e · f ⟧ u )
                                           by (exists u;split;[assumption|reflexivity]).
                                         apply leq in Iu' as (v&Iv&Ev).
                                         rewrite <- (αequiv_binding Ev) in Eu.
                                         cut (zero v);[tauto|].
                                         apply test0_spec,soundness in T0.
                                         apply T0,filter_binding_lang;[assumption|].
                                         tauto.
                                    ++++ apply test0_false in T0 as (u&Iu).
                                         apply filter_binding_lang in Iu as (Sb&Eu);
                                           [|assumption].
                                         apply (binding_finite_bound_size b Be) in Sb;
                                           rewrite Eu in Sb;clear u Eu.
                                         apply Σ_bigger,in_map_iff;exists (β⋅β');split;[reflexivity|].
                                         apply in_map_iff;exists (β⋅β',M'▶);split;[reflexivity|].
                                         simpl_In;split.
                                         **** apply factors_In;[assumption|].
                                              rewrite <- prod_assoc,lower_squares_prod_destr_false.
                                              ------ unfold B in Iβ.
                                              apply in_map_iff in Iβ as ((?&?)&heq&I).
                                              simpl in heq;subst.
                                              apply filter_In in I as (I&EE).
                                              simpl in EE;rewrite eqX_correct in EE;subst.
                                              apply factors_prod in I;tauto.
                                              ------ assumption.
                                         **** simpl_eqX;reflexivity.
                           *** apply Σ_bounded;intros g Ig.
                               apply in_map_iff in Ig as (β&<-&Iβ).
                               etransitivity;
                                 [apply splitActStrict_αKA_inf,filter_binding_αKA_inf,leq|].
                               ---- apply is_binding_finite_filter_binding,Be.
                               ---- rewrite filter_binding_support,support_prod;simpl_In;tauto.
                               ---- rewrite filter_binding_support;tauto.
                               ---- assumption.
                               ---- apply Σ_bigger,in_map_iff;exists β;tauto.
                       +++ repeat rewrite Σ_distr_r,map_map.
                           apply Σ_bounded;intros g Ig.
                           apply in_map_iff in Ig as (β&<-&Iβ).
                           etransitivity.
                           *** apply proper_prod_inf;[|reflexivity].
                               etransitivity;[|apply (IH N M)].
                               rewrite <- inf_cup_left,<-inf_cup_right.
                               apply Σ_bigger,in_map_iff;exists (β,M'▶).
                               split;[reflexivity|].
                               unfold B in Iβ;apply in_map_iff in Iβ as ((?&?)&heq&I).
                               simpl in heq;subst.
                               apply filter_In in I as (I&EE).
                               simpl in EE;rewrite eqX_correct in EE;subst.
                               assumption.
                           *** apply ka_star_right_ind.
                               rewrite <- (IH N M) at 2.
                               rewrite <- inf_cup_left,<-inf_cup_left;reflexivity.
  Qed.

  Lemma TriSplitAct_αKA_inf c a N b M e f :
    is_binding_finite f -> a<>b -> a<>c -> b<>c -> c # e -> c # f ->
    e <=α f -> TriSplitAct c a N b M e <=α TriSplitAct c a N b M f.
  Proof.
    intros Bf N1 N2 N3 Fe Ff L.
    assert (F' : c # e∪f) by (rewrite support_join;simpl_In;tauto).
    apply (TriSplitAct_αKA N M Bf N1 N2 N3) in L;assumption.
  Qed.

    
End s.
  


  