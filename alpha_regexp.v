Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export tools algebra language regexp words positive_regexp.


Section s.
  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.
  (** * Nominal structure *)
  Global Instance actReg : Action 𝐀 (@regexp letter) :=
    fix act p e {struct e} :=
      match e with
      | ⟪x⟫ => ⟪p∙x⟫
      | e_un => e_un
      | e_zero => e_zero
      | e_add e f => e_add (act p e) (act p f)
      | e_prod e f => e_prod (act p e) (act p f)
      | e_star e => e_star (act p e)
      end.
  
  Global Instance supReg : Support 𝐀 (@regexp letter) :=
    fix sup e {struct e} :=
      match e with
      | ⟪x⟫ => ⌊x⌋
      | e_un => []
      | e_zero => []
      | e_add e f => sup e ++ sup f
      | e_prod e f => sup e ++ sup f
      | e_star e => sup e
      end.
  
  Global Instance nominalReg : Nominal 𝐀 (@regexp letter).
  Proof.
    split.
    - intros e π; unfold act,act_lists at 1 ;rewrite map_eq_id;unfold support.
      induction e;simpl;simpl.
      + reflexivity.
      + reflexivity.
      + intros h;f_equal.
        * apply IHe1;intros a I;apply h.
          simpl_In;tauto.
        * apply IHe2;intros a I;apply h.
          simpl_In;tauto.
      + intros h;f_equal.
        * apply IHe1;intros a I;apply h.
          simpl_In;tauto.
        * apply IHe2;intros a I;apply h.
          simpl_In;tauto.
      + intros h;f_equal.
        apply IHe;intros a I;apply h,I.
      + intro h;f_equal;apply action_invariant,map_eq_id,h.
    - intros e π;unfold support;simpl.
      induction e;simpl;try rewrite act_lists_app||rewrite support_action;try reflexivity.
      + rewrite IHe1,IHe2;reflexivity.
      + rewrite IHe1,IHe2;reflexivity.
      + rewrite IHe;reflexivity.
    - intros e π1 π2;unfold act;induction e;simpl;try reflexivity||congruence.
      f_equal;apply action_compose.
  Qed.

  (** * Facts about the support *)
  Lemma support_lang e u : ⟦e⟧ u -> ⌊u⌋ ⊆ ⌊e⌋.
  Proof.
    revert u;induction e as [| |e IHe f IHf|e IHe f IHf|e|x].
    - intros ? F;simpl;exfalso;apply F.
    - intros ? ->;apply incl_nil.
    - intros u [Ie|If].
      + rewrite (IHe _ Ie).
        apply incl_appl;reflexivity.
      + rewrite (IHf _ If).
        apply incl_appr;reflexivity.
    - intros w (u&v&->&Ie&If).
      rewrite support_list_app,(IHe _ Ie),(IHf _ If).
      reflexivity.
    - intros w (n&In);revert w In;induction n;intros w;simpl.
      + intros ->;apply incl_nil.
      + intros (u&v&->&Ie&In).
        rewrite support_list_app,(IHe _ Ie),(IHn _ In);simpl.
        apply incl_app;reflexivity.
    - intros u ->;unfold support,SupportList;simpl.
      rewrite undup_equivalent,app_nil_r;reflexivity.
  Qed.
  
  Lemma Σ_support L : ⌊L⌋ ≈ ⌊Σ L⌋.
  Proof.
    induction L as [|e L];simpl.
    - reflexivity.
    - rewrite support_list_cons,IHL.
      reflexivity.
  Qed.
  
  Lemma prefixes_support e : ⌊prefixes e⌋ ⊆ ⌊e⌋.
  Proof.
    induction e;simpl.
    - reflexivity.
    - reflexivity.
    - rewrite support_list_app,IHe1,IHe2;reflexivity.
    - case_eq (test0 e1 || test0 e2).
      + intros;apply incl_nil.
      + intros F;rewrite support_list_app,IHe1.
        apply incl_app.
        * apply incl_appl;reflexivity.
        * intros a Ia.
          apply In_support_list in Ia as (f&If&Ia).
          apply in_map_iff in If as (g&<-&Ig).
          apply in_app_iff in Ia as [Ia|Ia].
          -- apply in_app_iff;left;apply Ia.
          -- apply in_app_iff;right;apply IHe2,In_support_list;exists g;tauto.
    - case_eq (test0 e).
      + intros;apply incl_nil.
      + intros F a Ia.
        apply In_support_list in Ia as (f&If&Ia).
        apply in_map_iff in If as (g&<-&Ig).
        apply in_app_iff in Ia as [Ia|Ia].
        * apply Ia.
        * apply IHe,In_support_list;exists g;tauto.
    - unfold support,SupportList at 1;simpl.
      rewrite app_nil_r,undup_equivalent;reflexivity.
  Qed.

  Lemma fresh_lang e a u : a # e -> ⟦e⟧ u -> a # u.
  Proof. intros F Iu Ia;apply F,(support_lang Iu),Ia. Qed. 

  Lemma support_join e f : ⌊e∪f⌋ = ⌊e⌋++⌊f⌋.
  Proof. reflexivity. Qed.

  Lemma support_prod e f : ⌊e·f⌋ = ⌊e⌋++⌊f⌋.
  Proof. reflexivity. Qed.

  Lemma support_star e : ⌊e⋆⌋ = ⌊e⌋.
  Proof. reflexivity. Qed.

  Lemma support_Var e : ⌊e⌋ ≈ ⌊Var e⌋.
  Proof.
    induction e;simpl;try reflexivity.
    - replace e_add with join by reflexivity.
      rewrite support_join,support_list_app,IHe1,IHe2;reflexivity.
    - replace e_prod with prod by reflexivity.
      rewrite support_prod,support_list_app,IHe1,IHe2;reflexivity.
    - rewrite <- IHe;reflexivity.
    - unfold support,SupportList;simpl.
      rewrite app_nil_r,undup_equivalent;reflexivity.
  Qed.

  Lemma support_ϵ e : ⌊ϵ e⌋ = [].
  Proof. destruct (ϵ_zero_or_un e) as [-> | ->];reflexivity. Qed.

  (** * Facts about the group action *)
  Lemma act_lang e p u : ⟦p∙e⟧ u <-> ⟦e⟧ (p∗∙u).
  Proof.
    cut (forall e p u, ⟦p∙e⟧ u -> ⟦e⟧ (p∗∙u)).
    - intros hyp;split;[apply hyp|].
      rewrite <- (act_pinv_p (p∗) u) at 2.
      intros I;apply hyp;rewrite act_pinv_p;assumption.
    - clear;intros e p;induction e;intros u;simpl.
      + tauto.
      + intros ->;reflexivity.
      + intros [I|I].
        * apply IHe1 in I;left;tauto.
        * apply IHe2 in I;right;tauto.
      + intros (u1&u2&->&I1&I2).
        apply IHe1 in I1;apply IHe2 in I2.
        exists (p ∗∙u1),(p ∗∙ u2).
        rewrite act_lists_app;tauto.
      + intros (n&I);exists n;revert u I;induction n;simpl;intros.
        * rewrite I;reflexivity.
        * destruct I as (u1&u2&->&Iu&Iv).
          apply IHe in Iu.
          apply IHn in Iv.
          exists (p ∗∙u1),(p ∗∙ u2);rewrite act_lists_app;tauto.
      + intros ->;unfold act at 1;simpl.
        rewrite act_pinv_p;reflexivity.
  Qed.

    Lemma ϵ_act p e : ϵ (p∙e) = ϵ e.
  Proof.
    induction e;simpl;try reflexivity.
    - unfold act in *;rewrite IHe1,IHe2;reflexivity.
    - unfold act in *;rewrite IHe1,IHe2;reflexivity.
  Qed.

  Lemma δ_act p l e : δ l (p∙e) = p∙ δ (p∗∙l) e.
  Proof.
    induction e;simpl;try reflexivity;replace actReg with act by reflexivity.
    - rewrite IHe1,IHe2;reflexivity.
    - rewrite ϵ_act;rewrite IHe1,IHe2.
      unfold_eqX;reflexivity.
    - rewrite IHe;reflexivity.
    - replace eq_letter with (@tools.eqX _ dec_letter) by reflexivity.
      unfold_eqX;reflexivity||(exfalso;apply N;subst).
      + apply act_pinv_p.
      + symmetry;apply act_p_pinv.
  Qed.

  Lemma test0_act p e : test0 (p∙e) = test0 e.
  Proof.
    induction e;simpl;try reflexivity.
    - rewrite <-IHe1, <-IHe2;reflexivity.
    - rewrite <-IHe1, <-IHe2;reflexivity.
  Qed.

  Lemma sizeExpr_act p e : sizeExpr (p∙e) = sizeExpr e.
  Proof. unfold act;induction e;simpl; lia. Qed.

  Lemma Σ_act p L : p ∙ Σ L = Σ (p∙L).
  Proof. induction L;simpl;[|unfold act in *;rewrite <- IHL];reflexivity. Qed.

  Lemma positive_act p e : positive (p∙e) = p ∙ (positive e).
  Proof.
    induction e;simpl;replace actReg with act by reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite IHe1,IHe2;reflexivity.
    - rewrite IHe1,IHe2;reflexivity.
    - rewrite IHe;reflexivity.
    - reflexivity.
  Qed.
  
  Lemma KA_act p e f : e =KA f -> p ∙ e =KA p ∙ f.
  Proof.
    intro eq;induction eq.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - unfold act;simpl;replace actReg with act by reflexivity;rewrite IHeq1,IHeq2;reflexivity.
    - unfold act;simpl;replace actReg with act by reflexivity;rewrite IHeq1,IHeq2;reflexivity.
    - unfold act;simpl;replace actReg with act by reflexivity;rewrite IHeq;reflexivity.
    - destruct H;unfold act;simpl;replace actReg with act by reflexivity;apply ax_eq_ax.
      + apply KA_prod_assoc.
      + apply KA_add_assoc.
      + apply KA_add_comm.
      + apply KA_left_distr.
      + apply KA_right_distr.
      + apply KA_zero.
      + apply KA_un_left.
      + apply KA_un_right.
      + apply KA_left_zero.
      + apply KA_right_zero.
      + apply KA_idem.
      + apply KA_star_unfold.
    - destruct H as [e f|e f];unfold act;simpl;replace actReg with act by reflexivity;
        (eapply ax_eq_ax';[|apply IHeq]).
      + apply KA_star_left_ind.
      + apply KA_star_right_ind.
  Qed.
    
  (** * Splitting the size by name *)
  Fixpoint sizeAt e (a : atom) :=
    match e with
    | e_un | e_zero | ⟪var _⟫ => 0
    | ⟪open b⟫ | ⟪close b⟫ => if a=?=b then 1 else 0
    | e_add e f | e_prod e f => sizeAt e a + sizeAt f a
    | e_star e => sizeAt e a
    end.

  Lemma sizeAt_fresh e a : a # e -> sizeAt e a = 0.
  Proof.
    induction e;simpl;try reflexivity.
    - intros I;rewrite IHe1,IHe2.
      + reflexivity.
      + intros I';apply I,in_app_iff;now right.
      + intros I';apply I,in_app_iff;now left.
    - intros I;rewrite IHe1,IHe2.
      + reflexivity.
      + intros I';apply I,in_app_iff;now right.
      + intros I';apply I,in_app_iff;now left.
    - apply IHe.
    - destruct x;simpl;unfold_eqX;tauto.
  Qed.
  
  Lemma size_sizeAt e : sum (sizeAt e) {{⌊e⌋}} <= sizeExpr e.
  Proof.
    induction e;simpl;try reflexivity.
    - rewrite <- sum_add_distr;apply Plus.plus_le_compat.
      + rewrite <- IHe1;apply PeanoNat.Nat.eq_le_incl.
        symmetry;apply (sum_incr_0_right ⌊e1⌋).
        apply sizeAt_fresh.
      + rewrite <- IHe2;apply PeanoNat.Nat.eq_le_incl.
        symmetry;apply (sum_incr_0_left ⌊e2⌋).
        apply sizeAt_fresh.
    - rewrite <- sum_add_distr;apply Plus.plus_le_compat.
      + rewrite <- IHe1;apply PeanoNat.Nat.eq_le_incl.
        symmetry;apply (sum_incr_0_right ⌊e1⌋).
        apply sizeAt_fresh.
      + rewrite <- IHe2;apply PeanoNat.Nat.eq_le_incl.
        symmetry;apply (sum_incr_0_left ⌊e2⌋).
        apply sizeAt_fresh. 
    - apply IHe.
    - destruct x;simpl;simpl_eqX.
      + reflexivity.
      + reflexivity.
      + rewrite sum_zero_in;[lia|intros;reflexivity].
  Qed.

  
End s.






