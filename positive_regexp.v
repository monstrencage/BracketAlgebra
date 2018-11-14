Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp systems.

Section s.
  Context {X : Set}.
  Context {decX : decidable_set X}.
  
  Notation Regexp := (@regexp X).
  
  Fixpoint positive e : Regexp :=
    match e with
    | e_zero | e_un => zero
    | ⟪x⟫ => ⟪x⟫
    | e_add e f => positive e ∪ positive f
    | e_prod e f => positive e · f ∪ e · positive f
    | e_star e => positive e · e ⋆
    end.


  Lemma positive_lang e u : ⟦positive e⟧ u <-> ⟦e⟧ u /\ u <> [].
  Proof.
    revert u;cut (⟦positive e⟧ ≃ (fun u => ⟦e⟧ u /\ u <> []));[intros h u;rewrite (h u);tauto|].
    induction e;simpl.
    - intro u;simpl;tauto.
    - intro u;split;[intro I;exfalso;apply I|intros (->&I);apply I;reflexivity].
    - rewrite IHe1,IHe2;intro u;unfold join,joinLang;tauto.
    - rewrite IHe1,IHe2;clear IHe1 IHe2.
      intro u;split.
      + intros [Iu|Iu].
        * destruct Iu as (u1&u2&->&(I1&N)&I2).
          split;[exists u1,u2;tauto|].
          intro E;apply N;apply app_eq_nil in E;tauto.
        * destruct Iu as (u1&u2&->&I1&I2&N).
          split;[exists u1,u2;tauto|].
          intro E;apply N;apply app_eq_nil in E;tauto.
      + intros ((u1&u2&->&I1&I2)&N).
        destruct_eqX u1 (@nil X);subst.
        * simpl in N;right;exists [],u2;tauto.
        * left;exists u1,u2;tauto.
    - rewrite IHe;clear IHe;intro u;split.
      + intros (u1&u2&->&(I1&N)&n&I2);split.
        * exists (S n),u1,u2;tauto.
        * intro E;apply N;apply app_eq_nil in E;tauto.
      + intros ((n&In)&N);revert u In N;induction n.
        * intros ? -> F;exfalso;apply F;reflexivity.
        * intros u (u1&u2&->&I1&IH) N.
          destruct_eqX u1 (@nil X);subst.
          -- simpl in *;apply IHn;assumption.
          -- exists u1,u2;split;[reflexivity|split;[tauto|]].
             exists n;assumption.
    - intro u;split.
      + intros ->;split;[reflexivity|intro E;discriminate].
      + tauto.
  Qed.
        
  Lemma positive_KA e f : e=KA f -> positive e =KA positive f.
  Proof.
    repeat rewrite CompletenessKA.
    intros E u;repeat rewrite positive_lang.
    rewrite (E u);reflexivity.
  Qed.

  Lemma positive_KA_inf e f : e<=KA f -> positive e <=KA positive f.
  Proof. unfold ax_inf;apply positive_KA. Qed.

  Lemma positive_inf e : positive e <=KA e.
  Proof. apply CompletenessKA_inf;simpl;intro u;rewrite positive_lang;tauto. Qed.
    
  Lemma positive_star e : positive e ⋆ =KA e ⋆.
  Proof.
    apply ax_inf_PartialOrder;unfold Basics.flip;split.
    - apply proper_star_inf,positive_inf.
    - apply CompletenessKA_inf;intros u (n&In).
      revert u In;induction n;intro u.
      + intros -> ;exists 0;reflexivity.
      + intros (u1&u2&->&I1&I2).
        destruct_eqX u1 (@nil X);subst.
        * simpl;apply IHn;assumption.
        * apply IHn in I2 as (m&Im).
          exists (S m),u1,u2;rewrite positive_lang;tauto.
  Qed.

End s.
