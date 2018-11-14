Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp alpha_regexp.

Section s.
  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.
  
  (** * Closed languages *)
  Definition α_closed : (@language letter) -> Prop := fun L => forall u v, u ≡ v -> L u <-> L v.
 
  Definition cl_α : language -> language := fun L w => exists u, L u /\ u ≡ w.

  Lemma cl_α_closed L : α_closed (cl_α L).
  Proof.
    intros u v e;split;intros (w&h&e');exists w;(split;[apply h|]).
    - rewrite e',e;reflexivity.
    - rewrite e',e;reflexivity.
  Qed.
  
  Lemma cl_α_idem l : cl_α (cl_α l) ≃ cl_α l.
  Proof.
    intro w;split.
    - intros (u&(v&h&e1)&e2).
      exists v;split.
      + assumption.
      + rewrite e1,e2;reflexivity.
    - intros (u&h&e);exists u;split.
      + exists u;split.
        * assumption.
        * reflexivity.
      + assumption.
  Qed.

  Lemma cl_α_incr l : l ≲ cl_α l.
  Proof.
    intros w h;exists w;split.
    - assumption.
    - reflexivity.
  Qed.
  
  Lemma cl_α_closed_idem L : α_closed L -> cl_α L ≃ L.
  Proof.
    intro A;apply inf_lang_PartialOrder;split;[|apply cl_α_incr].
    intros w (u&h&e).
    apply (A _ _ e),h.
  Qed.
    
  Global Instance inf_lang_cl_α : Proper (ssmaller ==> ssmaller) cl_α.
  Proof.
    intros l1 l2 e w (u&h&eu).
    exists u;split.
    - apply e,h.
    - assumption.
  Qed.

  Lemma minimal_cl_α L M : L ≲ M -> α_closed M -> cl_α L ≲ M.
  Proof. intros l A;rewrite <- (cl_α_closed_idem A);apply inf_lang_cl_α,l. Qed.

  Lemma cl_α_inf L M : cl_α L ≲ cl_α M <-> L ≲ cl_α M.
  Proof.
    split.
    - intros l;rewrite cl_α_incr;apply l.
    - intros l w (u&h&e).
      apply l in h as (v&h&e').
      exists v;split.
      + apply h.
      + rewrite e',e;reflexivity.
  Qed.
      
  Lemma cl_α_join L M : cl_α (L∪M) ≃ cl_α L ∪ cl_α M.
  Proof. intro w;unfold cl_α,join,joinLang;firstorder. Qed.

  Lemma cl_α_nil L : L [] <-> cl_α L [].
  Proof.
    split;intro I.
    + apply cl_α_incr,I.
    + destruct I as ([|l u]&I&E).
      * assumption.
      * apply αequiv_length in E;simpl in E;discriminate.
  Qed.

  Global Instance cl_α_eq_lang : Proper (sequiv ==> sequiv) cl_α.
  Proof. intros l m E u;unfold cl_α;setoid_rewrite (E _);tauto. Qed.

  Global Instance cl_α_inf_lang : Proper (ssmaller ==> ssmaller) cl_α.
  Proof. intros l m E u (v&I&E');apply E in I;exists v;tauto. Qed.

  Global Instance cl_α_αeq l : Proper (equiv ==> iff) (cl_α l).
  Proof. intros u v E;split;intros (w&I&Ew);exists w;split;assumption||rewrite Ew,E;reflexivity. Qed.

  Lemma cl_α_prod l m: cl_α (l · m) ≃ cl_α (cl_α l · cl_α m).
  Proof.
    apply inf_lang_PartialOrder;split;[|unfold Basics.flip].
    - apply cl_α_inf_lang,proper_prod_inf;apply cl_α_incr.
    - intros u (w&(u1&u2&->&(v1&I1&E1)&v2&I2&E2)&E).
      exists (v1++v2);split.
      + exists v1,v2;tauto.
      + rewrite E1,E2,E;reflexivity.
  Qed.

  Lemma cl_α_star l: cl_α (l⋆) ≃ cl_α ((cl_α l)⋆).
  Proof.
    apply inf_lang_PartialOrder;split;[|unfold Basics.flip].
    - apply cl_α_inf_lang,proper_star_inf;apply cl_α_incr.
    - intros u (w&(n&I)&E);rewrite <- E;clear E u; revert w I;induction n;simpl;intros w.
      + intros ->; exists [];simpl;split;[exists 0|];reflexivity.
      + intros (u1&u2&->&(u1'&I1&E1)&I2).
        apply IHn in I2 as (u2'&(n'&I2)&E2).
        exists (u1'++u2');split.
        * exists (S n'),u1',u2';tauto.
        * rewrite E1,E2;reflexivity.
  Qed.

  Definition restrict L A : (@language letter) := fun u => L u /\ ⌊u⌋ ⊆ A.

  Infix " ⇂ " := restrict (at level 20).

  Global Instance restrict_eqLists : Proper (sequiv ==> (@equivalent _) ==> sequiv) restrict.
  Proof.
    intros L M E2 A B E1 u;split;intros (Iu&Is);split;try apply E2,Iu.
    - rewrite <- E1;apply Is.
    - rewrite E1;apply Is.
  Qed.
  Global Instance restrict_inclLists : Proper (ssmaller ==> (@incl _) ==> ssmaller) restrict.
  Proof.
    intros L M E2 A B E1 u;intros (Iu&Is);split.
    - apply E2,Iu.
    - rewrite <- E1;apply Is.
  Qed.
  
  Proposition restrict_inf e f :
    cl_α ⟦e⟧ ≲ cl_α ⟦f⟧ <-> ⟦e⟧ ≲ (cl_α ⟦f⟧) ⇂ (⌊e⌋++⌊f⌋) .
  Proof.
    split.
    - intros h u I.
      split.
      + apply h;exists u;split.
        * assumption.
        * reflexivity.
      + rewrite (support_lang I);apply incl_appl;reflexivity.
    - intros I;apply cl_α_inf;intros u Ie.
      apply (I _ Ie).
  Qed.
      
  Proposition restrict_inf_bis e f :
    cl_α ⟦e⟧ ≲ cl_α ⟦f⟧ <-> (cl_α ⟦e⟧)⇂(⌊e⌋++⌊f⌋) ≲ (cl_α ⟦f⟧) ⇂ (⌊e⌋++⌊f⌋).
  Proof.
    rewrite restrict_inf;split;intros I u Iu;split.
    - destruct Iu as ((v&Iv&E)&R).
      apply I in Iv as ((w&Iw&Ew)&Rv).
      exists w;split.
      + assumption.
      + etransitivity;eauto.
    - apply Iu.
    - assert (Iu': (cl_α ⟦ e ⟧⇂(⌊ e ⌋ ++ ⌊ f ⌋)) u).
      + split.
        * exists u;split;[assumption|reflexivity].
        * rewrite (support_lang Iu);apply incl_appl;reflexivity.
      + apply (I _ Iu').
    - rewrite (support_lang Iu);apply incl_appl;reflexivity.
  Qed.

  Corollary restrict_eq e f : 
    cl_α ⟦e⟧ ≃ cl_α ⟦f⟧ <-> (cl_α ⟦e⟧)⇂(⌊e⌋++⌊f⌋) ≃ (cl_α ⟦f⟧) ⇂ (⌊e⌋++⌊f⌋).
  Proof.
    split;intro E;apply inf_lang_PartialOrder;unfold Basics.flip;split.
    - rewrite <- restrict_inf_bis,E;reflexivity.
    - rewrite app_comm,<-restrict_inf_bis,E;reflexivity.
    - rewrite restrict_inf_bis,E;reflexivity.
    - rewrite restrict_inf_bis,app_comm,E;reflexivity.
  Qed.

End s.