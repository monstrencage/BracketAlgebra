(** * RIS.language : Languages. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra.

Section lang.
  Context {A : Set}.
  (** * Definitions *)
  (** A language is a set of words, i.e. a predicate over lists. *)
  Definition language := list A -> Prop.
  (** Two languages are equivalent if they agree on every word. *)
  Global Instance eq_lang : SemEquiv language := fun l1 l2 => forall w, l1 w <-> l2 w.
  (** Languages may be ordered by containment. *)
  Global Instance inf_lang : SemSmaller language := fun l1 l2 => forall w, l1 w -> l2 w.

  Global Instance eq_lang_equiv : Equivalence (@sequiv _ eq_lang).
  Proof. split;intro;unfold sequiv,eq_lang;firstorder. Qed.
  Global Instance inf_lang_preorder : PreOrder (@ssmaller _ inf_lang).
  Proof. split;intro;unfold ssmaller,inf_lang;firstorder. Qed.
  Global Instance inf_lang_PartialOrder : PartialOrder sequiv (@ssmaller _ inf_lang).
  Proof.
    split.
    - intro e;split;intro w;rewrite (e w);tauto.
    - intros (h1&h2) w;split.
      + apply h1.
      + apply h2.
  Qed.

  (** The unit language only contains the empty word. *)
  Global Instance unLang : Un language := (fun w => w=[]).
  (** The empty language has no elements. *)
  Global Instance zeroLang : Zero language := fun _ : list A => False.
  (** From any two languages we may define their union and their concatenation. *)
  Global Instance joinLang : Join language:= fun l1 l2 w => l1 w \/ l2 w.
  Global Instance prodLang : Product language := fun l1 l2 w => exists u v, w = u++v /\ l1 u /\ l2 v.

  (** We may iterate the product on a language for any number of times. *)
  Reserved Notation " l ^{ n } " (at level 35).
  Fixpoint iter_lang n l : language :=
    match n with
    | 0 => 𝟭
    | S n => l · (l ^{n})
    end
  where "l ^{ n }" := (iter_lang n l).

  (** The Kleene star of a language is the union of its iterates. *)
  Global Instance starLang : Star language := fun l w => exists n, l^{n} w.

  (** * Compatibily of the operations with the ordering *)
  (** Applying any of the operations we have defined to equivalent
  arguments yields equivalent results. *)
  Global Instance proper_joinLang : Proper (sequiv ==> sequiv ==> sequiv) join.
  Proof. intros l m I l' m' I' w;unfold join,joinLang;rewrite (I w),(I' w);reflexivity. Qed.

  Global Instance proper_prodLang : Proper (sequiv ==> sequiv ==> sequiv) prod.
  Proof.
    intros l m I l' m' I' w;unfold prod,prodLang.
    setoid_rewrite (I _);setoid_rewrite (I' _);reflexivity. 
  Qed.
      
  Global Instance inf_lang_iter_lang n :
    Proper (sequiv ==> sequiv) (iter_lang n).
  Proof.
    intros l1 l2 e;induction n.
    - reflexivity.
    - simpl;rewrite IHn,e;reflexivity.
  Qed.

  Global Instance proper_starLang : Proper (sequiv ==> sequiv) star.
  Proof.
    intros l1 l2 e w;split;intros (n&In);exists n;apply (inf_lang_iter_lang n e),In.
  Qed.

  (** * Algebraic properties *)
  (** The containment order is the natural order stemming from [∪]. *)
  Lemma joinOrderLang : relation_equivalence (leqA sequiv) ssmaller.
  Proof.
    unfold leqA;intros L M;split;intros I w.
    - rewrite (I w);intro;now left.
    - split.
      + intro h;right;apply h.
      + intros [h|h];[apply I|];apply h.
  Qed.

  (** The set of languages is a semi-ring. *)
  Global Instance lang_Semiring : SemiRing language sequiv prod join un zero.
  Proof.
    split.
    - split.
      + typeclasses eauto.
      + intros l1 l2 l3 w';split.
        * intros (u&v1&->&h1&(v&w&->&h2)).
          exists (u++v),w;rewrite app_ass;split;[|split].
          -- reflexivity.
          -- exists u,v;tauto.
          -- tauto.
        * intros (u1&w&->&(u&v&->&h1&h2)&h3).
          exists u,(v++w);rewrite app_ass;split;[|split].
          -- reflexivity.
          -- tauto.
          -- exists v,w;tauto.
      + split;intros L w;(split;[intros (u&v&->&h1&h2)|intro h]).
        * rewrite h1;simpl;tauto.
        * exists [],w;simpl;split;[|split];tauto||reflexivity.
        * rewrite h2,app_nil_r;assumption.
        * exists w,[];rewrite app_nil_r;split;[|split];tauto||reflexivity.
    - split;simpl.
      + typeclasses eauto.
      + intros l1 l2 l3;firstorder.
      + split;intros l w;firstorder.
    - intros l1 l2 w;firstorder.
    - split;intros l w;firstorder.
    - intros l1 l2 l3 w;split.
      + intros (u&v&->&h1&[h2|h2]);[left|right];exists u,v;tauto.
      + intros [h|h];destruct h as (u&v&->&h1&h2);exists u,v;firstorder.
    - intros l1 l2 l3;split.
      + intros (u&v&->&[h1|h1]&h2);[left|right];exists u,v;tauto.
      + intros [h|h];destruct h as (u&v&->&h1&h2);exists u,v;firstorder.
  Qed.
  
  Remark iter_lang_last n l : l^{S n} ≃ l^{n} · l.
  Proof.
    induction n;simpl.
    - rewrite right_unit,left_unit;reflexivity.
    - rewrite IHn at 1.
      rewrite (mon_assoc l _ l);reflexivity.
  Qed.

  (** It is actually a Kleene algebra. *)
  Global Instance lang_KA : KleeneAlgebra language sequiv.
  Proof.
    split.
    - apply proper_starLang.
    - apply lang_Semiring.
    - intros l w;firstorder.
    - intros L;apply joinOrderLang.
      intros w [->|(u&v&->&h1&(n&h2))].
      + exists 0;reflexivity.
      + exists (S n),u,v;tauto.
    - intros l1 l2 L.
      apply joinOrderLang;apply joinOrderLang in L.
      intros w (u&v&->&(n&h1)&h2).
      revert u v h1 h2;induction n;intros.
      + rewrite h1;simpl;assumption.
      + destruct h1 as (u1&u2&->&h1&h1').
        rewrite app_ass.
        apply L.
        exists u1,(u2++v);firstorder.
    - intros l1 l2 L.
      apply joinOrderLang;apply joinOrderLang in L.
      intros w (u&v&->&h1&(n&h2)).
      revert u v h1 h2;induction n;intros.
      + rewrite h2,app_nil_r;assumption.
      + rewrite (iter_lang_last n _ v) in h2.
        destruct h2 as (v1&v2&->&h2&h2').
        rewrite <- app_ass.
        apply L.
        exists (u++v1),v2;firstorder.
  Qed.

  (* begin hide *)
  Global Instance join_semilattice_Lang : Semilattice language sequiv join := join_semilattice.
  (* end hide *)
End lang.
