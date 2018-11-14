Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools.

Section subword.
  Context {A : Set}.
  
  Reserved Notation " u ⊑ v " (at level 80).

  Fixpoint subword (u v : list A) :=
    match u with
    | [] => True
    | a::u => match v with
             | [] => False
             | b::v => (a = b /\ u ⊑ v) \/ (a::u ⊑ v) 
             end
    end
  where " u ⊑ v " := (subword u v).

  Global Instance subword_cons_Proper a :
    Proper (subword ==> subword) (cons a).
  Proof. intros u v S;simpl;tauto. Qed.

  Global Instance subword_PreOrder : PreOrder subword.
  Proof.
    split.
    - intro u;induction u;simpl;tauto.
    - intros u v w s1 s2;revert v u s2 s1.
      induction w as [|c w];intros [|b v] [|a u] s1 s2;simpl in *;try tauto.
      destruct s1 as [(->&s1)|s1];destruct s2 as [(->&s2)|s2].
      + left;split;[reflexivity|apply (IHw _ _ s1 s2)].
      + right;apply (IHw _ _ s1);simpl;tauto.
      + right;apply (IHw _ _ s1);simpl;tauto.
      + right;apply (IHw _ _ s1);simpl;tauto.
  Qed.

  Lemma subword_length u v : u ⊑ v -> ⎢u⎥ <= ⎢v⎥.
  Proof.
    revert u;induction v as [|b v];intros [|a u];simpl;try tauto||lia.
    intros [(<-&s)|s];apply IHv in s;simpl in *;lia.
  Qed.

  Global Instance subword_leq_length : Proper (subword ==> le) (@length A).
  Proof. intros u v;apply subword_length. Qed.
    
  Global Instance subword_PartialOrder : PartialOrder eq subword.
  Proof.
    intros u v;simpl;unfold relation_conjunction,predicate_intersection,Basics.flip;simpl.
    split.
    - intros ->;split;reflexivity.
    - revert u;induction v as [|b v];intros u;intros (s1&s2).
      + destruct u as [|a u];[reflexivity|simpl in *;tauto].
      + destruct u as [|a u];[simpl in *;tauto|].
        destruct s1 as [(<-&s1)|s1].
        * destruct s2 as [(_&s2)|s2].
          -- f_equal;apply IHv;tauto.
          -- apply subword_length in s1.
             apply subword_length in s2.
             simpl in *;lia.
        * apply subword_length in s1.
          apply subword_length in s2.
          simpl in *;lia.
  Qed.

  Lemma subword_app_r u v : v ⊑ u++v.
  Proof.
    induction u;simpl.
    - reflexivity.
    - destruct v;simpl;tauto.
  Qed.
  
  Global Instance subword_app : Proper (subword ==> subword ==> subword) (@app A).
  Proof.
    intros u1 v1 s1 u2 v2 s2;revert u1 s1 u2 v2 s2;induction v1 as [|b v1];
      intros [|a u1] s1;simpl in s1;[tauto|tauto| |];intros u2 v2 s2.
    - rewrite app_nil_l.
      rewrite s2;clear IHv1 s2 u2.
      apply subword_app_r.
    - destruct s1 as [(<-&s1)|s1].
      + simpl;left;split;[reflexivity|].
        apply (IHv1 _ s1 _ _ s2).
      + right;apply (IHv1 _ s1 _ _ s2).
  Qed.

  Lemma subword_nil u : [] ⊑ u.
  Proof. destruct u;simpl;tauto. Qed.
  Lemma subword_cons u a : u ⊑ a::u.
  Proof. destruct u;[simpl;tauto|right;left;split;reflexivity]. Qed.

End subword.
Infix " ⊑ " := subword (at level 80).
