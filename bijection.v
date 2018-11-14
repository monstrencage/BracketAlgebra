(** * RIS.bijection : generate permutations. *)
Require Import tools atoms PeanoNat Nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Applying a permutation commutes with computing the shuffles. *)
Lemma shuffles_act {X: Set} `{Nominal X} π (l : list X) : shuffles (π∙l) = π ∙ shuffles l.
Proof.
  induction l as [|a l].
  - reflexivity.
  - simpl;unfold act at 1 in IHl;rewrite IHl.
    clear;induction (shuffles l) as [|m L].
    + reflexivity.
    + simpl;rewrite act_lists_app;f_equal;[clear|apply IHL].
      induction m as [|b m];simpl.
      * reflexivity.
      * rewrite act_lists_cons;f_equal.
        unfold act at 2 in IHm;rewrite IHm.
        unfold act,act_lists;rewrite map_map,map_map.
        apply map_ext;intro;reflexivity.
Qed.


Section bijection.
  Context {atom : Set} {A : Atom atom}.
  (** * Permutation out of two lists *)
  (** If [l] and [m] are duplication-free and have the same length, then there is a permutation (computed by [make_perm l m]) that send [l] to [m]. Furthermore, every atom mentioned by this permutation comes from either [l] or [m]. *)
  Fixpoint make_perm (l m : list atom) : perm :=
    match (l,m) with
    | ([],_) | (_,[]) => []
    | (a::l,b::m) =>
      let p := make_perm l m in
      (p∙a,b)::p
    end.
  Notation " l >> m " := (make_perm l m) (at level 80).
  
  Lemma make_perm_spec (l m : list atom) :
    NoDup l -> NoDup m -> ⎢l⎥ = ⎢m⎥ ->
    let p := (l >> m) in
    p ∙ l = m /\ elements p ⊆ l++m.
  Proof.
    revert m;induction l as [|a l];intros [|b m] NDl NDm len.
    - simpl;split;auto;reflexivity.
    - simpl in *;discriminate.
    - simpl in *;discriminate.
    - apply NoDup_cons_iff in NDl as (Ia&NDl).
      apply NoDup_cons_iff in NDm as (Ib&NDm).
      destruct (IHl m) as (Ep&Ip);auto.
      split;simpl;revert Ep Ip;set (p:= (l >> m));intros Ep Ip.
      + unfold act at 1;unfold act_lists;simpl;rewrite act_cons.
        repeat simpl_beq;f_equal;auto.
        rewrite <- Ep;apply map_ext_in.
        intros c Ic;simpl.
        rewrite act_cons;destruct_eqX (p∙c) (p∙a).
        * exfalso; apply perm_inj in E as ->;tauto.
        * destruct_eqX (p∙c) b;auto.
          exfalso;apply Ib;rewrite <- E,<- Ep;simpl_In.
          apply In_act_lists.
          rewrite inverse_comp_l;auto.
      + transitivity ([a;b]++l++m);[|intro;simpl_In;simpl;tauto].
        simpl;intros x [<-|[<-|Ix]].
        * case_in (p∙a) (elements (p∗)).
          -- rewrite <- elements_inv_eq in I.
             right;right;rewrite<-Ip;auto.
          -- apply elements_inv_act_atom in I as <-;rewrite inverse_comp_l.
             now left.
        * now right;left.
        * right;right;apply Ip,Ix.
  Qed.

  Lemma make_bij (l m : list atom) :
    NoDup l -> NoDup m -> ⎢l⎥ = ⎢m⎥ -> (l >> m) ∙ l = m.
  Proof. intros;apply make_perm_spec;assumption. Qed.

  (** Applying [make_perm] to two copies of the same lists yields a permutation equivalent to the identity. *)
  Lemma make_perm_id l : (l >> l) ≃ [].
  Proof.
    induction l;simpl.
    - reflexivity.
    - rewrite IHl,act_nil at 1.
      intro b;rewrite act_cons.
      repeat rewrite IHl,act_nil.
      destruct_eqX b a;reflexivity.
  Qed.
  
  (** * Permutation out of a bijection *)

  (** Atom bijections with finite support are equivalent to permutations. *)
  Lemma to_perm_correct f l :
    injective f -> has_support f l -> forall x, ({{l}} >> map f {{l}}) ∙ x = f x.
  Proof.
    intros inj sup.
    cut (({{l}} >> map f {{l}}) ∙ {{l}} = map f {{l}}
         /\ elements ({{l}} >> map f {{l}}) ⊆ l).
    - intros (h1&h2).
      intro x;case_in x l.
      + unfold act,act_lists in h1.
        apply In_undup in I.
        apply In_nth with (d:= x) in I as (n&L&<-).
        rewrite <- map_nth with (f:= f);rewrite <- h1 at 2.
        rewrite <- map_nth with (f:= act ((_ >> _))).
        apply nth_indep;rewrite map_length;auto.
      + destruct_eqX (f x) x.
        * apply elements_inv_act_atom.
          intro Ix;apply I,h2,Ix.
        * apply sup in N;tauto.
    - assert (El : l ≈ {{l}}++ (map f {{l}})).
      + intro x;simpl_In;rewrite in_map_iff;split;try tauto.
        intros [I|(y&Ey&Iy)];[tauto|].
        simpl_In in Iy;eapply injective_support_closed in Iy;eauto.
        rewrite Ey in *;tauto.
      + rewrite El at 7; apply make_perm_spec;auto.
        * apply NoDup_undup.
        * apply NoDup_map_injective,NoDup_undup;auto.
        * symmetry;apply map_length.
  Qed.

  (** Functions that are injective and finitely supported may be represented as permutations. *)
  Theorem bijection_iff_perm (f : atom -> atom) :
    (injective f /\ supported f) <-> exists p, f ≃ (act p).
  Proof.
    split.
    - intros (I&[(l&S)]);exists ({{l}} >> map f {{l}}).
      intro x;symmetry;apply to_perm_correct;auto.
    - intros (p&E);rewrite E;split;eauto.
      apply injective_perm.
  Qed.

  (** * Enumerate permutations *)

  (** [permutations l] lists every permutation supported by [l]. *)
  Definition permutations l : list perm :=
    map (make_perm {{l}}) (shuffles {{l}}).

  (** Indeed, if every atom [a] such that [q∙a<>a] belongs to the list [l], then there is a permutation [p] that is equivalent to [q] and belongs to the list [permutations l]. *)
  Lemma permutations_spec q l :
    (exists p, p ≃ q /\ p ∈ permutations l) <-> (forall a, a <> q∙a -> a ∈ l).
  Proof.
    split.
    - intros (p&E&I);intro a.
      unfold permutations in I.
      apply in_map_iff in I as (m&<-&I).
      pose proof (shuffles_equiv I) as e.
      pose proof (shuffles_nodup (NoDup_undup l) I) as nd'.
      destruct make_perm_spec with (l:={{l}}) (m:=m)as (h1&h2).
      + apply NoDup_undup.
      + assumption.
      + apply shuffles_length,I.
      + rewrite <- e in h2 at 2.
        assert (e':{{l}}++{{l}}≈l) by (intro;simpl_In;tauto);rewrite e' in h2;clear e'.
        rewrite <- E.
        case_in a (elements ({{l}} >> m)).
        * apply h2 in I0;tauto.
        * rewrite elements_inv_act_atom;tauto.
    - intros h.
      assert (nd':NoDup (q∙{{l}})) by (apply NoDup_map_injective;[apply injective_perm
                                                                 |apply NoDup_undup]).
      exists ({{l}} >> q∙{{l}});split.
      + destruct make_perm_spec with (l:={{l}}) (m:=(q∙{{l}}))as (h1&h2);
          try assumption||solve_length||apply NoDup_undup.
        intro a; case_in a l.
        * apply (map_bij h1);simpl_In;assumption.
        * destruct_eqX a (q∙a).
          -- repeat rewrite <- E.
             rewrite <- E in I.
             rewrite elements_inv_act_atom;auto.
             intro I';apply h2 in I';simpl_In in I'.
             destruct I' as [I'|I'];[tauto|].
             rewrite In_act_lists,E,act_pinv_p in I';simpl_In in I'.
             tauto.
          -- apply h in N;tauto.
      + apply in_map_iff;exists (q∙{{l}});split;auto.
        apply shuffles_spec.
        pose proof (NoDup_undup l) as nd.
        rewrite NoDup_nb in nd,nd'.
        cut ({{l}}≈q∙{{l}}).
        * intros e a;case_in a {{l}}.
          -- transitivity 1.
             ++ apply nb_In in I.
                pose proof (nd a).
                lia.
             ++ apply e,nb_In in I.
                pose proof (nd' a).
                lia.
          -- pose proof I as I';apply nb_not_In in I' as ->.
             rewrite e in I;apply nb_not_In in I as ->.
             reflexivity.
        * intro a;rewrite In_act_lists.
          destruct_eqX (q∗∙a) (q∙(q∗∙a)).
          -- rewrite act_p_pinv;tauto.
          -- apply h in N.
             destruct_eqX a (q∙a).
             ++ rewrite act_pinv_p in *.
                rewrite <- E;tauto.
             ++ simpl_In;apply h in N0;tauto.
  Qed. 

  (** This means that if [p] is a permutation supported by [l], for every name [a] we know that [a∈l] if and only if [a∈p∙l]. *)
  Lemma permutations_image p l :
    p ∈ permutations l -> p∙l ≈ l.
  Proof.
    intros I.
    cut (exists q, q≃p /\ q∈permutations l);[|exists p;split;[reflexivity|assumption]].
    rewrite permutations_spec;intros h a;rewrite In_act_lists.
    destruct_eqX (p∙a) a.
    + rewrite <- E at 1;rewrite act_pinv_p;tauto.
    + split;intro Ia;apply h.
      * intros E;rewrite <- E in N;exfalso;apply N;reflexivity.
      * rewrite act_p_pinv.
        intro E;apply N.
        rewrite <- E at 1;rewrite act_p_pinv;reflexivity.
  Qed.

  (** The permutations appearing in [permutations l] have the additional property that they only mention names from [l]. *)
  Lemma permutations_elements p l :
    p ∈ permutations l -> elements p ⊆ l.
  Proof.
    intros I;pose proof (NoDup_undup l) as nd.
    unfold permutations in I; apply in_map_iff in I as (l'&<-&I).
    destruct make_perm_spec with (l:={{l}}) (m:=l')as (h1&h2); try assumption.
    - eapply shuffles_nodup;eauto.
    - apply shuffles_length,I.
    - rewrite <- (undup_equivalent l) at 2.
      rewrite h2,(shuffles_equiv I);intro;simpl_In;tauto.
  Qed.

End bijection.
Notation " l >> m " := (make_perm l m) (at level 80).
        