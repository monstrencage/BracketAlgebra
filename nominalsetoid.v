(** * RIS.nominalsetoid : Nominal sets up-to equivalence. *)

Require Import tools atoms PeanoNat Nat bijection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Definitions *)
Section s.
  (** We fix a decidable set of atoms. *)
  Context {atom : Set}{A : Atom atom}.

  (** We use the notation [π ⊙ x] for the group action of a nominal setoid, and [⌈x⌉] for its support. *)
  Class ActionSetoid (X : Set) := actoid : perm -> X -> X.
  Infix " ⊙ " := actoid (at level 50).
  Class SupportSetoid {A : Atom atom} (X : Set) := suppoid : X -> list atom.
  Notation " ⌈ x ⌉ " := (suppoid x).
  
  (** A nominal setoid is a set [X] equipped with a relation [≃], an action [⊙] and a support function [⌈_⌉] satisfying the following axioms: *)
  Class NominalSetoid (X : Set) (equiv : SemEquiv X) (act : ActionSetoid X)
        (supp : SupportSetoid X) :=
    {
      (** [≃] is an equivalence relation; *)
      eq_equivalence :> Equivalence sequiv;
     (** equivalent elements have equivalent support : if [x≃y], then [a∈⌈x⌉ <-> a∈⌈y⌉]; *)
      eq_support :> Proper (sequiv ==> (@equivalent atom)) suppoid;
      (** the action in compatible with the equivalence relation ; *)
      eq_act_proper π :> Proper (sequiv ==> sequiv) (actoid π);
      (** the remaining axioms are the same as for nominal sets, except that equality of elements in [X] has been substituted with [≃]. *)
      action_invariant_eq : forall (x : X) π, (π ∙ ⌈x⌉ = ⌈x⌉) -> (π ⊙ x) ≃ x;
      support_action_eq : forall x π, ⌈π ⊙ x⌉ ≈ π∙⌈x⌉;
      action_compose_eq : forall x π π', π ⊙ (π' ⊙ x) ≃ (π++π') ⊙ x
    }.

  
  (** The following observations are straightforward to check directly from the axioms we just listed. *)
  Remark actoid_pinv_p {X : Set} `{NominalSetoid X}:
    forall π x, π∗ ⊙ (π ⊙ x) ≃ x.
  Proof.
    intros;rewrite action_compose_eq;apply action_invariant_eq.
    rewrite perm_pinv_p_eq_nil,act_nil;reflexivity.
  Qed.

  Remark actoid_p_pinv {X : Set} `{NominalSetoid X}:
    forall π x, π ⊙ (π∗ ⊙ x) ≃ x.
  Proof.
    intros;rewrite action_compose_eq;apply action_invariant_eq.
    rewrite perm_p_pinv_eq_nil,act_nil;reflexivity.
  Qed.
  
  (** Permutations that are equivalent as functions yield the same action (even if they are syntactically different): if for every atom [a] we have [π ∙ a = π' ∙ a] and if [x≃y], then [π⊙x≃π'⊙y]. *)
  Global Instance eq_act {X : Set} `{NominalSetoid X} :
    Proper (sequiv ==> sequiv ==> sequiv) actoid.
  Proof.
    intros π π' Eπ x y <- ;clear y.
    transitivity (π'⊙(π'∗ ⊙ (π ⊙ x))).
    - rewrite actoid_p_pinv;reflexivity.
    - apply eq_act_proper.
      rewrite action_compose_eq;apply action_invariant_eq.
      rewrite <- action_compose.
      rewrite Eπ,act_pinv_p;reflexivity.
  Qed.

  Lemma minimal_support_eq {X: Set} `{NominalSetoid X} l x :
    (forall π, (forall a, a ∈ l -> π ∙ a = a) -> π ⊙ x ≃ x) -> ⌈x⌉ ⊆ l.
  Proof.
    intros s a Ia.
    case_in a l;[tauto|exfalso].
    destruct (exists_fresh (a::l++⌈x⌉)) as (b&hb).
    simpl_In in hb.
    assert (E: [(a,b)]⊙x≃x).
    - apply s;intros c Ic.
      apply elements_inv_act_atom;simpl.
      intros [->|[->|F]];tauto.
    - pose proof (support_action_eq x [(a,b)]) as E'.
      rewrite E in E';revert Ia.
      rewrite E',In_act_lists.
      unfold act,act_atom;simpl;simpl_beq.
      tauto.                  
  Qed.
  
  Remark ActionSetoid_ext_In {X:Set} `{NominalSetoid X}:
    forall π π' x, (forall a, a ∈ ⌈x⌉ -> π ∙ a = π' ∙ a) -> π ⊙ x ≃ π' ⊙ x.
  Proof.
    intros p q x h.
    cut (x ≃ q∗ ⊙ (p ⊙ x)).
    - intros e ;rewrite e at 2;rewrite actoid_p_pinv;reflexivity.
    - symmetry;rewrite action_compose_eq.
      apply action_invariant_eq,map_eq_id.
      intros a Ia;rewrite <- action_compose,h,act_pinv_p;reflexivity||assumption.
  Qed.
     
End s.

(* begin hide *)
Infix " ⊙ " := actoid (at level 50).
Notation " ⌈ x ⌉ " := (suppoid x).
(* Arguments NominalSetoid : clear implicits. *)
Arguments NominalSetoid {atom} A X {equiv act supp}.
Arguments ActionSetoid _ A X : clear implicits.
Arguments SupportSetoid _ A X : clear implicits.
(* end hide *)

(** * Lifting the structure to lists *)
Section list.
  (** Let us fix a nominal setoid [S] over a set of atoms [Atom]. *)
  Context {atom : Set}{A: Atom atom}.
  Context {S : Set} {eqS : SemEquiv S} {actS : ActionSetoid _ A S}
          {suppS : SupportSetoid _ A S}.
  Context {N: NominalSetoid A S}.

  (** We define the action of [π] on a list by apply [π] pointwise. *)
  Global Instance actoid_lists : ActionSetoid _ A (list S):=
    fun π l => map (fun x => π⊙x) l.

  (* begin hide *)
  Remark actoid_lists_app π (l m : list S) : π⊙(l++m) = π⊙l++π⊙m.
  Proof. apply map_app. Qed.

  Remark actoid_lists_cons π (a :S) l : π⊙(a::l) = π⊙a::π⊙l.
  Proof. reflexivity. Qed.

  Remark actoid_lists_length π (l : list S) : ⎢π⊙l⎥ = ⎢l⎥.
  Proof. apply map_length. Qed.
  (* end hide *)

  (** To compute the support of a list, we compute the support of each element, take the union of those, and remove duplicates. *)
  Global Instance SupportSetoidList : SupportSetoid _ A (list S) :=
    fun l => {{flat_map suppoid l}}.

  (** Two lists are equivalent if they have the same length, and if their elements are pointwise equivalent. For instance if [l=l1...ln] and [m=m1...mn], then [l≃m] if and only if [forall 1<=i<=n, li≃mi]. *)
  Fixpoint semeq_list (l1 l2 : list S) :=
    match (l1,l2) with
    | ([],[]) => True
    | (a::l1,b::l2) => (a≃b) /\ semeq_list l1 l2
    | (_::_,[]) | ([],_::_) => False
    end.
  
  Instance SemEquiv_listS : SemEquiv (list S) :=  semeq_list.

  (* begin hide *)
  Global Instance cons_sequiv : Proper (sequiv ==> sequiv ==> sequiv) cons.
  Proof.
    intros x y E l m E'.
    unfold sequiv,SemEquiv_listS in *;simpl;tauto.
  Qed.
  Global Instance app_sequiv : Proper (sequiv ==> sequiv ==> sequiv) (@app S).
  Proof.
    intros x y E l m E'.
    unfold sequiv,SemEquiv_listS in *.
    revert y E;induction x as [|a x];intros [|b y];simpl;try tauto.
    intros (h1&h2);split;[tauto|apply IHx,h2].
  Qed.
  Global Instance length_sequiv : Proper (sequiv ==> eq) (@length S).
  Proof.
    intros x y E.
    unfold sequiv,SemEquiv_listS in *.
    revert y E;induction x as [|a x];intros [|b y];simpl;try tauto.
    intros (h1&h2);rewrite (IHx y);reflexivity||assumption.
  Qed.
  (* end hide *)

  (** It is a simple matter to check that the operations we have defined indeed define a nominal setoid structure over [list S]. *)
  Global Instance NominalSetoid_list : NominalSetoid A (list S).
  Proof.
    split.
    - unfold sequiv,SemEquiv_listS;split.
      + intros l;induction l as [|a l];simpl.
        * tauto.
        * split;[reflexivity|assumption].
      + intros l1;induction l1 as [|a l1];intros [|b l2];simpl;try tauto.
        intros (->&h);intuition.
      + intros l1;induction l1 as [|a l1];intros [|b l2] [|c l3];simpl;try tauto.
        intros (->&h1) (->&h2);split;[reflexivity|].
        apply (IHl1 l2 l3);assumption.
    - unfold sequiv,SemEquiv_listS;intros l1;induction l1 as [|a l1];intros [|b l2];simpl;
        try tauto||reflexivity.
      intros (e&h);apply IHl1 in h;revert h.
      unfold suppoid,SupportSetoidList;simpl.
      repeat rewrite undup_equivalent;intros ->.
      rewrite (eq_support e);reflexivity.
    - intros π l1;unfold sequiv,SemEquiv_listS;induction l1 as [|a l1];intros [|b l2];simpl;
        try tauto.
      intros (->&e);split;[reflexivity|].
      apply IHl1,e.
    - unfold sequiv,SemEquiv_listS;unfold suppoid,SupportSetoidList in *;simpl.
      intros x p h; unfold actoid,actoid_lists in *.
      unfold act,act_lists in h;rewrite <- map_undup_id in h.
      induction x as [|x l];auto.
      + reflexivity.
      + revert h;simpl;rewrite map_app;intro E;apply length_app in E as (E1&E2).
        * split;[|apply IHl,E2].
          apply action_invariant_eq,E1.
        * apply map_length.
    - unfold act,act_lists,actoid,actoid_lists,suppoid,SupportSetoidList,sequiv,SemEquiv_listS in *.
      intros x p;symmetry;simpl in *.
      rewrite map_undup_inj;eauto using perm_inj.
      repeat rewrite flat_map_concat_map.
      rewrite concat_map,map_map,map_map,undup_equivalent,undup_equivalent.
      intros a;repeat rewrite <- flat_map_concat_map,in_flat_map.
      setoid_rewrite support_action_eq;unfold act at 2,act_lists;tauto.
    - intros;unfold actoid,actoid_lists.
      rewrite map_map.
      unfold sequiv,SemEquiv_listS;induction x as [|a x];simpl;[tauto|split;[|apply IHx]].
      apply action_compose_eq.
  Qed.

  (* begin hide *)
  Remark suppoid_cons b w : ⌈b::w⌉ ≈ ⌈b⌉ ++ ⌈w⌉.
  Proof.
    intro a;unfold suppoid,SupportSetoidList.
    repeat rewrite undup_equivalent.
    simpl;simpl_In;tauto.
  Qed.
  Remark suppoid_app w1 w2 : ⌈w1++w2⌉ ≈ ⌈w1⌉ ++ ⌈w2⌉.
  Proof.
    intro a;unfold suppoid,SupportSetoidList.
    repeat rewrite undup_equivalent.
    rewrite flat_map_concat_map,map_app,concat_app,<-flat_map_concat_map,<-flat_map_concat_map.
    reflexivity.
  Qed.
  (* end hide *)
  
End list.


