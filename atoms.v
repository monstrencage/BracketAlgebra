(** * RIS.atoms : Nominal sets. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools.
Require Export Bool.
 
Section perm.
  (** * Set of atoms *)
  (** Type of atoms *)
  Class Atom (atom : Set) :=
    {
      (** We require [Atom] to be decidable, by a boolean function. *)
      dec_atom :> decidable_set atom;
      (** We also want an infinite number of atoms to be available. *)
      exists_fresh : forall l : list atom, exists a, ~ a ∈ l
    }.
  Context {atom : Set}{Atoms : Atom atom}.

  (** * Permutations *)
  (** ** Definitions and elementary properties *)

  (** Permutations are defined as lists of pairs. This is general enough as every permutation (on an infinite set) can be factored as a product of cycles of length 2 (we will provide a formal proof of this fact later on). *)
  Definition perm {Atoms : Atom atom} := list (atom * atom).

  (** Boolean equality predicate over permutations. *)
  Global Instance dec_perm : decidable_set perm.
  Proof. apply @dec_list,dec_prod;apply dec_atom. Qed.

  (** Notation for the action of a permutation on a set [X]. *)
  Class Action (Atoms : Atom atom) X := act : perm -> X -> X.
  Infix " ∙ " := act (at level 20).
  (** Notation for support functions *)
  Class Support (Atoms : Atom atom) (T : Set) := support : T -> list atom.
  Notation " ⌊ e ⌋ " := (support e).

  (** [act p a] computes the effect of the permutation [p] on the atom [a]. *)
  Global Instance act_atom : (Action Atoms atom) :=
    fun p a =>
      fold_right (fun t a =>
                    match t with
                    | (x,y) => if a =?= x
                              then y
                              else if a =?= y
                                   then x
                                   else a
                    end)
                 a p.

  (** The effect of the empty permutation is the identity. *)
  Lemma act_atom_nil : forall a, [] ∙ a = a.
  Proof. now simpl. Qed.

  (** List concatenation corresponds to functional composition of permutations. *)
  Lemma act_comp_app (p q : perm) x : p ∙ (q ∙ x) = (p++q) ∙ x.
  Proof.
    unfold act,act_atom ;rewrite fold_right_app;auto.
  Qed.

  (* begin hide *)
  Lemma act_cons a b p x : ((a,b)::p) ∙ x = if (p∙x)=?=a then b else if (p∙x)=?= b then a else p∙x.
  Proof. reflexivity. Qed.
  (* end hide *)
  (** Permutations are injective. *)
  Lemma perm_inj p x y : p ∙ x = p ∙ y -> x = y.
    intro h. induction p.
    simpl in *;auto.
    destruct a as (a&b).
    rewrite act_cons,act_cons in h;apply IHp.
    destruct_eqX (p ∙ x) a;destruct_eqX (p ∙ y) a;destruct_eqX (p ∙ x) b;destruct_eqX (p ∙ y) b;subst;
      tauto||auto.
  Qed.

  (** Permutations are bijective. *)
  Lemma perm_bij : forall p x y, p ∙ x = p ∙ y <-> x = y.
  Proof.
    split;intro h.
    eapply perm_inj;eauto.
    rewrite h;tauto.
  Qed.

  (** ** Inverse of a permutation *)
  (** The inverse of a permutation is computed by reversing the list. *)
  Definition inverse (p : perm) : perm := rev p.

  Notation "p ∗" := (inverse p) (at level 35).
  Hint Unfold inverse.

  (** The inverse is an involutive operation. *)
  Lemma inverse_inv (p : perm) : (p∗)∗ = p.
    unfold inverse;apply rev_involutive.
  Qed.

  (** Application of the inverse of a permutation is the functional left inverse of the application of the same permutation. *)
  Lemma inverse_comp_l (p : perm) : forall x,  p∗ ∙ (p ∙ x) = x.
  Proof.
    intro x; induction p as [|(a&b)p];simpl;auto.
    repeat (rewrite act_cons||simpl).  
    rewrite <- act_comp_app;simpl;
      destruct_eqX (p ∙ x) a.
    - rewrite act_cons,act_atom_nil;destruct_eqX b a;simpl;subst;auto.
    - rewrite act_cons,act_atom_nil;destruct_eqX (p ∙ x) b;subst;auto.
      destruct_eqX (p ∙ x) a;tauto.
  Qed.
  Ltac inv1 p x := replace x with (p∗∙(p∙x));[|apply inverse_comp_l].

  (** Application of the inverse of a permutation is the functional right inverse of the application of the same permutation. *)
  Lemma inverse_comp_r (p : perm) : forall x, p ∙ (p∗ ∙ x) = x.
  Proof.
    intro x;rewrite <- (inverse_inv p) at 1.
    apply inverse_comp_l.
  Qed.
  Ltac inv2 p x := replace x with (p∙(p∗∙x));[|apply inverse_comp_r].

  (** The inverse of a composite permutation is the reverse composition of the inverses of its parts. *)
  Lemma inverse_app p q : (p++q)∗ = q∗++p∗.
  Proof. unfold inverse;apply rev_app_distr;reflexivity. Qed.

  Hint Resolve inverse_inv inverse_comp_l inverse_comp_r.
  Ltac aux_perm :=
    (rewrite inverse_comp_l in * )
    || (rewrite inverse_comp_r in * )
    || (rewrite inverse_inv in * ).

  (** ** Equivalence of permutations *)
  (** Two permutations [p] and [q] are considered equivalent when the functions [p∙_] and [q∙_] are extensionally equal. *)
  Global Instance equiv_perm : SemEquiv perm := fun p q => forall a, p ∙ a = q ∙ a.

  (** The relation [≃] is an equivalence relation. *)
  Lemma equiv_perm_refl p : p ≃ p.
  Proof. intros a;reflexivity. Qed.
  Lemma equiv_perm_sym p q : p ≃ q -> q ≃ p.
  Proof. intros E a ;rewrite E;auto. Qed.
  Lemma equiv_perm_trans p q r : p ≃ q -> q ≃ r -> p ≃ r.
  Proof. intros E1 E2 a;rewrite E1,E2;auto. Qed.

  Hint Resolve equiv_perm_refl equiv_perm_sym equiv_perm_trans.

  Global Instance equiv_perm_Equivalence : Equivalence sequiv.
  Proof.
    split.
    - intros p a;reflexivity.
    - intros p q E a ;rewrite E;auto.
    - intros p q r E1 E2 a;rewrite E1,E2;auto.
  Qed.

  (** If [p≃q] then [p∗≃q∗]. *)
  Global Instance equiv_perm_inverse : Proper (sequiv ==> sequiv) inverse.
  Proof. intros p q H a;inv1 p ((q∗)∙a); rewrite H,inverse_comp_r;auto.
  Qed.

  (** If [p≃q] and [p'≃q'] then [p++p'≃q++q']. *)
  Global Instance equiv_perm_app :
    Proper (sequiv ==> sequiv ==> sequiv) (@app (atom*atom)%type).
  Proof.
    intros p p' E q q' F a;repeat rewrite <- act_comp_app;
      rewrite E,F;auto.
  Qed.

  (** Paraphrasing of the definition of [≃]. *)
  Global Instance equiv_perm_spec a :
    Proper (sequiv ==> Logic.eq) (fun p => p ∙ a).
  Proof. intros p q e; rewrite e ;reflexivity. Qed.

  (** For every atom [a], the permutations [[a,a]] and [[]] are equivalent. *)
  Lemma perm_a_a_eq_nil {a} : [(a,a)] ≃ [].
  Proof. intro x;rewrite act_cons,act_atom_nil;destruct_eqX x a;auto. Qed.

  (** For every permutation [p], [p∗++p] and [p++p∗] are also equivalent to [[]]. *)
  Lemma perm_pinv_p_eq_nil {p} : (p∗++p) ≃ [].
  Proof. intro x; rewrite <-act_comp_app,inverse_comp_l;reflexivity. Qed.
  Lemma perm_p_pinv_eq_nil {p} : (p++p∗) ≃ [].
  Proof. intro x; rewrite <-act_comp_app,inverse_comp_r;reflexivity. Qed.

  (** ** Elements *)
  (** The elements of a permutation are the atoms appearing in it. *)
  Definition elements (p:perm) :=
    flat_map (fun ab => (fst ab)::(snd ab)::[]) p.

  (** Atoms not appearing in [p] are fixpoints of [p]. *)
  Lemma elements_inv_act_atom x p : ~ In x (elements p) -> p∙x = x.
  Proof.
    induction p as [|(a,b) p];simpl;auto.
    rewrite act_cons;intros h;replace (p∙x) with x.
    - destruct_eqX x a;[|destruct_eqX x b];tauto.
    - symmetry;apply IHp;tauto.
  Qed.

  (** The function [elements] distributes over concatenations. *)
  Lemma elements_app p q : elements (p++q) = elements p++elements q.
  Proof. induction p as [|(a,b) p];simpl;auto;congruence. Qed.

  (** The inverse function preserves elements. *)
  Lemma elements_inv_eq q : elements q ≈ elements (q∗).
  Proof.
    unfold inverse;induction q as [|(a,b) q];simpl;auto.
    - reflexivity.
    - rewrite IHq;clear IHq.
      rewrite elements_app.
      intro x;simpl_In;simpl;tauto.
  Qed.

  (** For any atom [a] not mentioned in [p] and any atom [b], [p] is equivalent to the permutation [[(a,p∙b)]++p++[(a,b)]]. *)
  Lemma factor_perm a b p : ~ a ∈ elements p -> p ≃ [(a,p∙b)]++p++[(a,b)].
  Proof.
    intros I x;repeat rewrite <- act_comp_app.
    repeat rewrite act_cons,act_atom_nil.
    simpl;destruct_eqX x a.
    - rewrite elements_inv_act_atom;auto.
      destruct_eqX (p∙b) a;auto.
    - destruct_eqX x b.
      + rewrite (@elements_inv_act_atom a);try simpl_beq;auto.
      + destruct_eqX (p∙x) a;auto.
        * exfalso;apply N.
          rewrite<- (inverse_comp_l p),(elements_inv_act_atom I),<- E,inverse_comp_l;auto.
        * destruct_eqX (p∙x) (p∙b);auto.
          exfalso;apply N0.
          rewrite<- (inverse_comp_l p),<-E,inverse_comp_l;auto.
  Qed.

  (** ** Lifting an action on [S] to an action on [list S] *)
  (** We can lift an action over [A] to an action over [list A] by applying it pointwise. *)
  Global Instance act_lists {S : Set} `{@Action Atoms S} : Action Atoms (list S):=
    fun p l => map (fun x => p∙x) l.

  Lemma act_lists_app {S : Set} `{@Action Atoms S} p (l m : list S) :
    p∙(l++m) = p∙l++p∙m.
  Proof. apply map_app. Qed.

  Lemma act_lists_cons {S : Set} `{@Action Atoms S} p (a :S) l :
    p∙(a::l) = p∙a::p∙l.
  Proof. reflexivity. Qed.

  Lemma act_lists_length {S : Set} `{@Action Atoms S} p (l : list S) : ⎢p∙l⎥ = ⎢l⎥.
  Proof. apply map_length. Qed.

  (** * Nominal sets *)
  (** ** Definitions *) 
  (** For [S] to be nominal, it needs to be equipped with an action and a support, and they must satisfy these three axioms. *)
  Class Nominal (S : Set) {action:Action Atoms S} {supp:Support Atoms S} :=
    {
      action_invariant : forall (x : S) π, π ∙ ⌊x⌋ = ⌊x⌋ -> π ∙ x = x;
      support_action : forall (x : S) π, ⌊π ∙ x⌋ ≈ π ∙ ⌊x⌋ ;
      action_compose : forall (x : S) π π', π ∙ (π' ∙ x) = (π++π') ∙ x;
    }.
  (* begin hide *)
  Arguments Nominal S {action} {supp}.
  (* end hide *)

  (** If [x] is an element of a nominal set [N], a name [a] is _fresh_ for [x] if it does not appear in the support of [x]. *)
  Notation " a # x " := (~ a ∈ ⌊x⌋) (at level 80).
  
  (** ** Canonical nominal structures *)
  (** *** Atoms *)
  (** The support of [a] is [[a]]. *)
  Global Instance SupportAtom : Support Atoms atom := fun a => [a].

  (** The set of atoms is nominal. *)
  Global Instance Nominal_Atom : Nominal atom.
  Proof.
    split.
    - intros x p;unfold act at 1;unfold act_lists,support,SupportAtom;simpl.
      intros E;inversion E as [[X]];repeat rewrite X;auto.
    - intros x p;unfold act at 2;unfold act_lists,support,SupportAtom;simpl;auto.
      reflexivity.
    - intros x p q;apply act_comp_app.
  Qed.

  (** *** Lists *)
  (** The support of a list is the union of the supports of its elements. Because we encode supports as duplication-free lists, we remove duplicates using the [{{}}] function. *)
  Global Instance SupportList (S : Set) `{Support S} : Support Atoms (list S) :=
    fun l => {{flat_map support l}}.

  (** If [A] is nominal, so is [list A]. *)
  Global Instance Nominal_list (S : Set)  `{Nominal S} : Nominal (list S).
  Proof.
    split.
    - unfold support,SupportList in *;simpl.
      intros x p h; unfold act,act_lists in *.
      rewrite <- map_undup_id in h.
      induction x as [|x l];auto.
      revert h;simpl;rewrite map_app;intro E;apply length_app in E as (E1&E2).
      * apply IHl in E2 as ->.
        apply action_invariant in E1 as ->;auto.
      * apply map_length.
    - unfold act,act_lists,support,SupportList in *;simpl;auto.
      intros x p;symmetry.
      rewrite map_undup_inj;eauto using perm_inj.
      f_equal;repeat rewrite flat_map_concat_map.
      rewrite concat_map,map_map,map_map,undup_equivalent,undup_equivalent.
      intros a;repeat rewrite <- flat_map_concat_map,in_flat_map.
      setoid_rewrite support_action;unfold act at 2,act_lists;tauto.
    - intros;unfold act,act_lists.
      rewrite map_map;apply map_ext;intros;apply action_compose.
  Qed.

  (** *** Pairs *)
  (** We extend the action to pairs by applying the permutation to both components. *)
  Global Instance act_pair {A B : Set} `{@Action Atoms A,@Action Atoms B} : Action Atoms (A*B):=
    fun p l => (p ∙ (fst l),p ∙ (snd l)).

  (** The support of a pair is the union of the supports of its components. *)
  Global Instance SupportPair (A B: Set) `{@Support Atoms A,@Support Atoms B}
    : Support Atoms (A*B) := fun p => {{⌊fst p⌋++⌊snd p⌋}}.

  (** If [A] and [B] are nominal, so is [A*B]. *)
  Global Instance Nominal_Pair (A B : Set) `{Nominal A,Nominal B}
    : Nominal (A * B).
  Proof.
    split.
    - intros (x,y) p;unfold act,act_pair,act_lists,support,SupportPair.
      intro E; apply map_undup_id in E.
      rewrite map_app in E;apply length_app in E as (E1&E2);[|apply map_length].
      simpl in *;f_equal;apply action_invariant;tauto.
    - unfold act,act_lists,act_pair,support,SupportPair in *;simpl;auto.
      intros (a,b) p.
      intro x;simpl_In;repeat rewrite support_action.
      repeat rewrite map_undup_inj,map_app;eauto using perm_inj;simpl_In;tauto.
    - intros (a,b) p q;unfold act,act_pair;simpl.
      f_equal;apply action_compose.
  Qed.

  (** *** Natural numbers *)
  (** We can endow natural numbers with a trivial nominal structure. *)
  Global Instance action_nat : Action Atoms nat := fun _ n => n.
  Global Instance support_nat : Support Atoms nat := fun n => [].
  Global Instance groupAct_nat : Nominal nat.
  Proof.
    split;intro;intros;unfold support,support_nat,act,action_nat;simpl;auto using NoDup_nil.
    reflexivity.
  Qed.

  (** *** Option types *)
  (** If [A] is nominal, so is [option A]. *)
  Global Instance Action_option {A : Set} `{@Action Atoms A} : Action Atoms (option A):=
    fun p l => match l with None => None | Some a => Some (p∙a) end.

  Global Instance Support_option (A : Set) `{@Support Atoms A}
    : Support Atoms (option A) := fun l =>  match l with None => [] | Some l => ⌊l⌋ end.

  Global Instance Nominal_option (A : Set) `{Nominal A} : Nominal (option A).
  Proof.
    split;unfold act,support.
    - intros [x|] p;simpl;auto.
      intro E;f_equal;apply action_invariant,E.
    - intros [x|] p;simpl.
      + apply support_action.
      + reflexivity.
    - intros [x|] p1 p2;simpl;auto.
      f_equal;apply action_compose.
  Qed.

  (** *** Sum types *)
  (** If [A] and [B] are nominal, so is [A+B]. *)
  Global Instance Action_sum {A B : Set} `{@Action Atoms A,@Action Atoms B} : Action Atoms (A+B):=
    fun p l => match l with inl a => inl (p∙a) | inr b => inr (p∙b) end.

  Global Instance Support_sum {A B : Set} `{@Support Atoms A,@Support Atoms B} : Support Atoms (A+B) :=
    fun l =>  match l with inl x => ⌊x⌋ | inr x => ⌊x⌋ end.

  Global Instance Nominal_sum {A B : Set} `{Nominal A,Nominal B} : Nominal (A+B).
  Proof.
    split;unfold act,support.
    - intros [a|b] p;simpl;auto;intro E;f_equal;apply action_invariant,E.
    - intros [a|b] p;simpl;apply support_action.
    - intros [a|b] p1 p2;simpl;auto;f_equal;apply action_compose.
  Qed.

  (** ** Properties of group actions *)
  Section group.

    Context {A : Set} `{Nominal A}.

    (** Equivalent permutations yield the same action. *)
    Global Instance equiv_perm_act :
      Proper (sequiv ==> Logic.eq ==> Logic.eq) act.
    Proof.
      intros p q EP a b <- .
      replace (q ∙ a) with (p∙((p∗++q) ∙ a)).
      - f_equal;symmetry;apply action_invariant,map_eq_id.
        intros b I;rewrite <- action_compose,<-EP,inverse_comp_l;auto.
      - rewrite action_compose,<-app_ass,<-action_compose;apply action_invariant,map_eq_id.
        intros;rewrite <- action_compose;apply inverse_comp_r.
    Qed.

    Lemma act_nil : forall a : A, [] ∙ a = a.
    Proof.
      intro a;apply action_invariant;unfold act,act_lists;
        erewrite map_ext;[apply map_id|];intros; now simpl.
    Qed.

    Lemma act_p_pinv p (a : A) : p ∙ (p∗ ∙ a) = a.
    Proof.
      rewrite action_compose.
      setoid_rewrite perm_p_pinv_eq_nil.
      apply act_nil.
    Qed.

    Lemma act_pinv_p p (a : A) : p∗ ∙ (p ∙ a) = a.
    Proof.
      rewrite action_compose.
      setoid_rewrite perm_pinv_p_eq_nil.
      apply act_nil.
    Qed.

    (** If the support of [x] is disjoint from the elements of [p] then [x] is a fixpoint of [p∙]. *)
    Lemma elements_inv_act p x :
      (forall a, a ∈ ⌊x⌋ -> ~ a ∈ elements p) -> p∙x = x.
    Proof.
      intros I;apply action_invariant,map_eq_id.
      intros a Ia;apply elements_inv_act_atom,I,Ia.
    Qed.

    (** The function [p∙] is a bijection. *)
    Lemma act_bij p x y : p ∙ x = p ∙ y <-> x = y.
    Proof.
      split;[intro h|intros ->;auto].
      rewrite<- act_pinv_p with (p:=p),<- h,act_pinv_p;auto.
    Qed.

    (** We can relate the elements appearing in [l] with those appearing in [p∙l]. *)
    Lemma In_act_lists a p (l : list A) :
      a ∈ (p ∙ l) <-> (p∗ ∙ a) ∈ l.
    Proof.
      unfold act at 1; unfold act_lists;rewrite in_map_iff;split;
        [intros (y & <- & h)|intro h; eexists;split;[|eauto]].
      - rewrite act_pinv_p;auto.
      - rewrite act_p_pinv;auto.
    Qed.

    (** A name [a] is in the support of a list if and only if it is in the support of one of its elements. *)
    Lemma In_support_list a l : a ∈ ⌊l⌋ <-> exists x, x ∈ l /\ a ∈ ⌊x⌋.
    Proof.
      unfold support at 1;unfold SupportList.
      rewrite In_undup,in_flat_map;tauto.
    Qed.

    (** The support of a concatenation is equivalent to the concatenation of the supports. *)
    Lemma support_list_app (l m : list A) : ⌊l++m⌋ ≈ ⌊l⌋++⌊m⌋.
    Proof.
      unfold support,SupportList.
      rewrite flat_map_concat_map,map_app,concat_app,<-flat_map_concat_map,<-flat_map_concat_map.
      intro;simpl_In;tauto.
    Qed.

    (** The support of a cons is equivalent to the concatenation of the supports. *)
    Lemma support_list_cons l (w : list A) : ⌊l :: w⌋ ≈ ⌊l⌋++⌊w⌋.
    Proof.
      intro p;simpl_In;rewrite In_support_list,(In_support_list p w).
      simpl;firstorder (subst;auto).
    Qed.


    (** [rmfst] commutes with the action of permutations. *)
    Remark rmfst_perm `{decidable_set A} p l a : (p∙l) ⊖ a = p∙(l ⊖ p∗∙a).
    Proof.
      case_in (p∗∙a) l.
      - apply decomposition in I as (s1&s2&->&I).
        rewrite rmfst_in;auto.
        setoid_rewrite act_lists_app;rewrite act_lists_cons;simpl.
        unfold act at 2,act_pair;simpl;rewrite <- In_act_lists in I.
        etransitivity;[|apply rmfst_in;eauto].
        repeat f_equal;apply act_p_pinv.
      - rewrite rmfst_notin,rmfst_notin;auto.
        rewrite In_act_lists;apply I.
    Qed.

    (** If two permutations coincide on the support of [x], then applying either to [x] yields the same result. *)
    Lemma support_eq_action_eq p q (x : A) :
      (forall a, a ∈⌊x⌋ -> p ∙ a = q ∙ a) -> p ∙ x = q ∙ x.
    Proof.
      intro hyp;rewrite <- (act_bij (q∗)), act_pinv_p,action_compose.
      apply action_invariant,map_eq_id.
      intros a I; rewrite <-action_compose,(hyp a I).
      apply inverse_comp_l.
    Qed.

    (** Simplification lemma. *)
    Lemma act_cons_a_a :
      forall (a : atom) p (x : A), ((a,a)::p) ∙ x = p ∙ x.
    Proof.
      intros a π x.
      replace ((a,a)::π) with ([(a,a)]++π) by reflexivity.
      rewrite <- action_compose,perm_a_a_eq_nil,act_nil;reflexivity.
    Qed.
    
    Context {B : Set} `{Nominal B}.

    (** The function [p∙] distributes over [⊗]. *)
    Lemma combine_act p (l : list A)(m : list B) : p ∙ (l⊗m) = (p∙l)⊗(p∙m).
    Proof.
      revert m;induction l as [|a l];intros [|b m];simpl;auto.
      rewrite act_lists_cons;f_equal;apply IHl.
    Qed.
  End group.
  
  (** * Minimality of support *)
  
  (** If a list [l] supports an element [x], then [⌊x⌋] is contained in [l]. *)
  Lemma minimal_support {X: Set} `{Nominal X} l x :
    (forall π, (forall a, a ∈ l -> π ∙ a = a) -> π ∙ x = x) -> ⌊x⌋ ⊆ l.
  Proof.
    intros s a Ia.
    case_in a l;[tauto|exfalso].
    destruct (exists_fresh (a::l++⌊x⌋)) as (b&hb).
    simpl_In in hb.
    assert (E: [(a,b)]∙x=x).
    - apply s;intros c Ic.
      apply elements_inv_act_atom;simpl.
      intros [->|[->|F]];tauto.
    - pose proof (support_action x [(a,b)]) as E'.
      rewrite E in E';revert Ia.
      rewrite E',In_act_lists.
      unfold act,act_atom;simpl;simpl_beq.
      tauto.                  
  Qed.

  (** * Useful remarks *)
  (** If [l] is a list of atoms, then it is equivalent to its support. *)
  Remark support_list_atoms (l : list atom) : ⌊l⌋ ≈ l.
  Proof.
    intros a;rewrite In_support_list.
    unfold support,SupportAtom;simpl;firstorder subst;auto.
  Qed.

  (** The action of [p] on its list of elements yields an equivalent list. *)
  Remark elements_act_lists p : elements p ≈ p∙(elements p).
  Proof.
    intro a;split;auto.
    - intro elt;simpl_In.
      case_in (p∗∙a) (elements p);auto.
      + apply In_act_lists,I.
      + apply In_act_lists.
        apply elements_inv_act_atom in I;rewrite <- I,inverse_comp_r;auto.
    - simpl_In;intro elt.
      case_in a (elements p);auto.
      apply elements_inv_act_atom in I;rewrite <-I,In_act_lists,inverse_comp_l in elt;auto.
  Qed.

  (** The number of occurrences of [a] in [p∙l] is the number of occurrences of [p∗∙a] in [l]. *)
  Remark nb_act {A} `{Nominal A,decidable_set A} (a : A) l p :
    nb a (p∙l) = nb (p∗∙a) l.
  Proof.
    induction l as [|b l];auto.
    rewrite act_lists_cons;simpl.
    destruct_eqX a (p∙b);simpl.
    - rewrite act_pinv_p in *;simpl_beq;rewrite IHl;reflexivity.
    - rewrite <- act_bij with (p0:=p∗) in N.
      rewrite act_pinv_p in N;simpl_beq;auto.
  Qed.

  (** The functions [{{_}}], [prj1], and [prj2] commute with the action of permutations. *)
  Lemma undup_act {A : Set} `{decidable_set A,Nominal A}
        (l : list A) (π : perm) : {{π∙l}} = π∙{{l}}.
  Proof.
    induction l as [|a l].
    - reflexivity.
    - simpl;replace (act_lists π l) with (π ∙ l) in * by reflexivity.
      case_in a {{l}};case_in (π∙a) {{π ∙ l}}.
      + apply IHl.
      + rewrite undup_equivalent,In_act_lists,act_pinv_p,<-undup_equivalent in I0;tauto.
      + rewrite undup_equivalent,In_act_lists,act_pinv_p,<-undup_equivalent in I0;tauto.
      + rewrite IHl;reflexivity.
  Qed.

  Lemma proj1_act {A B : Set} `{Nominal A,Nominal B} (l : list (A*B)) π :
    π∙(prj1 l) = prj1 (π∙l).
  Proof.
    unfold act,act_lists;repeat rewrite map_map.
    apply map_ext;intros (a,b);reflexivity.
  Qed.

  Lemma proj2_act {A B : Set} `{Nominal A,Nominal B} (l : list (A*B)) π :
    π∙(prj2 l) = prj2 (π∙l).
  Proof.
    unfold act,act_lists;repeat rewrite map_map.
    apply map_ext;intros (a,b);reflexivity.
  Qed.

  (** Applying permutations preserves duplication-freeness. *)
  Lemma NoDup_act  {A : Set} `{Nominal A} (l : list A) (π : perm) :
    NoDup l -> NoDup (π∙l).
  Proof.
    intro;apply NoDup_map_injective;[|tauto].
    split;apply act_bij.
  Qed.

  (** For any permutation [π], the function [π∙_] is injective and surjective. *)
  Global Instance injective_perm {A} `{Nominal A} π : injective (act π).
  Proof. split;intros x y;apply act_bij. Qed.
  Global Instance surjective_perm {A} `{Nominal A} π : surjective (act π).
  Proof. split;intros x;exists (π∗∙x);apply act_p_pinv. Qed.

  (** The function [π∙_] is supported, and its support can be computed from the elements of [π]. *)
  Global Instance has_support_perm (π : perm) :
    has_support (act π) ((fun a => negb (π∙a =?=a)) :> elements π).
  Proof.
    split;intros x;simpl_In.
    rewrite negb_true_iff,eqX_false;split;[|tauto].
    intro h;split;auto.
    case_in x (elements π);auto.
    exfalso;apply elements_inv_act_atom in I;tauto.
  Qed.
  Hint Resolve injective_perm surjective_perm has_support_perm.

  (** The [group_by_fst] function commutes with group actions. *)
  Lemma group_by_fst_act
        {A B : Set} `{Nominal A,Nominal B} `{decidable_set A} :
    forall (l : list (A*B)) π, π ∙ (group_by_fst l) = group_by_fst (π∙l).
  Proof.
    intros l π.
    unfold group_by_fst .
    rewrite <- proj1_act,undup_act.
    unfold act at 1 3,act_lists;repeat rewrite map_map.
    apply map_ext_in;intros x' I.
    simpl_In in I;apply in_map_iff in I as ((x&y)&<-&I);simpl.
    unfold act at 1 4.
    rewrite filter_map,map_map,map_map.
    etransitivity;[apply map_ext|f_equal;[reflexivity|]].
    - clear;intros (x,y);reflexivity.
    - apply filter_ext;unfold Basics.compose.
      intros (x'&y');simpl.
      apply eq_iff_eq_true;repeat rewrite eqX_correct;rewrite act_bij;reflexivity.
  Qed.

  Remark reform {N} `{Nominal N} (l : list N) π :
    map (act π) l = π∙l.
  Proof. reflexivity. Qed.

  Remark act_eq_equivalent {N} `{Nominal N} (π π': perm) (l m : list N) :
    l ≈ m -> π ∙ m = π' ∙ m <-> π ∙ l = π' ∙ l.
  Proof. intros E;apply (map_eq_equivalent _ _ E). Qed.

  Global Instance equivalent_act {N} `{Nominal N} :
    Proper (sequiv ==> (@equivalent N) ==> (@equivalent N)) act.
  Proof.
    intros π1 π2 E l1 l2 E' a.
    repeat rewrite In_act_lists.
    rewrite E'.
    apply equiv_perm_inverse in E;rewrite E.
    reflexivity.
  Qed.
    
  (** * Equivariant functions *)
  (** A function between two nominal sets is equivalent if it commutes with the group actions. *)
  Class Equivariant {A B} `{Nominal A,Nominal B} (f : A -> B) :=
    equivariant : forall a p, p∙(f a) = f (p∙a).

  (** If [f] is equivariant, then the support of [f x] is contained in that of [x]. *)
  Lemma support_image_equivariant {A B : Set}`{Nominal A,Nominal B} :
    forall (f : A -> B) x, Equivariant f -> ⌊f x⌋ ⊆ ⌊x⌋.
  Proof.
    intros f x E a I.
    case_in a ⌊x⌋;auto;exfalso.
    destruct (exists_fresh (a::⌊x⌋++⌊f x⌋)) as (b&Ib).
    simpl in Ib;rewrite in_app_iff in Ib.
    pose proof (E x [(a,b)]).
    replace ([(a,b)]∙x) with x in H1.
    - revert I;rewrite <- H1,support_action,In_act_lists.
      simpl;unfold act,act_atom;simpl; simpl_beq;tauto.
    - symmetry;apply elements_inv_act.
      intros c Ic [F|[F|F]];simpl in *;subst;tauto.
  Qed.

End perm.

(* begin hide *)
Arguments Nominal {atom} Atoms S {action supp}.
Arguments Support {atom} Atoms T.
Arguments Action {atom} Atoms X.

Notation " ⌊ e ⌋ " := (support e).
Infix " ∙ " := act (at level 20).
Notation "p ∗" := (inverse p) (at level 35).
Notation " a # x " := (~ a ∈ ⌊x⌋) (at level 80).
  
Hint Resolve injective_perm surjective_perm has_support_perm.

Ltac solve_length :=
  repeat (rewrite app_length in * )
  || (rewrite map_length in * )
  || (rewrite act_lists_length in * )
  || (simpl in * ); lia.
(* end hide *)