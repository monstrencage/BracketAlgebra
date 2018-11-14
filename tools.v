(** * RIS.tools : Toolbox of simple definitions, lemmas and tactics. *)

Require Export Eqdep Setoid Morphisms Psatz List.
Require Import Bool.
Export ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Infix " ∘ " := Basics.compose (at level 40).
Hint Unfold Basics.compose.
Notation " $ o " := (proj1_sig o) (at level 0).

(** * Notations for equivalence relations and partial orders *)

(** Typeclass and notation for axiomatic equivalence relations. *)
Class Equiv (A : Set) := equiv : relation A.
Notation " e ≡ f " := (equiv e f) (at level 80).

(** Typeclass and notation for semantic equivalence relations. *)
Class SemEquiv (A : Type) := sequiv : relation A.
Notation " e ≃ f " := (sequiv e f) (at level 80).

(** Typeclass and notation for axiomatic preorder relations. *)
Class Smaller (A : Set) := smaller : relation A.
Notation " e ≤ f " := (smaller e f) (at level 80).

(** Typeclass and notation for semantic preorder relations. *)
Class SemSmaller (A : Type) := ssmaller : relation A.
Notation " e ≲ f " := (ssmaller e f) (at level 80).

(** * Decidable sets *)

(** The class of [decidable_set X] contains a binary function associating to every pair of elements of type [X] a boolean and a proof that this function encodes faithfully equality over [X]. *)
Class decidable_set X :=
  { eqX : X -> X -> bool;
    eqX_eq : forall x y, reflect (x = y) (eqX x y)}.

Infix " =?= " := eqX (at level 20).

Section decidable.
  Context { X : Set }.
  Context { D : decidable_set X }.
 
  (** This lemma is the preferred way of translating back and forth between boolean and propositional equality. *)
  Lemma eqX_correct : forall x y : X, eqX x y = true <-> x = y.
  Proof. intros;symmetry;apply reflect_iff,eqX_eq. Qed.

  (** The next few lemmas are useful on occasion.  *)
  Lemma eqX_false : forall x y, eqX x y = false <-> x <> y.
  Proof. intros;rewrite<-(eqX_correct _),not_true_iff_false;tauto. Qed.

  Lemma X_dec (x y : X) : {x = y} + {x <> y}.
  Proof.
    case_eq (eqX x y).
    - now intro h;left;apply (eqX_correct _).
    - intro h;right;intro E;apply (eqX_correct _) in E.
      contradict E;rewrite h;auto.
  Qed.

  Lemma eqX_refl x : eqX x x = true.
  Proof. apply eqX_correct;reflexivity. Qed.

End decidable.

(* begin hide *)
Ltac destruct_eqX x o :=
  let Ei := fresh "E" in
  let Ni := fresh "N" in
  let X := fresh "X" in
  destruct (@X_dec _ _ x o) as [Ei |Ni];
  [pose proof Ei as X;apply (@eqX_correct _ _) in X;
   try rewrite Ei in *
  |pose proof Ni as X;apply (@eqX_false _ _) in X];
  repeat rewrite X in *;repeat rewrite eqX_refl in *;clear X.

Ltac simpl_beq :=
  match goal with
  | [h: ?a <> ?b |- _] =>
    let E := fresh "E" in
    pose h as E;apply eqX_false in E;rewrite E in *;clear E
  | [h: ?a <> ?b |- _] =>
    let E := fresh "E" in
    assert (E:b<>a) by (intros E;apply h;rewrite E;reflexivity);
    apply eqX_false in E;rewrite E in *;clear E
  | _ => rewrite eqX_refl in *
  end.
Ltac simpl_eqX :=
  repeat
    simpl_beq
  || match goal with
    | [ |- context[?x =?= ?o]] =>
      let Ei := fresh "E" in
      let Ni := fresh "N" in
      let X := fresh "X" in
      destruct (@X_dec _ _ x o) as [Ei |Ni];
      [pose proof Ei as X;apply (@eqX_correct _ _) in X;
       try rewrite Ei in *;tauto||discriminate
      |pose proof Ni as X;apply (@eqX_false _ _) in X];
      repeat rewrite X in *;repeat rewrite eqX_refl in *;clear X
    end.
Ltac unfold_eqX :=
  repeat
    simpl_beq
  || match goal with
    | [ |- context[?x =?= ?o]] =>
      let Ei := fresh "E" in
      let Ni := fresh "N" in
      let X := fresh "X" in
      destruct (@X_dec _ _ x o) as [Ei |Ni];
      [pose proof Ei as X;apply (@eqX_correct _ _) in X;
       try rewrite Ei in *
      |pose proof Ni as X;apply (@eqX_false _ _) in X];
      repeat rewrite X in *;repeat rewrite eqX_refl in *;clear X
    end.
(* end hide *)
  
(** The set of natural numbers is decidable. *)
Global Instance NatNum : decidable_set nat :=
  Build_decidable_set PeanoNat.Nat.eqb_spec.


(** The set of natural booleans is decidable. *)
Global Instance Boolean : decidable_set bool.
Proof.
  cut (forall x y, reflect (x = y) (eqb x y));
  [apply Build_decidable_set|].
  intros;apply iff_reflect;symmetry;apply eqb_true_iff.
Qed.

(** If [A] and [B] are decidable, then so is their Cartesian product. *)
Global Instance dec_prod A B :
  decidable_set A -> decidable_set B -> decidable_set (A*B).
Proof.
  intros d1 d2.
  set (eqp := fun x y =>
                (@eqX _ d1 (fst x) (fst y))
                  && (@eqX _ d2 (snd x) (snd y))).
  assert (eqp_spec : forall x y, reflect (x=y) (eqp x y));
    [|apply (Build_decidable_set eqp_spec)].
  intros (x1,x2) (y1,y2);unfold eqp;simpl;
  destruct (@eqX_eq _ d1 x1 y1);destruct (@eqX_eq _ d2 x2 y2);
  apply ReflectT||apply ReflectF;
  (rewrite e,e0;reflexivity)||(intro h;inversion h;tauto).
Qed.

(** If [A] and [B] are decidable, then so is their sum. *)
Global Instance dec_sum A B :
  decidable_set A -> decidable_set B -> decidable_set (A+B).
Proof.
  intros d1 d2.
  set (eqp := fun (x y : A+B) =>
                match (x,y) with
                | (inl _,inr _) | (inr _,inl _) => false
                | (inl a,inl b) => a =?= b
                | (inr a,inr b) => a =?= b
                end).
  assert (eqp_spec : forall x y, reflect (x=y) (eqp x y));
    [|apply (Build_decidable_set eqp_spec)].
  intros [x|x] [y|y];unfold eqp;simpl.
  - destruct (@eqX_eq _ d1 x y).
    + apply ReflectT;subst;auto.
    + apply ReflectF;intro h;inversion h;tauto.
  - apply ReflectF;discriminate.
  - apply ReflectF;discriminate.
  - destruct (@eqX_eq _ d2 x y).
    + apply ReflectT;subst;auto.
    + apply ReflectF;intro h;inversion h;tauto.
Qed.

(** If [A] is decidable, then so is [option A]. *)
Global Instance dec_option (A : Set) :
  decidable_set A -> decidable_set (option A).
Proof.
  intros d1.
  set (eqlbl :=
         fun l1 l2 : option A =>
           match (l1,l2) with
           | (None,None) => true
           | (Some x,Some y) => eqX x y
           | _ => false
           end).
  exists eqlbl;intros [|] [|];apply iff_reflect;unfold eqlbl;simpl;split;
    try discriminate || tauto.
  * intros E;inversion E; apply eqX_refl.
  * rewrite eqX_correct;intros ->;reflexivity.
Qed.

(** * Binary relations *)
Section relations.
  Context {A : Set}.
  (** We define semantic (in)equality for binary relations in the usual way. *)
  Global Instance eqRel : SemEquiv (relation A) :=
    (fun r s => forall x y, r x y <-> s x y).

  Global Instance infRel : SemSmaller (relation A) :=
    (fun r s => forall x y, r x y -> s x y).

  (** Semantic equality is an equivalence relation, inequality is a partial order. *)
  Global Instance eqRel_Equivalence : Equivalence (@sequiv _ eqRel).
  Proof.
    split;intro;unfold sequiv,eqRel;firstorder.
    - apply H0,H;auto.
    - apply H,H0;auto.
  Qed.

  Global Instance infRel_PreOrder : PreOrder (@ssmaller _ infRel).
  Proof. split;intro;unfold ssmaller,infRel;firstorder. Qed.

  Global Instance infRel_PartialOrder : PartialOrder sequiv (@ssmaller _ infRel).
  Proof. split;intro;unfold ssmaller,infRel;firstorder. Qed.

  (** The product of two relations is their sequential composition. *)
  Definition product (r s : relation A) : relation A :=
    fun x y => exists z, r x z /\ s z y.

  Infix " ⨾ " := product (at level 40).

  (** [Δ] is the identity relation, also called diagonal. *)
  Definition Δ : relation A := fun x y => x = y.

  (** [≃] (reps. [≲]) is a congruence (resp pre-congruence) with respect to [⨾]. *)
  Global Instance product_eqRel : Proper (sequiv==>sequiv==>sequiv) product.
  Proof. intros r r' Er s s' Es x y;split;intros (z&R1&R2);exists z;split;apply Er||apply Es;auto. Qed.
  
  Global Instance product_infRel : Proper (ssmaller==>ssmaller==>ssmaller) product.
  Proof. intros r r' Er s s' Es x y;intros (z&R1&R2);exists z;split;apply Er||apply Es;auto. Qed.

  (** Relations equipped with [⨾] and [Δ] form a monoid. *)
  Lemma product_assoc (r s t : relation A) : (r ⨾ s)⨾ t ≃ r ⨾ (s ⨾ t).
  Proof.
    intros x y;split.
    - intros (z&(z'&Ir&Is)&It);exists z';split;auto;exists z;auto.
    - intros (z&Ir&(z'&Is&It));exists z';split;auto;exists z;auto.
  Qed.

  Lemma product_Δ (r : relation A) : r ⨾ Δ ≃ r.
  Proof.
    intros x y;split.
    - intros (z & R & ->);auto.
    - intro R;exists y;split;auto.
      reflexivity.
  Qed.
  Lemma Δ_product (r : relation A) : Δ ⨾ r ≃ r.
  Proof.
    intros x y;split.
    - intros (z & <- & R);auto.
    - intro R;exists x;split;auto.
      reflexivity.
  Qed.

  (** Let [X] be a set. *)
  Context {X : Set}.
  (** Any map [σ : X -> relation A] may be uniquely extended into a monoid homomorphism [mapRel σ] from [list X] to [relation A]. *)
  Definition mapRel (σ : X -> relation A) (u : list X) :=
    fold_right (fun l r => σ l ⨾ r) Δ u.

  Lemma mapRel_nil σ : mapRel σ [] = Δ.
  Proof. reflexivity. Qed.
  
  Lemma mapRel_app σ (u v : list X) : mapRel σ (u++v) ≃ mapRel σ u ⨾ mapRel σ v.
  Proof.
    induction u;simpl.
    - symmetry;apply Δ_product.
    - rewrite IHu;symmetry;apply product_assoc.
  Qed.

  Lemma mapRel_unique σ h :
    (forall a, h [a] ≃ σ a) -> (h [] ≃ Δ) -> (forall u v, h (u++v) = h u ⨾ h v) ->
    forall u, h u ≃ mapRel σ u.
  Proof.
    intros ha hnil happ;induction u.
    - rewrite hnil;reflexivity.
    - simpl;rewrite <- IHu,<- ha,<-happ;simpl;reflexivity.
  Qed.
  
  Remark mapRel_add σ u a : mapRel σ (u++[a]) ≃ mapRel σ u ⨾ σ a.
  Proof. rewrite mapRel_app;simpl;rewrite product_Δ;reflexivity. Qed.
  
End relations.
Infix " ⨾ " := product (at level 40).

(** * Lists *)
(** ** Notations *)
(** We associate the traditional containment symbol to list inclusion. *)
Infix " ⊆ " := incl (at level 80).

(** We use the following symbol to denote the membership predicate. *)
Infix " ∈ " := In (at level 60).

(** We'll write [P :> l] for the list [l] where we've removed elements that do not satisfy the boolean predicate [P]. *)
Infix " :> " := filter (at level 50).

(** The length of the list [l] is denoted by [⎢l⎥]. *)
Notation "⎢ l ⎥" := (length l).

(** ** Induction principles *)

(** Induction principle for lists in the reverse order. *)
Lemma rev_induction {A} (P : list A -> Prop) :
  P [] -> (forall a l, P l -> P (l++[a])) -> forall l, P l.
Proof.
  intros;rewrite <- rev_involutive;induction (rev l);simpl;auto.
Qed.

(** Strong induction on the length of a list. *)
Lemma len_induction {A} (P : list A -> Prop) :
  P [] -> (forall a l, (forall m, ⎢m⎥ <= ⎢l⎥ -> P m) -> P (a::l)) -> forall l, P l.
Proof.
  intros h0 hn l;remember ⎢l⎥ as N.
  assert (len:⎢l⎥ <= N) by lia.
  clear HeqN;revert l len;induction N.
  - intros [|a l];simpl;try lia;auto.
  - intros [|a l];simpl;auto.
    intro len;apply hn;intros m;simpl;intros len'.
    apply IHN;lia.
Qed.

(** Strong induction on the length of a list, taken in the reverse order. *)
Lemma len_rev_induction {A} (P : list A -> Prop) :
  P [] -> (forall a l, (forall m, ⎢m⎥ <= ⎢l⎥ -> P m) -> P (l++[a])) -> forall l, P l.
Proof.
  intros h0 hn l;remember ⎢l⎥ as N.
  assert (len:⎢l⎥ <= N) by lia.
  clear HeqN;revert l len;induction N.
  - intros [|a l];simpl;try lia;auto.
  - intros l0;case_eq l0;[intros->;simpl;auto|].
    intros a0 l0' _;destruct (@exists_last _ (a0::l0')) as (l&a&->);[discriminate|].
    rewrite app_length;simpl;intro len;apply hn;intros m;simpl;intros len'.
    apply IHN;lia.
Qed.

(** ** General lemmas *)
(** A list is not empty if and only if it has a last element. *)
Lemma not_nil_add {A} (v : list A) : v <> [] <-> exists u l, v = u++[l].
Proof.
  split.
  - induction v;try tauto.
    intros _;destruct v.
    + exists [];exists a;reflexivity.
    + destruct IHv as (u&x&->);try discriminate.
      exists (a::u),x;split.
  - intros (u&l&E) -> .
    apply app_cons_not_nil in E;auto.
Qed.

(** A list is either empty or can be decomposed with its last element apparent.*)
Lemma nil_or_last {A} (v : list A) : {v = []} + {exists a v', v = v'++[a]}.
Proof.
  induction v.
  - left;reflexivity.
  - right;destruct IHv as [->|(b&v'&->)].
    + exists a,[];reflexivity.
    + exists b,(a::v');reflexivity.
Qed.

(** If the list [l++a::l'] is duplicate free, so are [l] and [l']. *)
Lemma NoDup_remove_3 {A} (l l' : list A) (a : A) :
    NoDup (l ++ a :: l') -> NoDup l /\ NoDup l'.
Proof.
  revert l' a;induction l;intros l' b;simpl;
    repeat rewrite NoDup_cons_iff.
  - intros (_&h);split;auto;apply NoDup_nil.
  - rewrite in_app_iff;intros (N&hyp);apply IHl in hyp as (h1&h2);
      repeat split;auto.
Qed.

(** Filtering a concatenation is the same as concatenating filters. *)
Lemma filter_app {A} (f : A -> bool) (l m : list A) :
  f :> (l++m) = f :> l ++ f :> m.
Proof.
  induction l;simpl;auto.
  destruct (f a);simpl;auto.
  f_equal;auto.
Qed.

(** Filtering reduces the length of the list. *)
Lemma filter_length {A} (f : A -> bool) l :
  ⎢f :> l⎥ <= ⎢l⎥ .
Proof.
  induction l;simpl;auto.
  destruct (f a);simpl;lia.
Qed.

(** The following lemma give a more precise description. *)
Lemma filter_length_eq {A} (f : A -> bool) l :
  ⎢f :> l⎥ + ⎢(fun x => negb (f x)) :> l⎥ = ⎢l⎥ .
Proof.
  induction l;simpl;auto.
  destruct (f a);simpl;lia.
Qed.

(** [filter] and [map] commute. *)
Lemma filter_map {A B} (f : A -> bool) (g : B -> A) l :
  f :> (map g l) = map g ((f∘g) :> l).
Proof.
  induction l;simpl;auto.
  unfold Basics.compose;destruct (f (g a));simpl;auto.
  f_equal;auto.
Qed.

(** [filter] only depends on the values of the filtering function, not its implementation. *)
Lemma filter_ext_In {A} (f g : A -> bool) l :
  (forall x, x ∈ l -> f x = g x) -> f :> l = g :> l.
Proof.
  intro hyp;induction l as [|x l];simpl;auto.
  case_eq (f x);case_eq (g x).
  - intros _ _; f_equal;apply IHl;intros y I;apply hyp;now right.
  - intros h1 h2;exfalso.
    cut (true=false);[discriminate|].
    rewrite <-h1,<-h2;apply hyp;now left.
  - intros h1 h2;exfalso.
    cut (true=false);[discriminate|symmetry].
    rewrite <-h1,<-h2;apply hyp;now left.
  - intros _ _;apply IHl;intros y I;apply hyp;now right.
Qed.

Lemma filter_ext {A} (f g : A -> bool) l :
  (forall x, f x = g x) -> f :> l = g :> l.
Proof. intros hyp;apply filter_ext_In;intros x _;apply hyp. Qed.

(** Filtering with the predicate [true] does not modify the list. *)
Lemma filter_true {A} (l : list A) :
  (fun _ => true) :> l = l.
Proof. induction l;simpl;auto;congruence. Qed.

(** Filtering preserves the property [NoDup] (absence of duplicates). *)
Lemma filter_NoDup {A} (f : A -> bool) l :
  NoDup l -> NoDup (f :> l).
Proof.
  induction l;simpl;auto.
  destruct (f a);repeat rewrite NoDup_cons_iff;
    try rewrite filter_In;tauto.
Qed.

(** A filtered list [P :> l] is empty if and only if [P x] is [false] for every element [x∈l]. *)
Lemma filter_nil {A} (P : A -> bool) l :
  P:>l = [] <-> forall a, a ∈ l -> P a = false.
Proof.
  induction l;simpl;[tauto|].
  case_eq (P a);intro E.
  - split;[discriminate|].
    intro h;exfalso;pose proof (h a) as F;rewrite E in F.
    intuition discriminate.
  - rewrite IHl;clear IHl;firstorder subst;auto.
Qed.
  
(** If two concatenations are equal, and if the two initial factors have the same length, then the factors are equal. *)
Lemma length_app {A} (l1 l2 m1 m2 : list A) :
  ⎢l1⎥ = ⎢m1⎥ -> l1++l2 = m1++m2 -> l1 = m1 /\ l2 = m2.
Proof.
  intros El Ea.
  cut (l1 = m1).
  - intros ->;split;auto.
    eapply app_inv_head,Ea.
  - transitivity (firstn ⎢l1⎥ (l1++l2)).
    + rewrite firstn_app,PeanoNat.Nat.sub_diag;simpl.
      rewrite app_nil_r,firstn_all;reflexivity.
    + rewrite Ea,El.
      rewrite firstn_app,PeanoNat.Nat.sub_diag;simpl.
      rewrite app_nil_r,firstn_all;reflexivity.
Qed.

(** If two concatenations are equal, and if the two final factors have the same length, then the factors are equal. *)
Lemma length_app_tail {A} (l1 l2 m1 m2 : list A) :
  ⎢l2⎥ = ⎢m2⎥ -> l1++l2 = m1++m2 -> l1 = m1 /\ l2 = m2.
Proof.
  intros L;revert m1;induction l1;intros [|b m];simpl;auto.
  - intros ->;exfalso;simpl in L;rewrite app_length in L;lia.
  - intros <-;exfalso;simpl in L;rewrite app_length in L;lia.
  - intro E;inversion E as [[Ea El]];apply IHl1 in El as (->&->);auto.
Qed.

(** If two concatenations are equal, and the first initial factor is
smaller than the second one, we can find a unifying factor [w]. *)
Lemma app_eq_app_length {A : Set} (u1 u2 v1 v2 : list A) :
  u1++u2 = v1 ++ v2 -> ⎢u1⎥ <= ⎢v1⎥ -> exists w, v1 = u1++w /\ u2 = w++v2.
Proof.
  set (k:= ⎢v1⎥ - ⎢u1⎥ ).
  intros E L.
  assert (EL : ⎢u1 ++ u2⎥ = ⎢v1 ++ v2⎥) by (rewrite E;reflexivity).
  repeat rewrite app_length in EL.
  rewrite <- (firstn_skipn k u2) in E.
  rewrite <- (firstn_skipn k u2).
  rewrite <-app_ass in E.
  apply length_app in E as (E1 & E2).
  - rewrite <-E1, <-E2;eexists;eauto.
  - rewrite app_length,firstn_length_le;unfold k;lia.
Qed.

(** If two concatenations are equal, we can always find a unifying factor. *)
Lemma Levi {A:Set} (u1 u2 v1 v2 : list A) :
  u1++u2 = v1++v2 -> exists w, (u1=v1++w /\ v2=w++u2) \/ (v1=u1++w /\ u2=w++v2).
Proof.
  intro E;destruct (Compare_dec.le_lt_dec ⎢u1⎥ ⎢v1⎥ ) as [L|L].
  - apply (app_eq_app_length E) in L as (w&->&->).
    exists w;right;auto.
  - symmetry in E;apply app_eq_app_length in E as (w&->&->);[|lia].
    exists w;left;auto.
Qed.

(** This next lemma makes the unifying factor unambiguous. *)
Lemma Levi_strict {A:Set} (u1 u2 v1 v2 : list A) :
  u1++u2 = v1++v2 -> (u1 = v1 /\ u2 = v2)
                    \/ exists a w, (u1=v1++a::w /\ v2=a::w++u2) \/ (v1=u1++a::w /\ u2=a::w++v2).
Proof.
  intro E;destruct (Compare_dec.le_lt_dec ⎢u1⎥ ⎢v1⎥ ) as [L|L];
    [apply Compare_dec.le_lt_eq_dec in L as [L|L]|].
  - apply app_eq_app_length in E as (w&->&->);[|lia].
    rewrite app_length in L;destruct w as [|a w];[simpl in L;lia|].
    right;exists a,w;right;auto.
  - apply length_app in E;tauto.
  - symmetry in E;apply app_eq_app_length in E as (w&->&->);[|lia].
    rewrite app_length in L;destruct w as [|a w];[simpl in L;lia|].
    right;exists a,w;left;auto.
Qed.

(** If the concatenation of two lists is duplication free, then so are they. *)
Lemma NoDup_app_inv {X:Set} : forall (l m : list X),
    NoDup (l++m) -> NoDup l /\ NoDup m.
Proof.
  induction l;simpl;intros m nd.
  - split;auto using NoDup_nil.
  - rewrite NoDup_cons_iff in *;rewrite in_app_iff in nd.
    firstorder.
Qed.

(** If [l] and [m] don't share any element, then if both of them don't have duplication their concatenation won't either. *)
Lemma NoDup_app {X : Set} l m:
  (forall a : X, a ∈ l -> ~ a ∈ m) -> NoDup l ->  NoDup m -> NoDup (l++m).
Proof.
  intros h1 h2 h3;revert h2 m h3 h1; induction l.
  - simpl;intros;auto.
  - intros hl m hm h; inversion hl.
    simpl;apply NoDup_cons;auto.
    + rewrite in_app_iff;firstorder.
    + apply IHl;firstorder.
Qed.

(** If the boolean predicate [forallb f l] is false, then me may extract a counter-example, that is an element in the list [l] where the predicate [f] is false. *)
Lemma forallb_false_exists {A} f (l:list A) :
  forallb f l = false <-> exists a, a ∈ l /\ f a = false.
Proof.
  induction l;simpl.
  - split;[discriminate|firstorder].
  - rewrite andb_false_iff,IHl;split.
    + intros [h|(b&I&h)].
      * exists a;auto.
      * exists b;auto.
    + intros (b&[<-|I]&h);firstorder.
Qed.

(** [l] appears in the list [concat m] exactly when there is a list [L] in [m] such that [l] appears in [L]. *)
Lemma in_concat {A : Set} l (m : list (list A)) :
  l ∈ concat m <-> exists L, L ∈ m /\ l ∈ L.
Proof.
  induction m as [|L m].
  - simpl;firstorder.
  - simpl;rewrite in_app_iff,IHm;clear;firstorder (subst;tauto).
Qed.

(** If [map f m] can be split into [l1++l2], then we may split [l] into [m1++m2] accordingly. *)
Lemma map_app_inverse {A B} (f : A -> B) m l1 l2 :
  map f m = l1 ++ l2 -> exists m1 m2, l1 = map f m1 /\ l2 = map f m2 /\ m = m1 ++ m2.
Proof.
  revert m;induction l1 as [|a l1];intros l E;simpl in *.
  - exists [],l;split;auto.
  - destruct l as [|b l];simpl in E;inversion E.
    apply IHl1 in H1 as (m1&m2&->&->&->).
    exists (b::m1),m2;repeat split;auto.
Qed.

(** [lift_prod f] is the pointwise extension of the binary operation [f] over [A] into a binary operation over [list A].  *)
Definition lift_prod {A: Set} (f : A -> A -> A) : list A -> list A -> list A :=
  fun l m => flat_map (fun a => map (f a) m) l.

Lemma lift_prod_spec {A:Set} f (l m : list A) :
  forall c, c ∈ lift_prod f l m <-> exists a b, a ∈ l /\ b ∈ m /\ c = f a b.
Proof. intro c; unfold lift_prod;rewrite in_flat_map;setoid_rewrite in_map_iff;firstorder. Qed.

Lemma incl_map {A B:Set} (f : A -> B) l m : l ⊆ map f m -> exists n, l = map f n /\ n ⊆ m.
Proof.
  induction l as [|a l].
  - intros _;exists [];split;[reflexivity|intro;simpl;tauto].
  - intros I.
    assert (Ia : a ∈ (a :: l)) by (now left).
    apply I,in_map_iff in Ia as (b&<-&Ib).
    destruct IHl as (n&->&I').
    + intros x Ix;apply I;now right.
    + exists (b::n);split;[reflexivity|].
      apply incl_cons;tauto.
Qed.

(** ** Lists of pairs *)
(** We introduce some notations for lists of pairs: [prj1 l] is the list obtained by applying pointwise to [l] the function [fun (x,y) => x]. *)
Notation prj1 := (map fst).
(** Similarly, [prj2 l] is the list obtained by applying pointwise to [l] the function [fun (x,y) => y]. *)
Notation prj2 := (map snd).

(** If the a projection of [l] is equal to a projection of [m], then they have the same length. *)
Lemma proj_length {A B C} (l : list (A*B)) (m:list (B*C)) : prj2 l = prj1 m -> ⎢l⎥=⎢m⎥.
Proof. intro E;rewrite<-(map_length snd),E,map_length;auto. Qed.

(** *** Combine *)
Section combine.
  Context {A B : Set}.
  Context {l1 l3 : list A} {l2 l4: list B} {l: list (A*B)}.
  Hypothesis same_length : ⎢l1⎥ = ⎢l2⎥.
  
  (** The combine function can be described by the following recursive definition : 
      - [[]⊗l = l⊗[] = []];
      - [(a::l)⊗(b::m)=(a,b)::(l⊗m)].
      In the following, we will only use [l⊗m] when [l] and [m] have the same length.
   *)
  Infix "⊗" := combine (at level 50).

  (** The first projection of [l1 ⊗ l2] is [l1]. *)
  Lemma combine_fst : prj1 (l1 ⊗ l2) = l1.
  Proof.
    revert l2 same_length;induction l1 as [|a l0];intros [|c l2];try (simpl;lia). 
    - intros _;reflexivity.
    - simpl;intros L.
      rewrite IHl0;auto.
  Qed.

  (** The second projection of [l1 ⊗ l2] is [l2]. *)
  Lemma combine_snd : prj2 (l1 ⊗ l2) = l2.
  Proof.
    revert l2 same_length;induction l1 as [|a l0];intros [|b l2];try (simpl;lia).
    - intros _;reflexivity.
    - simpl;intros L.
      rewrite IHl0;auto.
  Qed.

  (** A combination of concatenations is the concatenation of combinations (assuming the first arguments of both concatenations have the same length). *)
  Lemma combine_app : (l1++l3) ⊗ (l2++l4) = l1 ⊗ l2 ++ l3 ⊗ l4.
  Proof.
    revert l2 l3 l4 same_length;induction l1 as [|a l0];intros [|b l2] l3 l4;try (simpl;lia).
    - intros _;reflexivity.
    - simpl;intros L;f_equal.
      rewrite IHl0;auto.
  Qed.

  (** Every list of pairs can be expressed as the combination of its first and second components. *)
  Lemma combine_split : l = (prj1 l) ⊗ (prj2 l).
  Proof. induction l as [|(a,b)l'];simpl;auto;f_equal;auto. Qed.

End combine.
Infix "⊗" := combine (at level 50).

(** *** Mix *)
Section mix.
  Context {A B : Set} {s1 s2 s3 s4 : list (A*B)}.
  Hypothesis same_length : ⎢s1⎥ = ⎢s2⎥.

  (** Given two lists of pairs [s1] and [s2], the mix of [s1] and [s2] is the combination of the first projection of [s1] with the second projection of [s2]. We will only use this construct when [s1] and [s2] have the same length. *)
  Definition mix (s1 s2 : list (A*B)) := (prj1 s1) ⊗ (prj2 s2).
  Infix "⋈" := mix (at level 50).
  
  Lemma mix_fst : prj1 (s1 ⋈ s2) = prj1 s1.
  Proof. intros;unfold mix;rewrite combine_fst;repeat rewrite map_length;auto. Qed.

  Lemma mix_snd : prj2 (s1 ⋈ s2) = prj2 s2.
  Proof. intros;unfold mix;rewrite combine_snd;repeat rewrite map_length;auto. Qed.

  Lemma mix_app : (s1++s3) ⋈ (s2++s4) = s1 ⋈ s2 ++ s3 ⋈ s4.
  Proof. intros;unfold mix;rewrite map_app,map_app,combine_app;repeat rewrite map_length;auto. Qed.
End mix.
Infix "⋈" := mix (at level 50).

(** *** Flip *)
Section flip.
  Context {A B : Set} {l m : list (A*B)}.

  (** Flipping a list of pairs amounts to applying pointwise to the list the function [fun (x,y) => (y,x)], that is exchanging the order of every pair in the list. *)
  Definition flip {A B} : list (A*B) -> list (B*A) := map (fun x => (snd x,fst x)).
  Notation " l ` " := (flip l) (at level 20).
  
  (** Flip is an involution. *)
  Lemma flip_involutive : l`` = l.
  Proof.
    unfold flip;rewrite map_map;simpl.
    erewrite map_ext;[apply map_id|intros (?,?);simpl;auto].
  Qed.

  (** Flip distributes over concatenations. *)
  Lemma flip_app : (l++m)`=l`++m`.
  Proof. intros;apply map_app. Qed.

  (** Flip swaps first and second projections. *)
  Lemma flip_proj1 : prj1 (l `) = prj2 l.
  Proof. unfold flip;rewrite map_map;simpl;auto. Qed.

  Lemma flip_proj2 : prj2 (l `) = prj1 l.
  Proof. unfold flip;rewrite map_map;simpl;auto. Qed.

  (** The pair [(a,b)] is in [l] if and only if [(b,a)] is in [l`]. *)
  Lemma In_flip a b : (a,b) ∈ l ` <-> (b,a) ∈ l.
  Proof.
    unfold flip;rewrite in_map_iff;split.
    - intros ((c,d)&E&I);inversion E;subst;auto.
    - intro I;exists (b,a);simpl;auto.
  Qed.

End flip.
Notation " l ` " := (flip l) (at level 30).


(** ** Lists as finite sets *)

(** We say that two lists are equivalent if they contain the same elements. *)
Definition equivalent A l m := forall x : A , x ∈ l <-> x ∈ m.
Infix " ≈ " := equivalent (at level 80).

(** We now establish that [≈] is a congruence, and that [⊆] is a partial order.*)
Global Instance equivalent_Equivalence T : Equivalence (@equivalent T).
Proof.
  split.
  - intros l x; firstorder.
  - intros l m h x; firstorder.
  - intros l m h n h' x; firstorder.
Qed.
Global Instance incl_PreOrder T : PreOrder (@incl T).
Proof.
  split.
  - intros l x ;firstorder.
  - intros l m h n h' x;eauto.
Qed.
Global Instance incl_PartialOrder T :
  PartialOrder (@equivalent T) (@incl T).
Proof.
  intros l m;split.
  - intros h;split;intro x; firstorder.
  - intros (h1 & h2);intro x; firstorder.
Qed.

(** Concatenation preserves both relations. *)
Global Instance incl_app_Proper T :
  Proper ((@incl T) ==> (@incl T) ==> (@incl T)) (@app T).
Proof. intros l m h1 n o h2 x;repeat rewrite in_app_iff;intuition. Qed.
Global Instance equivalent_app_Proper T :
  Proper ((@equivalent T) ==> (@equivalent T) ==> (@equivalent T))
         (@app T).
Proof. intros l m h1 n o h2 x;repeat rewrite in_app_iff;firstorder. Qed.

(** The operation of adding an element to a list preserves both relations. *)
Global Instance incl_cons_Proper T a :
  Proper ((@incl T) ==> (@incl T)) (cons a).
Proof. intros l m h x;simpl in *;intuition. Qed.
Global Instance equivalent_cons_Proper T a :
  Proper ((@equivalent T) ==> (@equivalent T)) (cons a).
Proof. intros l m h x;simpl in *;firstorder. Qed.

(** For any function [f], the list morphism [map f] preserves both relations. *)
Global Instance map_incl_Proper {A B} (f : A -> B) :
  Proper (@incl A ==> @incl B) (map f).
Proof.
  intros l m I x;rewrite in_map_iff,in_map_iff.
  intros (y&<-&J);exists y;split;auto.
Qed.
Global Instance map_equivalent_Proper {A B} (f : A -> B) :
  Proper (@equivalent A ==> @equivalent B) (map f).
Proof.
  intros l m I x;rewrite in_map_iff,in_map_iff.
  split;intros (y&<-&J);exists y;split;auto;apply I,J.
Qed.

(** For any boolean predicate [f], the filtering map [filter f] preserves both relations. *)
Global Instance filter_incl_Proper {A} (f : A -> bool) :
  Proper (@incl A ==> @incl A) (filter f).
Proof.
  intros l m I x;repeat rewrite filter_In.
  intros (J&->);split;auto.
Qed.
Global Instance filter_equivalent_Proper {A} (f : A -> bool) :
  Proper (@equivalent A ==> @equivalent A) (filter f).
Proof.
  intros l m I x;repeat rewrite filter_In.
  split;intros (J&->);split;auto;apply I,J.
Qed.

(** The lemmas [In_incl_Proper] and [In_equivalent_Proper] are completely tautological, but turn out to be useful for technical reasons. *)
Global Instance In_incl_Proper {A} (x : A): Proper ((@incl A) ==> Basics.impl) (In x).
Proof. intros l m I;firstorder. Qed.
Global Instance In_equivalent_Proper {A} (x : A): Proper ((@equivalent A) ==> iff) (In x).
Proof. intros l m I;firstorder. Qed.

(** The operation of reversing a list preserves both relations. *)
Lemma rev_equivalent {A} (l : list A) : l ≈ rev l.
Proof. intro x;apply in_rev. Qed.
Global Instance incl_rev_Proper T : Proper ((@incl T) ==> (@incl T)) (@rev T).
Proof. intros l m h x;simpl in *;repeat rewrite <-in_rev;intuition. Qed.
Global Instance equivalent_rev_Proper T : Proper ((@equivalent T) ==> (@equivalent T)) (@rev T).
Proof. intros l m h x;simpl in *;repeat rewrite <-in_rev;apply h. Qed.

(** The [flat_map] function preserves both relations. *)
Global Instance incl_flat_map_Proper A B (f : A -> list B) :
  Proper ((@incl A) ==> (@incl B)) (flat_map f).
Proof. intros l m h x;simpl in *;repeat rewrite in_flat_map;firstorder. Qed.
Global Instance equivalent_flat_map_Proper A B (f : A -> list B) :
  Proper ((@equivalent A) ==> (@equivalent B)) (flat_map f).
Proof. intros l m h x;simpl in *;repeat rewrite in_flat_map;firstorder. Qed.

(** The [lift_prod f] function preserves both relations. *)
Global Instance incl_lift_prod_Proper {A:Set} (f : A -> A -> A) :
  Proper ((@incl _) ==> (@incl _) ==> (@incl _)) (lift_prod f).
Proof.
  intros l1 l2 E1 m1 m2 E2.
  transitivity (lift_prod f l1 m2).
  - clear l2 E1.
    induction l1;simpl.
    + reflexivity.
    + rewrite E2 at 1;rewrite IHl1;reflexivity.
  - clear m1 E2.
    induction l1;simpl.
    + intro;simpl;tauto.
    + rewrite IHl1 by (rewrite <- E1;apply incl_tl;reflexivity).
      clear IHl1;intro b;rewrite in_app_iff,in_map_iff;intros [(c&<-&Ic)|I];[|assumption].
      apply lift_prod_spec;exists a,c;rewrite <- E1;simpl;tauto.
Qed.
Global Instance equivalent_lift_prod_Proper {A:Set} (f : A -> A -> A) :
  Proper ((@equivalent _) ==> (@equivalent _) ==> (@equivalent _)) (lift_prod f).
Proof.
  intros l1 l2 E1 m1 m2 E2;apply incl_PartialOrder;unfold Basics.flip;simpl;split.
  - apply incl_PartialOrder in E1 as (->&_).
    apply incl_PartialOrder in E2 as (->&_).
    reflexivity.
  - apply incl_PartialOrder in E1 as (_&->).
    apply incl_PartialOrder in E2 as (_&->).
    reflexivity.
Qed.
    
(** The following simple facts about inclusion and equivalence are convenient to have in our toolbox. *)
Lemma incl_nil T (A : list T) : [] ⊆ A.
Proof. intros x;firstorder. Qed.
Lemma incl_app_or T (A B C : list T) : A ⊆ B \/ A ⊆ C -> A⊆B++C.
Proof. intros [?|?];auto using incl_appl, incl_appr. Qed.
Create HintDb eq_list.
Lemma incl_app_split {A} (l m p : list A) : l++m ⊆ p <-> l⊆ p /\ m ⊆ p.
Proof. unfold incl;setoid_rewrite in_app_iff;firstorder. Qed.
Hint Resolve incl_appl incl_appr incl_nil app_assoc : eq_list.
Lemma app_idem {A} (l : list A) : l ++ l ≈ l.
Proof. intro;rewrite in_app_iff;tauto. Qed.
Lemma app_comm {A} (l m : list A) : l ++ m ≈ m ++ l.
Proof. intro;repeat rewrite in_app_iff;tauto. Qed.
Lemma incl_split {A} (l m n : list A) :
  l ⊆ m ++ n -> exists l1 l2, l ≈ l1++l2 /\ l1 ⊆ m /\ l2 ⊆ n.
Proof.
  induction l as [|a l];simpl;intro I.
  - exists [],[];split;[reflexivity|split;apply incl_nil].
  - destruct IHl as (l1&l2&E&I1&I2).
    + intros x Ix;apply I;now right.
    + assert (Ia : a ∈ (m++n)) by (apply I;now left).
      apply in_app_iff in Ia as [Ia|Ia].
      * exists (a::l1),l2;split;[rewrite E;reflexivity|].
        split;[|assumption].
        intros x [<-|Ix];[assumption|].
        apply I1,Ix.
      * exists l1,(a::l2);split;[rewrite E;intro;repeat (rewrite in_app_iff;simpl);tauto|].
        split;[assumption|].
        intros x [<-|Ix];[assumption|].
        apply I2,Ix.
Qed.

(** ** More general lemmas *)
(** If a boolean predicate [f] fails to be true for every element of a list [l], then there must exists a witnessing element [y] falsifying [f]. This is an instance of a classical principle holding constructively when restricted to decidable properties over finite domains. *)
Lemma forall_existsb {A} (f : A -> bool) l :
  ~ (forall x, x ∈ l -> f x = true) -> exists y, y ∈ l /\ f y = false.
Proof.
  induction l as [|a l].
  - intro h;exfalso;apply h.
    intros x;simpl;tauto.
  - intros h;case_eq (f a).
    + intro p;destruct IHl as (y&I&E).
      * intro h';apply h;intros x [<-|I];auto.
      * exists y;split;auto.
        now right.
    + intro E;exists a;split;auto.
      now left.
Qed.

(** In [forallb f l] we may replace [f] with a function [g] outputting the same values on the elements of [l]. *)
Lemma forallb_ext_In {A} (f g : A -> bool) l : (forall a, a ∈ l -> f a = g a) -> forallb f l = forallb g l.
Proof.
  induction l;simpl;[|f_equal];auto.
  intros h;f_equal;[apply h|apply IHl];auto.
Qed.

(** In [forallb f l] we may replace [f] with a function [g] outputting the same values. *)
Lemma forallb_ext {A} (f g : A -> bool) l : (forall a, f a = g a) -> forallb f l = forallb g l.
Proof. intro h;apply forallb_ext_In;intros;apply h. Qed.

(** For every list [l] and every function [f], [l] is a fixpoint of [map f] if and only if every element of [l] is a fixpoint of [f]. *)
Lemma map_eq_id {A} (l : list A) (f : A -> A) :
  map f l = l <-> (forall x, x ∈ l -> f x = x).
Proof.
  split.
  - intros E x I.
    apply In_nth with (d:=x) in I as (n&len&<-).
    rewrite <- map_nth with (f:=f).
    rewrite E.
    apply nth_indep,len.
  - intro E;erewrite map_ext_in;[rewrite map_id;auto|].
    intros x I;apply E;auto.
Qed.

(** [fun f => map f l] is bijective, using extensional equality of functions. *)
Lemma map_bij {A B} (f g : A -> B) l : map f l = map g l -> forall a, a ∈ l -> f a = g a.
Proof.
  induction l;simpl;auto.
  - intros;tauto.
  - intros E b [I|I];inversion E;subst;auto.
Qed.

Lemma map_ext_in_iff (A B : Type) (f g : A -> B) (l : list A) :
  (forall a : A, a ∈ l -> f a = g a) <-> map f l = map g l.
Proof.
  split;[apply map_ext_in|].
  induction l;simpl;[tauto|].
  intros h b.
  inversion h as [[h1 h2]].
  intros [<-|I].
  - assumption.
  - apply IHl,I;assumption.
Qed.

Lemma map_eq_equivalent (A B : Set) (f g : A -> B) l m :
  l ≈ m -> map f m = map g m <-> map f l = map g l.
Proof.
  intros E;rewrite <- map_ext_in_iff.
  setoid_rewrite <- E.
  rewrite map_ext_in_iff;reflexivity.
Qed.

(** We may lift a decomposition of the second (respectively first) component of a list of pairs into a decomposition of the original list. *)
Lemma split_snd {A B} a (t : list (A * B)) t1 t2 :
  prj2 t = t1 ++ a :: t2 -> ~ a ∈ t1 -> exists k s1 s2, t = s1++(k,a)::s2 /\ t1 = prj2 s1 /\ t2 = prj2 s2.
Proof.
  revert t t2;induction t1;intros [|(k,b)t] t2;simpl;try discriminate.
  - intros E _;inversion E;subst.
    exists k,[],t;simpl;auto.
  - intros E0 I;inversion E0 as [[X E]];subst;clear E0.
    apply IHt1 in E as (m&s1&s2&->&->&->);[|tauto].
    exists m,((k,a0)::s1),s2;simpl;auto.
Qed.

Lemma split_fst {A B} a (t : list (A * B)) t1 t2 :
  prj1 t = t1 ++ a :: t2 -> ~ a ∈ t1 -> exists k s1 s2, t = s1++(a,k)::s2 /\ t1 = prj1 s1 /\ t2 = prj1 s2.
Proof.
  revert t t2;induction t1;intros [|(b,k) t] t2;simpl;try discriminate.
  - intros E _;inversion E;subst.
    exists k,[],t;simpl;auto.
  - intros E0 I;inversion E0 as [[X E]];subst;clear E0.
    apply IHt1 in E as (m&s1&s2&->&->&->);[|tauto].
    exists m,((a0,k)::s1),s2;simpl;auto.
Qed.

(** If [n] is smaller than the length of [u], then [u] can be split into a prefix of size [n], followed by a non-empty list. *)
Lemma split_word {A} n (u : list A) : n < ⎢u⎥ -> exists x u1 u2, u = u1++x::u2 /\ ⎢u1⎥ = n.
Proof.
  induction u using rev_induction;simpl;[lia|].
  destruct_eqX n ⎢u⎥ ;subst.
  - intros _;exists a,u,[];split;auto.
  - rewrite app_length;simpl;intros L;destruct IHu as (x&u1&u2&->&E);[lia|].
    exists x,u1,(u2++[a]);split;auto.
    rewrite app_ass;simpl;auto.
Qed.

(** ** Subsets of a list *)
Fixpoint subsets {A : Set} (l : list A) :=
  match l with
  | [] => [[]]
  | a::l => map (cons a) (subsets l)++subsets l
  end.

Lemma subsets_In {A : Set}(l : list A) :
  forall m, m ∈ subsets l -> m ⊆ l.
Proof.
  induction l as [|a l];intros m;simpl;try rewrite in_app_iff.
  - intros [<-|F];[reflexivity|tauto].
  - rewrite in_map_iff;intros [(m'&<-&I)|I];apply IHl in I as ->.
    + reflexivity.
    + intro;simpl;tauto.
Qed.

Lemma incl_cons_disj {A : Set} (a : A) m l :
  m ⊆ a :: l -> m ⊆ l \/ exists m', m ≈ a::m' /\ m' ⊆ l.
Proof.
  induction m as [|b m];simpl.
  - intro;left;apply incl_nil.
  - intros I.
    destruct IHm as [IH|(m'&E&IH)].
    + intros x Ix;apply I;now right.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m;split;[reflexivity|assumption].
      * left;intros c [<-|Ic];[assumption|].
        apply IH,Ic.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m';split;[|assumption].
        rewrite E;clear;intro;simpl;tauto.
      * right;exists (b::m');split.
        -- rewrite E;intro;simpl;tauto.
        -- intros c [<-|Ic];[assumption|].
           apply IH,Ic.
Qed.

Lemma subsets_spec {A : Set} (l : list A) :
  forall m, m ⊆ l <-> exists m', m' ∈ subsets l /\ m ≈ m'.
Proof.
  intro m;split.
  - revert m; induction l as [|a l];intros m L.
    + exists [];split;[simpl;tauto|].
      apply incl_PartialOrder;split;[assumption|apply incl_nil].
    + simpl;destruct (incl_cons_disj L) as [h|(m'&E&h)];apply IHl in h as (m''&I&E').
      * exists m'';split;[|assumption].
        rewrite in_app_iff;tauto.
      * exists (a::m'');split.
        -- apply in_app_iff;left;apply in_map_iff;exists m'';tauto.
        -- rewrite E,E';reflexivity.
  - intros (m'&I&->);apply subsets_In,I.
Qed.

Lemma subsets_NoDup {A : Set} (k l : list A) :
  NoDup l -> k ∈ subsets l -> NoDup k.
Proof.
  revert k;induction l as [|a l];intros k;simpl.
  - intros h [<-|F];tauto.
  - rewrite NoDup_cons_iff,in_app_iff,in_map_iff.
    intros (nI&nd) [(k'&<-&Ik')|Ik].
    + apply NoDup_cons.
      * intro h;apply nI,(subsets_In Ik'),h.
      * apply IHl;tauto.
    + apply IHl;tauto.
Qed.

(** ** Pairs *)
Definition pairs {A B : Set} l r : list (A * B) :=
  fold_right (fun a acc => (map (fun b => (a,b)) r)++acc) [] l.

Lemma pairs_spec {A B : Set} l r (a : A) (b : B) : (a,b) ∈ pairs l r <-> a ∈ l /\ b ∈ r.
Proof.
  revert a b;induction l;simpl;[tauto|].
  intros a' b;rewrite in_app_iff.
  rewrite IHl;clear IHl.
  rewrite in_map_iff.
  split.
  - intros [(?&E&Ib)|I].
    + inversion E;subst;tauto.
    + tauto.
  - intros ([<-|Ia]&Ib).
    + left;exists b;tauto.
    + right;tauto.
Qed.

(** ** Enumerate lists of a certain length *)
Fixpoint lists_of_length {A} (elts:list A) n :=
  match n with
  | 0 => [[]]
  | S n => flat_map (fun l => map (fun e => e::l) elts) (lists_of_length elts n)
  end.

Lemma lists_of_length_spec {A} (elts : list A) n l :
  l ∈ lists_of_length elts n <-> ⎢l⎥ = n /\ l ⊆ elts.
Proof.
  revert l;induction n;intros l;simpl.
  - split.
    + intros [<-|F];[|tauto].
      split;[reflexivity|apply incl_nil].
    + destruct l;[tauto|simpl;intros (F&_);discriminate].
  - rewrite in_flat_map;setoid_rewrite IHn;clear IHn.
    setoid_rewrite in_map_iff.
    split.
    + intros (m&(Len&Lm)&(a&<-&Ia)).
      split;[simpl;rewrite Len;reflexivity|].
      apply incl_cons;tauto.
    + intros (Len&Incl).
      destruct l as [|a l];simpl in Len;inversion Len as [[Len']].
      exists l;split.
      * split;[reflexivity|].
        intros x Ix;apply Incl;now right.
      * exists a;split;[reflexivity|].
        apply Incl;now left.
Qed.

(** ** Pad a list with an element *)
Definition pad {A} (e : A) (l : list A) := e::flat_map (fun a => [a;e]) l.

Lemma pad_contents {A} (e : A) l : pad e l ≈ e::l.
Proof.
  unfold pad;induction l;simpl.
  - reflexivity.
  - rewrite IHl;intro;simpl;tauto.
Qed.

(** ** Lists over a decidable set *)
Section dec_list.
  Context { A : Set } { dec_A : decidable_set A }.

  (** Boolean equality for lists *)
  Fixpoint equal_list l m :=
    match (l,m) with
    | ([],[]) => true
    | (a::l,b::m) => eqX a b && equal_list l m
    | _ => false
    end.

  Lemma equal_list_spec l m : reflect (l = m) (equal_list l m).
  Proof.
    apply iff_reflect;revert m;induction l as [|a l];intros [|b m];
    simpl;split;try reflexivity||discriminate;
    rewrite andb_true_iff,<-IHl.
    - intro h;inversion h;split;auto;apply eqX_refl.
    - intros (h&->);apply eqX_correct in h as ->;reflexivity.
  Qed.
                                
  (** The set of lists of [A]s is decidable. *)
  Global Instance dec_list : decidable_set (list A).
  Proof. apply (Build_decidable_set equal_list_spec). Qed.

  (** Boolean predicate testing whether an element belongs to a list. *)
  Definition inb (n : A) l := existsb (eqX n) l.
  
  Lemma inb_spec n l : inb n l = true <-> n ∈ l.
  Proof.
    case_eq (inb n l);intro E;unfold inb in *.
    - apply existsb_exists in E as (y&I&E).
      apply eqX_correct in E as ->;tauto.
    - rewrite <- not_true_iff_false, existsb_exists in E;split.
      -- discriminate.
      -- intro I;exfalso;apply E;eexists;split;[eauto|];apply eqX_refl.
  Qed.

  Lemma inb_false n l : inb n l = false <-> ~ n ∈ l.
  Proof. rewrite <- inb_spec,not_true_iff_false;reflexivity. Qed.

  (** This boolean predicate allows us to use the excluded middle with the predicate [In]. *)
  Lemma inb_dec n l : { inb n l = true /\ n ∈ l } + { inb n l = false /\ ~ n ∈ l }.
  Proof.
    case_eq (inb n l);intro E;[left|right];rewrite <- inb_spec;auto.
    split;auto;rewrite E;discriminate.
  Qed.

  Lemma In_dec (n : A) l : { n ∈ l } + { ~ n ∈ l }.
  Proof.
    case_eq (inb n l);intro E;[left|right];rewrite <- inb_spec,E;auto.
  Qed.
  (* begin hide *)
  Ltac case_in a l :=
    let I := fresh "I" in
    let E := fresh "E" in
    destruct (inb_dec a l) as [(E&I)|(E&I)];
    try rewrite E in *;clear E.
  (* end hide *)

  (** Boolean function implementing containment test. *)  
  Definition inclb (a b : list A) :=
    forallb (fun x => inb x b) a.
  
  Lemma inclb_correct a b : inclb a b = true <-> a ⊆ b.
  Proof.
    unfold incl,inclb;rewrite forallb_forall.
    setoid_rewrite inb_spec;intuition.
  Qed.

  (** Boolean function testing for equivalence of lists. *)
  Definition equivalentb l1 l2 := inclb l1 l2 && inclb l2 l1.

  Lemma equivalentb_spec l1 l2 : equivalentb l1 l2 = true <-> l1 ≈ l2.
  Proof.
    unfold equivalentb;rewrite andb_true_iff,inclb_correct,inclb_correct.
    split.
    - intros (e1&e2);apply incl_PartialOrder;split;tauto.
    - intros ->;split;reflexivity.
  Qed.


  (** If [u=u1++a::u2], we call the triple [(u1,u2)] an [a]-decomposition of [u] if [a] does not appear in [u1]. *)

  (** If [a] is in [l], then there exists an [a]-decomposition of [l]. *)
  Lemma decomposition (a : A) l :
    a ∈ l <-> exists l1 l2, l = l1 ++ a :: l2 /\ ~ a ∈ l1.
  Proof.
    induction l as [|b l];simpl;auto.
    - split;try tauto.
      intros (?&?&?&_).
      apply app_cons_not_nil in H;tauto.
    - destruct_eqX a b.
      + split;auto.
        intros _;exists [],l;split;auto.
      + rewrite IHl;clear IHl;split.
        * intros [<-|(l1&l2&->&h)];[tauto|].
          exists (b::l1),l2;split;auto.
          intros [->|I];tauto.
        * intros (l1&l2&E&I);right.
          destruct l1 as [|c l1].
          -- simpl in *;inversion E;subst;tauto.
          -- simpl in E;inversion E;subst;clear E.
             exists l1,l2;split;auto.
             intro;apply I;now right.
  Qed.

  (** Decompositions are unique.*)
  Lemma decomp_unique (a:A) u1 u2 v1 v2 :
    u1++(a::u2) = v1++a::v2 -> ~ In a v1 -> ~ In a u1 -> u1 = v1 /\ u2 = v2.
  Proof.
    intros E I1 I2;destruct (Levi_strict E) as [(->&E2)|(c&w&[(->&E2)|(->&E2)])];
      inversion E2;subst;clear E2;auto.
    - exfalso;apply I2,in_app_iff;right;left;auto.
    - exfalso;apply I1,in_app_iff;right;left;auto.
  Qed.

  Lemma decomp_unambiguous (u1 u2 v1 v2 : list A) a b :
    u1++a::u2 = v1++b::v2 -> ~ In a v1 -> ~ In b u1 -> u1 = v1 /\ a=b /\ u2 = v2.
  Proof.
    intros E Ia Ib;destruct (Levi_strict E) as [(->&E2)|(c&w&[(->&E2)|(->&E2)])].
    - inversion E2;auto.
    - exfalso;apply Ib;rewrite in_app_iff;simpl.
      inversion E2;auto.
    - exfalso;apply Ia;rewrite in_app_iff;simpl.
      inversion E2;auto.
  Qed.

  (** [{{l}}] is a list containing the same elements as [l], but without duplication. *)
  Definition undup l :=
    fold_right (fun a acc =>
                  if inb a acc
                  then acc
                  else a::acc)
               nil
               l.

  Notation " {{ l }} " := (undup l) (at level 0).

  (** [{{l}}] is shorter than [l]. *)
  Lemma undup_length l : ⎢{{l}}⎥ <= ⎢l⎥ .
  Proof. induction l;simpl; [|destruct (inb a _);simpl];lia. Qed.

  (** [{{l}}] contains the same elements as [l]. *)
  Lemma In_undup a l: a ∈ {{l}} <-> a ∈ l.
  Proof.
    revert a; induction l;simpl;auto;try tauto.
    intro b;case_in a {{l}};simpl;rewrite IHl in *;try tauto.
    destruct_eqX a b;tauto.
  Qed.
  (*begin hide *)
  Ltac simpl_In :=
    repeat rewrite in_app_iff
    || rewrite <- In_rev
    || rewrite In_undup
    || rewrite filter_In.
  Tactic Notation "simpl_In" "in" hyp(h) :=
    repeat rewrite in_app_iff in h
    || rewrite <- In_rev in h
    || rewrite In_undup in h
    || rewrite filter_In in h.
  Tactic Notation "simpl_In" "in" "*" :=
    repeat rewrite in_app_iff in *
    || rewrite <- In_rev in *
    || rewrite In_undup in *
    || rewrite filter_In in *.
  (* end hide *)

  (** Put differently, [{{l}}] is equivalent to [l]. *)
  Lemma undup_equivalent l : {{l}} ≈ l.
  Proof. intros x;apply In_undup. Qed.
  
  (** The [{{}}] operator always produces a duplication free list. *)
  Lemma NoDup_undup l : NoDup {{l}}.
  Proof.
    induction l;simpl;auto using NoDup_nil.
    case_in a {{l}};auto using NoDup_cons.
  Qed.

  (** The [{{}}] operator doesn't change duplication free lists. *)
  Lemma NoDup_undup_eq l : NoDup l -> l = {{l}}.
  Proof.
    induction l;simpl;auto.
    intro h;apply NoDup_cons_iff in h as (I&h).
    apply IHl in h as <-;case_in a l;tauto.
  Qed.

  (** A list is without duplication if and only if its mirror is duplication free. *)
  Lemma NoDup_rev {X:Set} (l : list X) : NoDup l <-> NoDup (rev l).
  Proof.
    induction l;simpl;firstorder.
    - apply NoDup_cons_iff in H1 as (I&h1).
      apply NoDup_app;firstorder;simpl.
      + simpl_In in *;intros [->|?];tauto.
      + apply NoDup_cons;firstorder;apply NoDup_nil.
    - apply NoDup_remove in H1 as (h1&h2);rewrite app_nil_r in *;apply H0 in h1.
      simpl_In in *;apply NoDup_cons;auto.
  Qed.

  (** [{{}}] preserves both [⊆] and [≈]. *)
  Global Instance undup_incl_Proper : Proper (@incl A ==> @incl A) undup.
  Proof. intros l m I x;simpl_In;auto. Qed.
  Global Instance undup_equivalent_Proper : Proper (@equivalent A ==> @equivalent A) undup.
  Proof. intros l m I x;simpl_In;auto. Qed.

  (** If [l] is contained in [m] and doesn't contain duplicates, then it must be shorter than [m]. *)
  Lemma NoDup_length (l m : list A) :
    l ⊆ m -> NoDup l -> ⎢l⎥ <= ⎢m⎥ .
  Proof.
    revert m;induction l;simpl;intros m E ND.
    - lia.
    - cut (⎢l⎥ <= ⎢(fun x=> negb (x=?=a)) :> m⎥).
      + intro L;eapply Lt.lt_le_S,PeanoNat.Nat.le_lt_trans;[apply L|].
        assert (Ia : a ∈ m) by (apply E;now left);revert Ia;clear.
        induction m as [|b m];simpl;[tauto|].
        intros [->|Ia].
        * rewrite eqX_refl;simpl;auto.
          apply Lt.le_lt_n_Sm,filter_length.
        * apply IHm in Ia;destruct_eqX b a;simpl;lia.
      + apply NoDup_cons_iff in ND as (Ia&ND).
        apply IHl;auto.
        rewrite <- E;simpl;rewrite eqX_refl;simpl.
        intro x;simpl_In; rewrite negb_true_iff,eqX_false.
        intros I;split;auto.
        intros ->;tauto.
  Qed.

  (** [l] is a fixpoint of [map f] if and only if [{{l}}] is a fixpoint of the same list homomorphism [map f]. *)
  Lemma map_undup_id (l : list A) (f : A -> A) :
    map f l = l <-> map f {{l}} = {{l}}.
  Proof.
    repeat rewrite map_eq_id.
    setoid_rewrite In_undup;tauto.
  Qed.

  (** If [f] is injective, [map f] and [{{}}] commute. *)
  Lemma map_undup_inj (l : list A) (f : A -> A) :
    (forall x y, f x = f y -> x = y) -> map f {{l}} = {{map f l}}.
  Proof.
    intro hp;induction l;auto.
    simpl;case_in a {{l}};case_in (f a) {{map f l}};simpl;rewrite IHl;auto;exfalso.
    - apply I0,In_undup,in_map_iff;exists a;simpl_In in I;tauto.
    - apply I;simpl_In in *.
      apply in_map_iff in I0 as (y&Ey&Iy);apply hp in Ey as ->;auto.
  Qed.

  (** [NoDup] is a decidable property. *)
  Definition NoDupb l := l =?= {{l}}.
  
  Lemma NoDupb_NoDup l : NoDupb l = true <-> NoDup l.
  Proof.
    unfold NoDupb;rewrite eqX_correct;split.
    + intros ->;apply NoDup_undup.
    + apply NoDup_undup_eq.
  Qed.

  (** Remove an element from a list. *)
  Definition rm (a : A) l := (fun x => negb (a=?=x)) :> l.
  Notation " l ∖ a " := (rm a l) (at level 50).

  Lemma rm_In b a l : b ∈ l ∖ a <-> b ∈ l /\ a<>b.
  Proof. unfold rm;rewrite filter_In,negb_true_iff,eqX_false;tauto. Qed.

  Lemma rm_equiv a l : a ∈ l -> l ≈ a::(l ∖ a).
  Proof. intros I x;simpl;rewrite rm_In;destruct_eqX a x;tauto. Qed.

  Global Instance rm_equivalent_Proper a : Proper ((@equivalent A)==> (@equivalent A)) (rm a).
  Proof. apply filter_equivalent_Proper. Qed.
  
  Global Instance rm_incl_Proper a : Proper ((@incl A)==> (@incl A)) (rm a).
  Proof. apply filter_incl_Proper. Qed.

  Lemma rm_notin a l : ~ a ∈ l -> l ∖ a = l.
  Proof.
    unfold rm;intro I.
    erewrite filter_ext_In;[apply filter_true|].
    intros b Ib.
    apply eq_true_iff_eq;split;[tauto|].
    intros _;apply negb_true_iff,eqX_false.
    intros ->;tauto.
  Qed.

  (** Remove the first occurrence of an element from a list. *)

  Fixpoint rmfst (a : A) l :=
  match l with
  | [] => []
  | b::l => if a=?=b then l else b::(rmfst a l)
  end.
  Notation " l ⊖ a " := (rmfst a l) (at level 50).

  Lemma rmfst_notin a l : ~ a ∈ l -> l ⊖ a = l.
  Proof.
    induction l;simpl;auto.
    intros N;simpl.
    destruct_eqX a a0.
    - exfalso;apply N;tauto.
    - f_equal;apply IHl;intro;tauto.
  Qed.

  Lemma rmfst_in a l1 l2 : ~ a ∈ l1 -> (l1 ++ a :: l2) ⊖ a = l1++l2.
  Proof.
    induction l1;simpl;auto.
    - rewrite eqX_refl;auto.
    - intros N;destruct_eqX a a0.
      + exfalso;apply N;tauto.
      + f_equal;apply IHl1;tauto.
  Qed.

  (** [l ⊖ a] is contained in the list [l]. *)
  Lemma rmfst_decr a l : l ⊖ a ⊆ l.
  Proof.
    case_in a l.
    - apply decomposition in I as (?&?&->&I).
      rewrite rmfst_in;auto;intro;simpl_In;simpl;tauto.
    - rewrite rmfst_notin;auto;reflexivity.
  Qed.

  (** The operation [rmfst] commutes with itself. *)
  Lemma rmfst_comm (l : list A) a b : (l ⊖ a) ⊖ b = (l ⊖ b) ⊖ a.
  Proof.
    induction l as [|c l];simpl;auto.
    destruct_eqX a c;subst.
    - destruct_eqX b c;auto.
      simpl;rewrite eqX_refl;reflexivity.
    - simpl;destruct_eqX b c;auto.
      simpl;apply eqX_false in N as ->.
      rewrite IHl;reflexivity.
  Qed.

  (** If we try to remove [a] from [l++m], one of three things may happen:
      - [a] appears in [l], so we obtain [(l⊖ a)++m];
      - [a] appears in [m] but not in [l], so we obtain [l++(m⊖ a)];
      - [a] does not appear in [l] or [m], so we obtain [l++m].
   *)
  Lemma rmfst_app_dec (l m:list A) a :
    (exists l1 l2, l = l1++a::l2 /\ ~ a ∈ l1 /\ (l++m) ⊖ a = l1++l2++m)
    \/ (exists m1 m2, m = m1++a::m2 /\ ~ a ∈ (l++m1) /\ (l++m) ⊖ a = l++m1++m2)
    \/ (~ a ∈ (l++m) /\ (l++m) ⊖ a = l++m).
  Proof.
    case_in a l.
    - left;apply decomposition in I as (l1&l2&->&I).
      exists l1,l2;repeat split;auto.
      rewrite app_ass;apply rmfst_in;auto.
    - case_in a m.
      + right;left;apply decomposition in I0 as (m1&m2&->&I0).
        exists m1,m2;simpl_In;repeat split;try tauto.
        repeat rewrite <-app_ass;apply rmfst_in;simpl_In;tauto.
      + right;right;rewrite rmfst_notin;simpl_In;tauto.
  Qed.

  (** This lemma highlights the existence of a list [l1-l2]: the list [m] shown to exist here is such that it contains no elements from [l1], but concatenating [l1] and [m] yields a list equivalent to [l1++l2]. Furthermore, we produce [m] without inserting any duplicates. *)
  Lemma split_app_unambiguous (l1 l2 : list A) :
    exists m, l1++l2 ≈ l1++m /\ NoDup m /\ (forall a, a ∈ m -> ~ a ∈ l1).
  Proof.
    induction l2 as [|b l];simpl.
    - exists [];repeat split;try tauto.
      apply NoDup_nil.
    - destruct IHl as (m&Em&nd&F).
      case_in b (l1++m).
      + exists m;split;[|split];try assumption.
        rewrite <- Em;clear F nd.
        intro;simpl_In in *;firstorder subst.
        * tauto.
        * cut (x∈(l1++l));[simpl_In;tauto|].
          rewrite Em;simpl_In;tauto.
      + exists (b::m);split;[|split].
        * transitivity (b::l1++l);[intro;repeat (simpl;simpl_In);tauto|].
          transitivity (b::l1++m);[|intro;repeat (simpl;simpl_In);tauto].
          rewrite Em;reflexivity.
        * apply NoDup_cons;[|assumption].
          intro I';apply I;simpl_In;tauto.
        * intros a [<-|Ia].
          -- intro Ib;apply I;simpl_In;tauto.
          -- apply F,Ia.
  Qed.

  (** Sometimes we will need to count the number of occurrences of a particular element in a given list. *)
  Notation nb a l := ⎢eqX a :> l⎥.

  (** An equivalent (but slightly less convenient) function was defined in the standard library. *)
  Lemma nb_count_occ (a : A) l : nb a l = count_occ X_dec l a.
  Proof.
    induction l;simpl;auto.
    destruct_eqX a0 a;simpl;auto.
    destruct_eqX a a0;subst;simpl;tauto.
  Qed.

  (** For convenience, we translate all the lemmas regarding [count_occ] in terms of [nb]. *)
  Lemma nb_nil (x : A) : nb x [] = 0.
  Proof. rewrite nb_count_occ;apply count_occ_nil. Qed.

  Lemma nb_In l (x : A) : x ∈ l <-> nb x l > 0.
  Proof. rewrite nb_count_occ;apply count_occ_In. Qed.
  
  Lemma nb_not_In (l : list A) (x : A): ~ x ∈ l <-> nb x l = 0.
  Proof. rewrite nb_count_occ;apply count_occ_not_In. Qed.
  
  Lemma NoDup_nb (l : list A) : NoDup l <-> (forall x : A, nb x l <= 1).
  Proof. setoid_rewrite nb_count_occ;apply NoDup_count_occ. Qed.

  Lemma nb_inv_nil (l : list A) : (forall x : A, nb x l = 0) <-> l = [].
  Proof. setoid_rewrite nb_count_occ;apply count_occ_inv_nil. Qed.

  Lemma nb_cons_neq (l : list A) (x y : A) : x <> y -> nb y (x :: l) = nb y l.
  Proof. repeat rewrite nb_count_occ;apply count_occ_cons_neq. Qed.

  Lemma nb_cons_eq (l : list A) (x y : A) : x = y -> nb y (x :: l) = S (nb y l).
  Proof. repeat rewrite nb_count_occ;apply count_occ_cons_eq. Qed.

  Lemma NoDup_nb' (l : list A) : NoDup l <-> (forall x : A, x ∈ l -> nb x l = 1).
  Proof. setoid_rewrite nb_count_occ;apply NoDup_count_occ'. Qed.
  
End dec_list.
Notation " l ∖ a " := (rm a l) (at level 50).
Notation " l ⊖ a " := (rmfst a l) (at level 50).
Notation nb a l := ⎢eqX a :> l⎥.
Notation " {{ l }} " := (undup l) (at level 0).

(* begin hide *)
Ltac case_in a l :=
  let I := fresh "I" in
  let E := fresh "E" in
  destruct (inb_dec a l) as [(E&I)|(E&I)];
  try rewrite E in *;clear E.
Lemma decompose_app {A : Set} (u1 u2 v1 v2 : list A) :
  u1++u2=v1++v2 -> (u1=v1/\u2=v2)\/(exists w a,u1=v1++a::w /\ v2=a::w++u2)\/(exists w a, v1=u1++a::w /\ u2=a::w++v2).
Proof.
  intro E;apply Levi_strict in E as [(->&->)|(a&w&[(->&->)|(->&->)])].
  - tauto.
  - right;left;exists w,a;tauto.
  - right;right;exists w,a;tauto.
Qed.

Ltac levi u v :=
  let a := fresh "a" in
  let w := fresh "w" in
  let h := fresh "h" in
  let E1 := fresh "E" in
  let E2 := fresh "E" in
  assert (h:u=v);
  [auto
  |destruct (decompose_app h) as [E1|[(w&a&E1)|(w&a&E1)]];
   destruct E1 as (E1&E2);repeat (rewrite E1 in * || rewrite E2 in * )].

Tactic Notation "levi" hyp(h) :=
  let a := fresh "a" in
  let w := fresh "w" in
  let E1 := fresh "E" in
  let E2 := fresh "E" in
  destruct (decompose_app h) as [E1|[(w&a&E1)|(w&a&E1)]];
  destruct E1 as (E1&E2);repeat (rewrite E1 in * || rewrite E2 in * ).
Lemma in_cons_iff {A} (l : list A) a b :
  a ∈ (b::l) <-> b = a \/ a ∈ l.
Proof. simpl;tauto. Qed.
Ltac simpl_In :=
  repeat rewrite in_app_iff
  || rewrite in_cons_iff
  || rewrite <- In_rev
  || rewrite In_undup
  || rewrite filter_In.
Tactic Notation "simpl_In" "in" hyp(h) :=
  repeat (rewrite in_app_iff in h)
  || (rewrite in_cons_iff in h)
  || (rewrite <- In_rev in h)
  || (rewrite In_undup in h)
  || (rewrite filter_In in h).
Tactic Notation "simpl_In" "in" "*" :=
  repeat (rewrite in_app_iff in * )
  || (rewrite in_cons_iff in * )
  || (rewrite <- In_rev in * )
  || (rewrite In_undup in * )
  || (rewrite filter_In in * ).
(* end hide *)

Lemma nb_map {A B :Set} `{decidable_set A,decidable_set B} (f : A -> B) :
  (forall x1 x2 : A, f x1 = f x2 -> x1 = x2) ->
  forall (x : A) (l : list A), nb x l = nb (f x) (map f l).
Proof. setoid_rewrite nb_count_occ;apply count_occ_map. Qed.

Lemma rmfst_flip {A B : Set} `{decidable_set A,decidable_set B} (s : list (A*B)) a b :
  s` ⊖ (a,b) = (s ⊖ (b,a))`.
Proof.
  case_in (b,a) s.
  - rewrite decomposition in I;destruct I as (s1&s2&->&I).
    rewrite rmfst_in;auto.
    rewrite flip_app;simpl.
    rewrite rmfst_in,flip_app;auto.
    rewrite In_flip;apply I.
  - rewrite rmfst_notin,rmfst_notin;auto.
    rewrite In_flip;apply I.
Qed.

(** * Sum function *)
(** If [a1,...,an] are elements in [A] and [f] is a function from [A] to [nat], then [sum f [a1;...;an]] is the natural number [f a1+...+f an]. *)
Definition sum {A} f (l : list A) := fold_right (fun a acc => f a + acc) 0 l.

(** [sum f] distributes over concatenations. *)
Lemma sum_app {A} f (l m : list A) : sum f (l++m) = sum f l + sum f m.
Proof. induction l;simpl;try lia. Qed.

(** If [l] is contained in [m] and has no duplicates, then summing [f] on [l] yields a smaller value than summing [f] on [m]. *)
Lemma sum_incl_ND {A} f (l m : list A) :
  l ⊆ m -> NoDup l -> sum f l <= sum f m.
Proof.
  revert m;induction l;intros m Incl ND;simpl.
  - lia.
  - assert (Ia: a ∈ m) by (apply Incl;now left).
    apply in_split in Ia as (m1&m2&->).
    rewrite sum_app;simpl.
    apply NoDup_cons_iff in ND as (Ia&ND).
    apply (IHl (m1++m2)) in ND.
    + rewrite sum_app in ND;lia.
    + intro x;pose proof (Incl x) as h;revert h.
      repeat rewrite in_app_iff;simpl;intuition subst;tauto.
Qed.

(** If two duplicate-free list are equivalent, then summing [f] on any of them yields the same result. *)
Lemma sum_eq_ND {A} f (l m : list A) :
  l ≈ m -> NoDup l -> NoDup m -> sum f l = sum f m.
Proof.
  revert m;induction l;intros m Eq NDl NDm;simpl.
  - destruct m as [|a m];[simpl;lia|].
    exfalso;cut (a ∈ []);[simpl;tauto|].
    rewrite Eq;now left.
  - assert (Ia: a ∈ m) by (apply Eq;now left).
    apply in_split in Ia as (m1&m2&->).
    rewrite sum_app;simpl.
    apply NoDup_cons_iff in NDl as (Ial&NDl).
    apply NoDup_remove in NDm as (Iam&NDm).
    apply (IHl (m1++m2)) in NDl;auto.
    + rewrite sum_app in NDl;lia.
    + intro x;pose proof (Eq x) as h;revert h NDm.
      repeat rewrite in_app_iff;simpl;intuition subst;tauto.
Qed.

(** If [f] is pointwise smaller than [g], then the sum [sum f l] is smaller than [sum g l]. *)
Lemma sum_incr {A} f g (l : list A) : (forall x, f x <= g x) -> sum f l <= sum g l.
Proof.
  intro h;induction l;simpl;auto.
  pose proof (h a);lia.
Qed.

(** [sum f l] only depends on the values of [f], not its implementation. *)
Lemma sum_ext {A} f g (l : list A) : (forall x, f x = g x) -> sum f l = sum g l.
Proof. intro h;induction l;simpl;auto. Qed.

Lemma sum_ext_In {A} f g (l : list A) : (forall x, x ∈ l -> f x = g x) -> sum f l = sum g l.
Proof.
  induction l.
  - intro;reflexivity.
  - intro h;simpl.
    rewrite IHl,h;auto.
    + now left.
    + intros x I;apply h;now right.
Qed.

(** If [h] is the pointwise sum of [f] and [g], then [sum h l] is the sum of [sum f l] and [sum g l]. *)
Lemma sum_add {A} f g h (l : list A) : (forall x, h x = f x + g x) -> sum h l = sum f l + sum g l.
Proof.
  intro H;induction l;simpl;auto.
  pose proof (H a);lia.
Qed.

Lemma sum_add_distr {A} f g (l : list A) : sum f l + sum g l = sum (fun x => f x + g x) l.
Proof. symmetry;apply sum_add;tauto. Qed.

(** If [f] is uniformly [0] on the elements of the list [l], then [sum f l] is [0]. *)
Lemma sum_zero_in {A} f (l : list A) : (forall x, x ∈ l -> f x = 0) -> sum f l = 0.
Proof.
  induction l;intro hyp;simpl;auto.
  rewrite IHl,(hyp a);auto.
  - now left.
  - intros;apply hyp;now right.
Qed.

(** If [l] is contained in [m] and if [m] has no duplicates, then the length of [l] can be obtained by summing over [m] the function that maps [a] to the number of occurrences of [a] in [l]. *)
Lemma length_sum_filter {A:Set} {d:decidable_set A} l m:
  l ⊆ m -> NoDup m -> ⎢l⎥ = sum (fun a => nb a l) m.
Proof.
  induction l.
  - simpl;intros.
    induction m;simpl;auto.
    apply IHm.
    + intro;simpl;tauto.
    + apply NoDup_cons_iff in H0;tauto.
  - intros I N.
    assert (IH : l ⊆ m) by (intros x h;apply I;now right).
    apply IHl in IH;auto;clear IHl.
    replace ⎢a::l⎥ with (S ⎢l⎥) by reflexivity.
    rewrite IH;clear IH.
    assert (Ia : a ∈ m) by (apply I;now left).
    apply in_split in Ia as (m1&m2&->).
    repeat rewrite sum_app.
    simpl;rewrite (@sum_ext_In _ _ (fun b =>  nb b (a::l))),
          (@sum_ext_In _ _ (fun b => nb b (a::l)) m2).
    + simpl;rewrite eqX_refl;simpl;lia.
    + intros;simpl.
      destruct_eqX x a;subst;auto.
      exfalso;apply NoDup_remove_2 in N.
      apply N,in_app_iff;tauto.
    + intros;simpl.
      destruct_eqX x a;subst;auto.
      exfalso;apply NoDup_remove_2 in N.
      apply N,in_app_iff;tauto.
Qed.    

Lemma sum_le {A} f g (l : list A) :
  (forall a, a∈ l -> f a <= g a) -> sum f l <= sum g l.
Proof.
  induction l as [|a l];simpl.
  - intros _ ;reflexivity.
  - intros h;cut (f a<= g a /\ sum f l <= sum g l);[lia|split].
    + apply h;tauto.
    + apply IHl;intros b I;apply h;tauto.
Qed.

Lemma sum_lt {A} f g (l : list A) :
  (forall a, a∈ l -> f a <= g a) -> (exists b, b ∈ l /\ f b < g b) -> sum f l < sum g l.
Proof.
  induction l as [|a l];simpl.
  - intros _ (b&F&_);tauto.
  - intros h (b&[<-|Ib]&hb).
    + cut (sum f l <= sum g l);[lia|].
      apply sum_le;intros c Ic;apply h;tauto.
    + cut (f a <= g a /\ sum f l < sum g l);[lia|split].
      * apply h;tauto.
      * apply IHl.
        -- intros c Ic;apply h;tauto.
        -- exists b;split;auto.
Qed.

Lemma sum_incr_0_left {A : Set} `{decidable_set A} f (l m : list A) :
  (forall x, ~ x ∈ l -> f x = 0) -> sum f {{l}} = sum f {{m++l}}.
Proof.
  intros;induction m;simpl.
  - reflexivity.
  - case_in a {{m++l}}.
    + assumption.
    + simpl;rewrite H0;[lia|].
      intro I';apply I;simpl_In;tauto.
Qed.

Lemma sum_incr_0_right {A : Set} `{decidable_set A} f (l m : list A) :
  (forall x, ~ x ∈ l -> f x = 0) -> sum f {{l}} = sum f {{l++m}}.
Proof.
  intros h;rewrite (sum_incr_0_left m h).
  apply sum_eq_ND.
  - rewrite app_comm;reflexivity.
  - apply NoDup_undup.
  - apply NoDup_undup.
Qed.

Lemma sum_filter {A : Set} (P : A -> bool) f l : sum f (P:>l) <= sum f l.
Proof. induction l as [|a l];simpl;[|destruct (P a)];simpl;lia. Qed.

(** * Function predicates *)
Class injective {A B} (f : A -> B) :=
  {is_injective : forall x y, f x = f y -> x = y}.
Class surjective {A B} (f : A -> B) :=
  {is_surjective : forall y, exists x, f x = y}.
Class has_support {A} (f : A -> A) l :=
  {is_support : forall x, f x <> x <-> In x l}.
Class supported {A} (f : A -> A) :=
  {is_supported : exists l, has_support f l}.
Lemma has_support_supported {A} f l `{has_support A f l} : supported f.
Proof. split;exists l;auto. Qed.
Hint Resolve has_support_supported.

Global Instance extensional_equality {A B} : SemEquiv (A->B) :=
  { sequiv := fun f g => forall x, f x = g x }.
Global Instance ext_eq_Equiv {A B} : Equivalence (@sequiv (A->B) extensional_equality).
Proof.
  split.
  - intros f x;reflexivity.
  - intros f g E x;rewrite E;reflexivity.
  - intros f g h E1 E2 x;rewrite E1,E2;reflexivity.
Qed.
Global Instance extensional_equality2 {A B C} : SemEquiv (A->B->C) :=
  { sequiv := fun f g => forall x y, f x y = g x y }.
Global Instance ext_eq2_Equiv {A B C} : Equivalence (@sequiv (A->B->C) extensional_equality2).
Proof.
  split.
  - intros f x y;reflexivity.
  - intros f g E x y;rewrite E;reflexivity.
  - intros f g h E1 E2 x y;rewrite E1,E2;reflexivity.
Qed.

Lemma NoDup_map_injective {A B} {f : A->B}  l : injective f -> NoDup l -> NoDup (map f l).
Proof.
  intro inj; induction l;intros N;simpl;auto.
  - apply NoDup_nil.
  - apply NoDup_cons_iff in N as (Ia&N).
    apply NoDup_cons;auto.
    rewrite in_map_iff.
    intros (x&E&Ix);apply Ia.
    apply inj in E as ->;auto.
Qed.

Lemma injective_support_closed {A} f l {x : A} :
  injective f -> has_support f l -> x ∈ l -> f x ∈ l.
Proof.
  intros inj sup I.
  apply sup;intro E.
  apply inj in E.
  apply sup in I;apply I;auto.
Qed.

Global Instance ext_eq_map {A B} : Proper (sequiv ==> sequiv) (@map A B).
Proof. intros f g E x;apply map_ext,E. Qed.
Global Instance ext_eq_sum {A} : Proper (sequiv ==> sequiv) (@sum A).
Proof. intros f g E x;apply sum_ext,E. Qed.
Global Instance ext_eq_filter {A} : Proper (sequiv ==> sequiv) (@filter A).
Proof. intros f g E x;apply filter_ext,E. Qed.
Global Instance ext_eq_fold_left {A B} : Proper (sequiv ==> sequiv) (@fold_left A B).
Proof.
  intros f g E l;induction l;intro x;simpl;auto.
  rewrite (E x a),IHl;reflexivity.
Qed.
Global Instance ext_eq_fold_right {A B} : Proper (sequiv ==> sequiv) (@fold_right A B).
Proof.
  intros f g E x l;revert x;induction l;intro x;simpl;auto.
  rewrite (E a _),IHl;reflexivity.
Qed.
Global Instance injective_ext_eq {A B} : Proper (@sequiv (A->B) _ ==> iff) injective.
Proof.
  intros f g E;split;intros [h];split;intros x y e;apply h.
  - rewrite E,E,e;reflexivity.
  - rewrite <-E,<-E,e;reflexivity.
Qed.
Global Instance surjective_ext_eq {A B} : Proper (@sequiv (A->B) _ ==> iff) surjective.
Proof.
  intros f g E;split;intros [h];split;intros y;destruct (h y) as (x&<-).
  - rewrite E;eauto.
  - rewrite <-E;eauto.
Qed.
Global Instance has_support_ext_eq {A} :
  Proper (@sequiv (A->A) _ ==> (@equivalent A) ==> iff) has_support.
Proof.
  intros f g E l m E';split;intros [h];split;intro x.
  - rewrite <-E,<-E',h;reflexivity.
  - rewrite E,E',h;reflexivity.
Qed.
Global Instance supported_ext_eq {A} :
  Proper (@sequiv (A->A) _ ==> iff) supported.
Proof.
  intros f g E;split; intros [(l&S)].
  - rewrite E in S;eauto.
  - rewrite <-E in S;eauto.
Qed.

Lemma map_injective_injective {A B: Set} (f : A -> B) :
  injective f -> forall l m, map f l = map f m -> l = m.
Proof.
  intro I;induction l as [|a l];intros [|b m];simpl;try reflexivity||discriminate.
  intros e;inversion e as [[e1 e2]].
  apply I in e1;apply IHl in e2.
  congruence.
Qed.

(** * Enumerate permutations of a list *)
Section shuffle.
  Context {A : Set}.

  (** [insert a l] generates the list of all possibles lists [l1::a++l2] such that [l=l1++l2]. *)
  Fixpoint insert (a : A) l :=
    match l with
    | [] => [[a]]
    | b::l => (a::b::l)::(map (cons b) (insert a l))
    end.

  (** [shuffles l] generates the list of all lists obtained by reordering the elements of [l]. For instance [shuffles [a;b]=[[a;b];[b;a]]]. *)
  Fixpoint shuffles l :=
    match l with
    | [] => [[]]
    | a::l => flat_map (insert a) (shuffles l)
    end.

  Lemma insert_spec a l m :
    m ∈ insert a l <-> exists l1 l2, l = l1++l2 /\ m = l1++a::l2.
  Proof.
    revert m;induction l as [|b l];intros m;simpl.
    - split.
      + intros [<-|F];[|tauto];exists [],[];split;reflexivity.
      + intros (l1&l2&h&->);symmetry in h; apply app_eq_nil in h as (->&->).
        simpl;left;reflexivity.
    - rewrite in_map_iff;split.
      + intros [<-|(m'&<-&I)].
        * exists [],(b::l);simpl;split;reflexivity.
        * apply IHl in I as (l1&l2&->&->).
          exists (b::l1),l2;split;reflexivity.
      + intros (l1&l2&e&->).
        destruct l1 as [|c l1].
        * simpl in e;subst;simpl.
          left;reflexivity.
        * simpl in e;inversion e;subst;clear e.
          right;exists (l1++a::l2).
          split;[reflexivity|].
          apply IHl.
          exists l1,l2;tauto.
  Qed.

  
  (** A list [m] appears in [shuffles l] exactly when for every [a:A] there are as may occurrences of [a] in [l] as in [m]. *)
  Lemma shuffles_spec `{decidable_set A} m l : m ∈ shuffles l <-> forall a, nb a l = nb a m.
  Proof.
    revert m;induction l as [|b l];intros m;simpl.
    - split.
      + intros [<-|F];[|tauto].
        intro a;reflexivity.
      + destruct m as [|c m];[tauto|].
        intros h;simpl.
        pose proof (h c) as e;revert e.
        simpl;simpl_beq;simpl.
        discriminate.
    - rewrite in_flat_map;setoid_rewrite IHl;setoid_rewrite insert_spec;split.
      + intros (l'&h&l1&l2&->&->) a.
        pose proof (h a) as e.
        rewrite filter_app in *.
        rewrite app_length in *;simpl.
        clear IHl h;destruct_eqX a b;simpl;lia.
      + intros h.
        exists (m ⊖ b);case_in b m.
        * apply decomposition in I as (l1&l2&->&I).
          rewrite rmfst_in;auto;split.
          -- intros a;pose proof (h a) as e;revert e;clear.
             destruct_eqX a b;simpl.
             ++ repeat rewrite filter_app.
                repeat rewrite app_length in *;simpl.
                simpl_beq;simpl.
                lia.
             ++ repeat rewrite filter_app.
                repeat rewrite app_length in *;simpl.
                simpl_beq;simpl.
                lia.
          -- eauto.
        * pose proof (h b) as e;revert e.
          simpl_beq;simpl.
          apply nb_not_In in I as ->;discriminate.
  Qed.
  (** Shuffles of [l] contain the same elements. *)
  Lemma shuffles_equiv l m : m ∈ shuffles l -> l ≈ m.
  Proof.
    revert m;induction l;intros m h;simpl in *.
    - destruct h as [<-|F];[reflexivity|exfalso;apply F].
    - apply in_flat_map in h as (x&Ix&Im).
      apply insert_spec in Im as (m1&m2&->&->).
      apply IHl in Ix;rewrite Ix;intro;simpl_In;tauto.
  Qed.
  
  (** If [l] has no duplicates and [m] is a shuffle of [l], then [m] has no duplicates either. *)
  Lemma shuffles_nodup l m : NoDup l -> m ∈ shuffles l -> NoDup m.
  Proof.
    revert m;induction l;intros m nd h;simpl in *.
    - destruct h as [<-|F];[apply NoDup_nil|exfalso;apply F].
    - apply in_flat_map in h as (x&Ix&Im).
      apply NoDup_cons_iff in nd as (nI&nd).
      apply insert_spec in Im as (m1&m2&->&->).
      rewrite (shuffles_equiv Ix) in nI;apply (IHl _ nd) in Ix.
      clear IHl l nd;induction m1;simpl.
      + apply NoDup_cons;tauto.
      + simpl in Ix;apply NoDup_cons_iff in Ix as (Ix&nd).
        apply NoDup_cons.
        * clear IHm1 nd; simpl_In in *;firstorder (subst;tauto).
        * apply IHm1;[|assumption].
          clear IHm1 nd; simpl_In in *;firstorder (subst;tauto).
  Qed.
  
  (** Shuffles of [l] have the same length as [l]. *)
  Lemma shuffles_length l m : m ∈ shuffles l -> ⎢l⎥ = ⎢m⎥.
  Proof.
    revert m;induction l;intros m h;simpl in *.
    - destruct h as [<-|F];[reflexivity|exfalso;apply F].
    - apply in_flat_map in h as (x&Ix&Im).
      apply insert_spec in Im as (m1&m2&->&->).
      apply IHl in Ix;rewrite Ix;repeat rewrite app_length;simpl;lia.
  Qed.

  (** If [l] has no duplicates, then [shuffles l] contain exactly the lists that are equivalent to [l] without having any duplicates. *)
  Lemma In_shuffles l m :
    NoDup l -> m ∈ shuffles l <-> l ≈ m /\ NoDup m.
  Proof.
    intros ndl;split;[intro Il;split;[apply shuffles_equiv|apply (shuffles_nodup ndl)];apply Il|].
    revert m;induction l;intros m (e&ndm);simpl.
    - destruct m as [|a m];[tauto|].
      cut (a ∈ []);[intro F;right;apply F|].
      apply e;now left.
    - apply NoDup_cons_iff in ndl as (nI&ndl).
      assert (Em : a ∈ m) by (apply e;now left).
      apply in_split in Em as (m1&m2&->).
      apply in_flat_map;exists (m1++m2);split.
      + pose proof (NoDup_remove_2 _ _ _ ndm) as Ia.
        apply NoDup_remove_1 in ndm.
        apply IHl;[assumption|split;[|assumption]].
        clear IHl ndl ndm.
        intro b;split;simpl_In;intro h.
        -- cut (b ∈ (a::l));[|now right].
           rewrite e;clear e;simpl_In in *;firstorder (subst;tauto).
        -- cut (b ∈ (m1++a::m2)).
           ++ rewrite <-e;clear e.
              simpl_In in *;firstorder (subst;tauto).
           ++ simpl_In in *;tauto.
      + apply insert_spec;exists m1,m2;tauto.
  Qed.

  (** If [l1] is a shuffle of [l2], then being a shuffle of [l1] is equivalent to being a shuffle of [l2]. *)
  Lemma eq_shuffles l1 l2 : l1 ∈ shuffles l2 -> shuffles l1 ≈ shuffles l2.
  Proof.
    revert l1;induction l2;simpl;intros l1.
    - intros [<-|F];[reflexivity|tauto].
    - rewrite in_flat_map;intros (m&Im&Il1).
      apply insert_spec in Il1 as (m1&m2&->&->).
      apply IHl2 in Im;clear IHl2.
      rewrite <- Im;clear Im l2.
      induction m1 as [|b m1];simpl;[reflexivity|].
      rewrite IHm1;clear IHm1.
      generalize (shuffles (m1++m2));intros l x.
      repeat setoid_rewrite in_flat_map;clear m1 m2.
      setoid_rewrite insert_spec.
      transitivity
        (exists l1 l2 m1 m2 , (l1 ++ l2) ∈ l /\ m1 ++ m2 = l1 ++ a :: l2
                         /\ x = m1 ++ b :: m2);
        [firstorder subst;eauto|].
      + exists x4,x5,x1,x2;tauto.
      + transitivity
          (exists l1 l2 m1 m2 , (l1 ++ l2) ∈ l /\ m1 ++ m2 = l1 ++ b :: l2
                           /\ x = m1 ++ a :: m2);
          [|firstorder subst;eauto].
        * split;intros (l1&l2&k1&k2&I&E&Ex);levi E;subst;clear E.
          -- exists l1,l2,(l1++[b]),l2;repeat rewrite app_ass;tauto.
          -- symmetry in E1;inversion E1;subst;clear E1.
             exists (l1++w),k2,l1,(w++b::k2);repeat rewrite app_ass;tauto.
          -- exists k1,(a0::w++l2),(k1++b::a0::w),l2;repeat rewrite app_ass in *;tauto.
          -- exists l1,l2,(l1++[a]),l2;repeat rewrite app_ass;tauto.
          -- symmetry in E1;inversion E1;subst;clear E1.
             exists (l1++w),k2,l1,(w++a::k2);repeat rewrite app_ass;tauto.
          -- exists k1,(a0::w++l2),(k1++a::a0::w),l2;repeat rewrite app_ass in *;tauto.
        * exists x4,x5,x1,x2;tauto.
  Qed.

  (** If [l] has no duplicates, neither does [shuffles l]. *)
  Lemma NoDup_shuffles (l : list A) : NoDup l -> NoDup (shuffles l).
  Proof.
    induction l as [|a l].
    - simpl;intro;apply NoDup_cons;simpl;auto using NoDup_nil.
    - simpl;rewrite NoDup_cons_iff.
      intros (I&nd);pose proof (IHl nd) as IH;clear IHl.
      assert (e: forall m, m ∈ shuffles l -> l ≈ m /\ NoDup m).
      + intros m Im;split.
        * apply shuffles_equiv,Im.
        * apply (shuffles_nodup nd Im).
      + induction (shuffles l) as [|m L];simpl;[apply NoDup_nil|].
        assert (h:m∈(m::L)) by (now left).
        apply e in h as (eq&nd').
        apply NoDup_app.
        * intros m' Im';rewrite in_flat_map.
          intros (m''&IL&Im'').
          apply NoDup_cons_iff in IH as (Im&IH).
          rewrite insert_spec in Im',Im''.
          destruct Im' as (l1&l2&->&->).
          destruct Im'' as (m1&m2&->&E).
          levi E;inversion E1;subst;clear E E1.
          -- tauto.
          -- apply I;rewrite eq;simpl_In;tauto.
          -- apply I;rewrite eq;simpl_In;tauto.
        * revert nd' I;rewrite eq;clear.
          induction m as [|b m];simpl.
          -- intros;apply NoDup_cons;simpl;auto using NoDup_nil.
          -- rewrite NoDup_cons_iff.
             intros (Ib&nd) e;apply NoDup_cons.
             ++ rewrite in_map_iff;intros (l'&E&I).
                inversion E;subst.
                tauto.
             ++ apply NoDup_map_injective.
                ** split;intros l1 l2 E;inversion E;tauto.
                ** apply IHm;tauto.
        * apply IHL.
          -- apply NoDup_cons_iff in IH;tauto.
          -- intros m' Im';apply e;now right.
  Qed.

End shuffle.

(** [insert] commutes with [map]. *)
Lemma insert_map {A B : Set} `{decidable_set A,decidable_set B} :
  forall (f : A -> B) l a, insert (f a) (map f l) = map (map f) (insert a l).
Proof.
  intro f;induction l as [|b l];intro a;simpl.
  - reflexivity.
  - rewrite IHl,map_map,map_map.
    f_equal.
Qed.

(** [shuffles] commutes with [map]. *)
Lemma shuffles_map {A B : Set} `{decidable_set A,decidable_set B} :
  forall (f : A -> B) l, shuffles (map f l) = map (map f) (shuffles l).
Proof.
  intro f;induction l as [|a l];simpl.
  - reflexivity.
  - rewrite IHl,flat_map_concat_map,flat_map_concat_map.
    rewrite map_map,concat_map,map_map.
    f_equal;apply map_ext.
    intros;apply insert_map.
Qed.

Lemma incl_cons_disj' {A : Set} (a : A) m l :
  NoDup m -> m ⊆ a :: l -> m ⊆ l \/ exists m', m ≈ a::m' /\ m' ⊆ l /\ NoDup m'.
Proof.
  induction m as [|b m];simpl.
  - intro;left;apply incl_nil.
  - intros ND I.
    apply NoDup_cons_iff in ND as (nI&ND).
    destruct (IHm ND) as [IH|(m'&E&IH&ND')].
    + intros x Ix;apply I;now right.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m;split;[reflexivity|split;assumption].
      * left;intros c [<-|Ic];[assumption|].
        apply IH,Ic.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m';split;[|split;assumption].
        rewrite E;clear;intro;simpl;tauto.
      * right;exists (b::m');split;[|split].
        -- rewrite E;intro;simpl;tauto.
        -- intros c [<-|Ic];[assumption|].
           apply IH,Ic.
        -- apply NoDup_cons;[|assumption].
           intro F;apply nI,E;now right.
Qed.

Lemma all_subsets_nodup {A : Set} (l : list A) :
  NoDup l -> forall m, m ∈ (flat_map shuffles (subsets l)) <-> NoDup m /\ m ⊆ l.
Proof.
  intros N m;rewrite in_flat_map;split.
  - intros (k&Ik&Im).
    apply In_shuffles in Im as (E&nd).
    + split;[tauto|].
      rewrite <- E;apply subsets_In,Ik.
    + eapply subsets_NoDup;eauto.
  - intros (Nd&Incl).
    apply subsets_spec in Incl as (m'&Im'&E).
    exists m';split;[assumption|].
    apply In_shuffles.
    + apply (subsets_NoDup N);assumption.
    + rewrite <- E;split;[reflexivity|assumption].
Qed.

Section group_by_fst.
  Context {A B : Set} `{decidable_set A}.
  Definition group_by_fst : list (A*B) -> list (list B) :=
    fun l => map (fun a => map snd ((fun p => fst p =?= a):> l)) {{map fst l}}.

  Lemma group_by_fst_length l : ⎢l⎥ = sum (@length B) (group_by_fst l).
  Proof.
    unfold group_by_fst.
    assert (h: prj1 l ⊆ {{prj1 l}}) by (rewrite undup_equivalent;reflexivity).
    assert (nd:NoDup {{prj1 l}}) by (apply NoDup_undup).
    generalize dependent {{prj1 l}};intros L h nd.
    induction l as [|(a,b) l];simpl.
    - clear;induction L;simpl.
      + reflexivity.
      + tauto.
    - rewrite IHl by (rewrite <- h;simpl;apply incl_tl;reflexivity).
      assert (I: a ∈ L) by (apply h;now left).
      apply decomposition in I as (L1&L2&->&_).
      pose proof (NoDup_remove_2 L1 L2 a nd) as I.
      rewrite in_app_iff in I.
      repeat rewrite map_app,sum_app;simpl;rewrite eqX_refl;simpl.
      rewrite <- plus_n_Sm;f_equal;f_equal.
      + f_equal;apply map_ext_in.
        intros c Ic.
        destruct_eqX a c;[|reflexivity].
        subst;exfalso;apply I;tauto.
      + f_equal;f_equal.
        apply map_ext_in.
        intros c Ic.
        destruct_eqX a c;[|reflexivity].
        subst;exfalso;apply I;tauto.
  Qed.

  Lemma group_by_fst_In l b1 b2 :
    (exists c, c ∈ group_by_fst l /\ b1 ∈ c /\ b2 ∈ c) <-> exists a, (a,b1) ∈ l /\ (a,b2) ∈ l.
  Proof.
    unfold group_by_fst.
    setoid_rewrite in_map_iff.
    setoid_rewrite undup_equivalent.
    split.
    - intros (c&(a&<-&Ia)&I1&I2).
      rewrite in_map_iff in I1,I2.
      destruct I1 as ((a1,b1')&e1&I1).
      destruct I2 as ((a2,b2')&e2&I2).
      simpl in *;rewrite e1 in *;rewrite e2 in *;clear e1 e2.
      rewrite filter_In in I1,I2;simpl in *;rewrite eqX_correct in I1,I2.
      destruct I1 as (I1&->).
      destruct I2 as (I2&->).
      exists a;tauto.
    - intros (a&I1&I2).
      exists (prj2 ((fun p => fst p =?= a) :> l)).
      split;[|split].
      + exists a;split;auto.
        apply in_map_iff;exists (a,b1);split;auto.
      + apply in_map_iff;exists (a,b1);split;auto.
        apply filter_In;split;auto.
        simpl;rewrite eqX_refl;reflexivity.
      + apply in_map_iff;exists (a,b2);split;auto.
        apply filter_In;split;auto.
        simpl;rewrite eqX_refl;reflexivity.
  Qed.
  
  Lemma group_by_fst_map_supp l f x :
    x ∈ l <-> (exists c, c ∈ group_by_fst (map (fun x => (f x,x)) l) /\ x ∈ c).
  Proof.
    transitivity (exists a, (a,x)∈ (map (fun x => (f x,x)) l) /\ (a,x)∈ (map (fun x => (f x,x)) l)).
    - split.
      + intro I;exists (f x);split;apply in_map_iff;exists x;split;auto.
      + intros (b&I&_);apply in_map_iff in I as (c&E&Ic).
        inversion E;subst;assumption.
    - rewrite <- group_by_fst_In;clear; firstorder.
  Qed.

  Lemma group_by_fst_map_In l f x1 x2 :
    (exists c, c ∈ group_by_fst (map (fun x => (f x,x)) l) /\ x1 ∈ c /\ x2 ∈ c) <->
    (x1 ∈ l /\ x2 ∈ l /\ f x1 = f x2).
  Proof.
    rewrite group_by_fst_In.
    setoid_rewrite in_map_iff.
    split.
    - intros (a&(b1&E1&I1)&b2&E2&I2);inversion E1;inversion E2;subst;clear E1 E2.
      rewrite H3;tauto.
    - intros (I1&I2&E);exists (f x1);split.
      + exists x1;split;auto.
      + exists x2;rewrite E;split;auto.
  Qed.

End group_by_fst.

(* begin hide *)
Create HintDb length.
Hint Resolve filter_length app_length undup_length : length.

Global Instance le_plus_Proper : Proper (le ==> le ==> le) plus.
Proof. intros ? ? ? ? ? ?;lia. Qed.
Global Instance lt_plus_Proper : Proper (lt ==> lt ==> lt) plus.
Proof. intros ? ? ? ? ? ?;lia. Qed.


(* Tactics *)

Lemma andb_prop_iff x y: Is_true (x && y) <-> Is_true x /\ Is_true y.
Proof.
  split; [apply andb_prop_elim | apply andb_prop_intro].
Qed.

Lemma orb_prop_iff x y: Is_true (x || y) <-> Is_true x \/ Is_true y.
Proof.
  split; [apply orb_prop_elim | apply orb_prop_intro].
Qed.

Hint Rewrite andb_prop_iff orb_prop_iff : quotebool.

Ltac case_equal a b :=
  let E := fresh "E" in
  destruct (X_dec a b) as [E|E];
    [try rewrite E in *|].
Goal (forall n, n = 0 \/ n <> 0).
Proof. intro n;case_equal n 0;tauto. Qed.

Ltac mega_simpl :=
  repeat (simpl in *;
           rewrite in_app_iff
           || match goal with
              | [ h : In _ (map _ _ ) |- _ ] => 
                let u1 := fresh "u" in
                apply in_map_iff in h as (u1&<-&h)
              | [ h : _ \/ _ |- _ ] =>
                destruct h as [h|h]
              | [ h : In _ (_ ++ _ ) |- _ ] =>
                apply in_app_iff in h as [h|h]
              | [ _ : False |- _ ] => tauto
              | |- (forall _, _) => intro
              | |- (_ -> _) => intro
              | |- (In _ (map _ _)) => apply in_map_iff
              | |- (In _ (_ ++ _)) => apply in_app_iff
              | |- (_ /\ _) => split
              | |- (_ \/ False) => left
              | |- (exists _, _) => eexists
              | [ h : In _ ?l |- In _ ?l ] => apply h
              | [ h : In _ ?l |- In _ ?l \/ _ ] => left;apply h
              | [ h : In _ ?l |- _ \/ In _ ?l ] => right;apply h
              end).



Ltac destruct_eqb x o :=
  let Ei := fresh "E" in
  let Ni := fresh "N" in
  let X := fresh "X" in
  destruct (PeanoNat.Nat.eq_dec x o) as [Ei |Ni];
    [pose proof Ei as X;apply PeanoNat.Nat.eqb_eq in X;
     try rewrite Ei in *
    |pose proof Ni as X;apply PeanoNat.Nat.eqb_neq in X];
    try rewrite X in *;clear X;
    repeat  (rewrite <- plus_n_O || rewrite PeanoNat.Nat.eqb_refl).
Ltac destruct_eqX_D D x o :=
  let Ei := fresh "E" in
  let Ni := fresh "N" in
  let X := fresh "X" in
  destruct (@X_dec _ D x o) as [Ei |Ni];
    [pose proof Ei as X;apply (@eqX_correct _ D)in X;
     try rewrite Ei in *
    |pose proof Ni as X;apply  (@eqX_false _ D) in X];
    repeat rewrite X in *;repeat rewrite (eqX_refl D) in *;clear X.
Ltac destruct_ltb x o :=
  let Li := fresh "L" in
  let X := fresh "X" in
  destruct (Compare_dec.le_lt_dec o x) as [Li |Li];
    [pose proof Li as X;apply PeanoNat.Nat.ltb_ge in X
    |pose proof Li as X;apply PeanoNat.Nat.ltb_lt in X];
    try rewrite X in *;clear X;
    repeat (rewrite <- plus_n_O || rewrite PeanoNat.Nat.eqb_refl).

Ltac destruct_leb o x :=
  let Li := fresh "L" in
  let X := fresh "X" in
  destruct (Compare_dec.le_lt_dec o x) as [Li |Li];
    [try rewrite (Compare_dec.leb_correct _ _ Li) in *
    |try rewrite (Compare_dec.leb_correct_conv _ _ Li) in *];
    repeat (rewrite <- plus_n_O || rewrite PeanoNat.Nat.eqb_refl).

Ltac simpl_nat :=
  repeat ((rewrite<-plus_n_O in * )
          || (rewrite PeanoNat.Nat.sub_0_r in * )
          ||(rewrite PeanoNat.Nat.add_sub in * )
          ||(rewrite Minus.minus_plus in * )).

Create HintDb simpl_typeclasses.
Ltac rsimpl := simpl;autorewrite with simpl_typeclasses;simpl.
Tactic Notation "rsimpl" "in" hyp(h) :=
  (simpl in h;autorewrite with simpl_typeclasses in h;simpl in h).
Tactic Notation "rsimpl" "in" "*" :=
  (simpl in *;autorewrite with simpl_typeclasses in *;simpl in *).


Ltac simpl_words :=
  try discriminate;
  match goal with
  | [h: [] = _ ++ _ :: _ |- _ ] => apply app_cons_not_nil in h;tauto
  | [h: _ ++ _ :: _ = [] |- _ ] => symmetry in h;apply app_cons_not_nil in h;tauto
  | [h: _ ++ [_] = _ ++ [_] |- _ ] =>
    let h' := fresh "h" in
    apply app_inj_tail in h as (h,h');
    try discriminate
  end.

   (* end hide *)

(*  LocalWords:  bimap
 *)
