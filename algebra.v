(** * RIS.algebra : algebraic structures. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools.

(** * Definitions *)
Section algebra.
  (** Let [A] be some type equipped with an equivalence relation [⩵] and a partial order [≦]. *)
  Context {A : Type} {eqA: relation A} {leqA : relation A}.
  Context {equivA : @Equivalence A eqA} {preA : @PreOrder A leqA}
          {partialA : @PartialOrder A eqA equivA leqA preA}.

  Infix " ≦ " := leqA (at level 80).
  Infix " ⩵ " := eqA (at level 80).

  (** We introduce some notations. *)
  Class Un := un : A.
  Notation " 𝟭 " := un.

  Class Zero := zero : A.
  Notation " 𝟬 " := zero.
  
  Class Product := prod : A -> A -> A.
  Infix " · " := prod (at level 40).

  Class Join := join : A -> A -> A.
  Infix " ∪ " := join (at level 45).

  Class Star := star : A -> A.
  Notation " e ⋆ " := (star e) (at level 35).

  (** ** Basic properties *)
  Class Associative (prod : A -> A -> A) :=
    associative : (forall a b c : A, prod a (prod b c) ⩵ prod (prod a b) c).
  Class Commutative (prod : A -> A -> A) :=
    commutative : (forall a b : A, prod a b ⩵ prod b a).
  Class Idempotent (prod : A -> A -> A) :=
    idempotent : (forall a : A, prod a a ⩵ a).
  Class Unit (prod : A -> A -> A) (unit : A) :=
    {
      left_unit : forall a : A, prod unit a ⩵ a;
      right_unit : forall a : A, prod a unit ⩵ a
    }.
  Class Absorbing (prod : A -> A -> A) (z : A) :=
    {
      left_absorbing : forall a : A, prod z a ⩵ z;
      right_absorbing : forall a : A, prod a z ⩵ z
    }.

  (** ** Basic structures *)
  Class Monoid (prod : A -> A -> A) (unit : A) :=
    {
      mon_assoc :> Associative prod;
      mon_unit :> Unit prod unit;
    }.

  Class Semilattice (join : A -> A -> A) :=
    { 
      lat_assoc :> Associative join;
      lat_comm :> Commutative join;
      lat_idem :> Idempotent join;
    }.
  
  Class Lattice (m j : A -> A -> A) :=
    { 
      lat_meet_assoc :> Associative m;
      lat_meet_comm :> Commutative m;
      lat_join_assoc :> Associative j;
      lat_join_comm :> Commutative j;
      lat_join_meet : forall a b, j a (m a b) ⩵ a;
      lat_meet_join : forall a b, m a (j a b) ⩵ a;
    }.

  Class SemiRing (prod add : A -> A -> A) (u z : A) :=
    {
      semiring_prod :> Monoid prod u;
      semiring_add :> Monoid add z;
      semiring_comm :> Commutative add;
      semiring_zero :> Absorbing prod z;
      semiring_left_distr : forall a b c, prod a (add b c) ⩵ add (prod a b) (prod a c);
      semiring_right_distr : forall a b c, prod (add a b) c ⩵ add (prod a c) (prod b c);
    }.

  (** The property [JoinOrder] states that the partial order we choose
  coincides with the natural ordering we get from a join
  [Semilattice]. *)
  Class JoinOrder j :=
    join_is_order : forall x y, x ≦ y <-> y ⩵ j x y.

  (** An idempotent semi-ring is in particular a semi-lattice. *)
  Global Instance IdemSemiRing_Semilattice p j u z `{SemiRing p j u z} `{Idempotent j} : Semilattice j.
  Proof.
    split.
    - cut (Monoid j z).
      + intro;apply mon_assoc.
      + apply semiring_add.
    - apply semiring_comm.
    - assumption.
  Qed.

  (** ** Kleene algebra and Boolean algebra *)
  Class KleeneAlgebra (j: Join) (p: Product) (z: Zero) (u:Un) (s:Star) :=
    {
      proper_prod :> Proper (eqA ==> eqA ==> eqA) prod;
      proper_join :> Proper (eqA ==> eqA ==> eqA) join;
      proper_star :> Proper (eqA ==> eqA) star;
      ka_semiring :> SemiRing prod join un zero;
      ka_idem :> Idempotent join;
      ka_joinOrder :> JoinOrder join;
      ka_star_unfold : forall a, 𝟭 ∪ a · a ⋆ ≦ a⋆ ;
      ka_star_left_ind : forall a b, a · b ≦ b -> a ⋆ · b ≦ b;
      ka_star_right_ind : forall a b, a · b ≦ a -> a · b ⋆ ≦ a;
    }.

  Class BooleanAlgebra (t f : A) (n : A -> A) (c d: A -> A -> A) :=
    {
      proper_c :> Proper (eqA ==> eqA ==> eqA) c;
      proper_d :> Proper (eqA ==> eqA ==> eqA) d;
      proper_n :> Proper (eqA ==> eqA) n;
      ba_conj_comm :> Commutative c;
      ba_disj_comm :> Commutative d;
      ba_true : forall a, c a t ⩵ a;
      ba_false : forall a, d a f ⩵ a;
      ba_conj_disj : forall x y z, c x (d y z) ⩵ d (c x y) (c x z);
      ba_disj_conj : forall x y z, d x (c y z) ⩵ c (d x y) (d x z);
      ba_neg_conj : forall a, c a (n a) ⩵ f;
      ba_neg_disj : forall a, d a (n a) ⩵ t;
    }.
  
End algebra.
Arguments Zero: clear implicits.
Arguments Un: clear implicits.
Arguments Product: clear implicits.
Arguments Join: clear implicits.
Arguments Star: clear implicits.
Notation " 𝟭 " := un.
Notation " 𝟬 " := zero.
Infix " · " := prod (at level 40).
Infix " ∪ " := join (at level 45).
Notation " e ⋆ " := (star e) (at level 35).

Arguments KleeneAlgebra : clear implicits.
Arguments KleeneAlgebra A eqA leqA {j p z u s}.
Arguments SemiRing : clear implicits.
Arguments JoinOrder : clear implicits.
Arguments Semilattice : clear implicits.
Arguments BooleanAlgebra : clear implicits.
Arguments BooleanAlgebra {A} eqA t f n c d.

(** * Facts about boolean algebra *)
Section booleanAlgebra.
  Context {A : Type} {eqA: relation A} {leqA : relation A}.
  Context {equivA : @Equivalence A eqA} {preA : @PreOrder A leqA}
          {partialA : @PartialOrder A eqA equivA leqA preA}.

  Infix " ≦ " := leqA (at level 80).
  Infix " ⩵ " := eqA (at level 80).
  Context {top bot : A} {neg : A -> A} {conj disj : A -> A -> A}.
  Context `{BooleanAlgebra A eqA top bot neg conj disj}.

  Notation " ⊤ " := top.
  Notation " ⊥ " := bot.
  Notation " ¬ " := neg.
  Infix " ∧ " := conj (at level 40).
  Infix " ∨ " := disj (at level 45).

  (** When we defined boolean algebra before, we relied on
  Huntington's 1904 axiomatization, which differs from the usual way
  they are defined, but is much more concise. We now show that this
  axiomatization indeed implies all the properties we expect of a
  boolean algebra. The following subsection is a straightforward
  adaptation of the proofs detailed on the wikipedia page of boolean
  algebra: 
  #<a href="https://en.wikipedia.org/wiki/Boolean_algebra_(structure)##Axiomatics">en.wikipedia.org/wiki/Boolean_algebra_(structure)</a>#.*)

  (** ** Elementary properties *)
  Lemma UId1 o : (forall x, x ∨ o ⩵ x) -> o ⩵ ⊥.
  Proof.
    intros hyp.
    rewrite <- (ba_false o).
    rewrite (ba_disj_comm _ _).
    apply hyp.
  Qed.
  
  Lemma Idm1 x : x ∨ x ⩵ x.
  Proof.
    rewrite <- (ba_true (x∨x)),<-(ba_neg_disj x).
    rewrite <- ba_disj_conj,ba_neg_conj.
    apply ba_false.
  Qed.

  Lemma Bnd1 x : x ∨ ⊤ ⩵ ⊤.
  Proof.
    rewrite <- (ba_true (x∨⊤)),(ba_conj_comm _ _).
    rewrite <- (ba_neg_disj x) at 1.
    rewrite <- ba_disj_conj,ba_true.
    apply ba_neg_disj.
  Qed.

  Lemma Abs1 x y : x ∨ (x ∧ y) ⩵ x.
  Proof.
    rewrite <- (ba_true x) at 1.
    rewrite <- ba_conj_disj,(ba_disj_comm _ _),Bnd1.
    apply ba_true.
  Qed.

  Lemma UId2 o : (forall x, x ∧ o ⩵ x) -> o ⩵ ⊤.
  Proof.
    intros hyp.
    rewrite <- (ba_true o).
    rewrite (ba_conj_comm _ _).
    apply hyp.
  Qed.
  
  Lemma Idm2 x : x ∧ x ⩵ x.
  Proof.
    rewrite <- (ba_false (x∧x)),<-(ba_neg_conj x).
    rewrite <- ba_conj_disj,ba_neg_disj.
    apply ba_true.
  Qed.

  Lemma Bnd2 x : x ∧ ⊥ ⩵ ⊥.
  Proof.
    rewrite <- (ba_false (x∧⊥)),(ba_disj_comm _ _).
    rewrite <- (ba_neg_conj x) at 1.
    rewrite <- ba_conj_disj,ba_false.
    apply ba_neg_conj.
  Qed.

  Lemma Abs2 x y : x ∧ (x ∨ y) ⩵ x.
  Proof.
    rewrite <- (ba_false x) at 1.
    rewrite <- ba_disj_conj,(ba_conj_comm _ _),Bnd2.
    apply ba_false.
  Qed.
  
  Lemma UNg x x' : x ∨ x' ⩵ ⊤ -> x ∧ x' ⩵ ⊥ -> x' ⩵ ¬ x.
  Proof.
    intros h1 h2.
    rewrite <- (ba_true x'),<-(ba_neg_disj x),ba_conj_disj,(ba_conj_comm x' _),(ba_conj_comm x' _).
    rewrite h2.
    rewrite <- (ba_neg_conj x),(ba_conj_comm _ _),<-ba_conj_disj.
    rewrite h1.
    apply ba_true.
  Qed.

  Lemma DNg x : ¬(¬ x) ⩵ x.
  Proof.
    symmetry;apply UNg.
    - rewrite (ba_disj_comm _ _);apply ba_neg_disj.
    - rewrite (ba_conj_comm _ _);apply ba_neg_conj.
  Qed.

  Lemma A1 x y : x ∨ (¬ x ∨ y) ⩵ ⊤.
  Proof.
    rewrite <- (ba_true (x∨_)),(ba_conj_comm _ _),<-(ba_neg_disj x).
    rewrite <- ba_disj_conj.
    rewrite Abs2;reflexivity.
  Qed.

  Lemma A2 x y : x ∧ (¬ x ∧ y) ⩵ ⊥.
  Proof.
    rewrite <- (ba_false (x∧_)),(ba_disj_comm _ _),<-(ba_neg_conj x).
    rewrite <- ba_conj_disj.
    rewrite Abs1;reflexivity.
  Qed.

  Lemma B1 x y : (x ∨ y)∨(¬x∧¬y)⩵⊤.
  Proof.
    rewrite ba_disj_conj.
    rewrite (ba_disj_comm _ (¬x)), (ba_disj_comm _ (¬y)).
    rewrite (ba_disj_comm x y) at 2.
    rewrite <- (DNg x) at 2.
    rewrite <- (DNg y) at 3.
    repeat rewrite A1.
    apply ba_true.
  Qed.
    
  Lemma B2 x y : (x ∧ y)∧(¬x∨¬y)⩵⊥.
  Proof.
    rewrite ba_conj_disj.
    rewrite (ba_conj_comm _ (¬x)), (ba_conj_comm _ (¬y)).
    rewrite (ba_conj_comm x y) at 2.
    rewrite <- (DNg x) at 2.
    rewrite <- (DNg y) at 3.
    repeat rewrite A2.
    apply ba_false.
  Qed.

  Lemma C1 x y : (x ∨ y)∧ (¬x∧¬y)⩵⊥.
  Proof.
    rewrite (ba_conj_comm (x∨_) _),ba_conj_disj.
    rewrite (ba_conj_comm _ x),(ba_conj_comm _ y).
    rewrite (ba_conj_comm _ (¬y)) at 2.
    repeat rewrite A2.
    apply ba_false.
  Qed.

  Lemma C2 x y : (x ∧ y)∨ (¬x∨¬y)⩵⊤.
  Proof.
    rewrite (ba_disj_comm (x∧_) _),ba_disj_conj.
    rewrite (ba_disj_comm _ x),(ba_disj_comm _ y).
    rewrite (ba_disj_comm _ (¬y)) at 2.
    repeat rewrite A1.
    apply ba_true.
  Qed.

  Lemma DMg1 x y : ¬ (x∨y) ⩵ ¬ x ∧ ¬ y.
  Proof.
    symmetry;apply UNg.
    - apply B1.
    - apply C1.
  Qed.

  Lemma DMg2 x y : ¬ (x∧y) ⩵ ¬ x ∨ ¬ y.
  Proof.
    symmetry;apply UNg.
    - apply C2.
    - apply B2.
  Qed.

  Lemma D1 x y z : (x∨(y∨z))∨¬x⩵⊤.
  Proof.
    rewrite (ba_disj_comm _ (¬x)).
    rewrite <- (DNg x) at 2.
    apply A1.
  Qed.

  Lemma D2 x y z : (x∧(y∧z))∧¬x⩵⊥.
  Proof.
    rewrite (ba_conj_comm _ (¬x)).
    rewrite <- (DNg x) at 2.
    apply A2.
  Qed.

  Lemma E1 x y z : y∧(x∨(y∨z))⩵ y.
  Proof.
    rewrite ba_conj_disj,Abs2,(ba_disj_comm _).
    apply Abs1.
  Qed.

  Lemma E2 x y z : y∨(x∧(y∧z))⩵ y.
  Proof.
    rewrite ba_disj_conj,Abs1,(ba_conj_comm _).
    apply Abs2.
  Qed.

  Lemma F1 x y z : (x∨(y∨z))∨¬y ⩵ ⊤.
  Proof.
    rewrite (ba_disj_comm _ (¬ _)).
    rewrite <- ba_true,(ba_conj_comm _ _),<-(ba_neg_disj y) at 1.
    rewrite (ba_disj_comm y),<-ba_disj_conj,E1,(ba_disj_comm _ y).
    apply ba_neg_disj.
  Qed.

  Lemma F2 x y z : (x∧(y∧z))∧¬y ⩵ ⊥.
  Proof.
    rewrite (ba_conj_comm _ (¬ _)).
    rewrite <- ba_false,(ba_disj_comm _ _),<-(ba_neg_conj y) at 1.
    rewrite (ba_conj_comm y),<-ba_conj_disj,E2,(ba_conj_comm _ y).
    apply ba_neg_conj.
  Qed.

  Lemma G1 x y z : (x ∨(y∨z))∨¬z⩵⊤.
  Proof. rewrite (ba_disj_comm y z);apply F1. Qed.

  Lemma G2 x y z : (x ∧(y∧z))∧¬z⩵⊥.
  Proof. rewrite (ba_conj_comm y z);apply F2. Qed.

  Lemma H1 x y z : ¬ ((x∨y)∨z)∧x⩵⊥.
  Proof.
    rewrite DMg1,DMg1.
    rewrite (ba_conj_comm _).
    rewrite <- ba_false,(ba_disj_comm _).
    rewrite <- (ba_neg_conj x) at 1.
    rewrite <- ba_conj_disj,(ba_conj_comm _ (¬z)),E2.
    apply ba_neg_conj.
  Qed.

  Lemma H2 x y z : ¬ ((x∧y)∧z)∨x⩵⊤.
  Proof.
    rewrite DMg2,DMg2.
    rewrite (ba_disj_comm _).
    rewrite <- ba_true,(ba_conj_comm _).
    rewrite <- (ba_neg_disj x) at 1.
    rewrite <- ba_disj_conj,(ba_disj_comm _ (¬z)),E1.
    apply ba_neg_disj.
  Qed.

  Lemma I1 x y z : ¬ ((x∨y)∨z)∧y⩵⊥.
  Proof. rewrite (ba_disj_comm x y);apply H1. Qed.

  Lemma I2 x y z : ¬ ((x∧y)∧z)∨y⩵⊤.
  Proof. rewrite (ba_conj_comm x y);apply H2. Qed.

  Lemma J1 x y z : ¬((x∨y)∨z)∧z⩵⊥.
  Proof. rewrite DMg1,(ba_conj_comm _),(ba_conj_comm (¬ _));apply A2. Qed.

  Lemma J2 x y z : ¬((x∧y)∧z)∨z⩵⊤.
  Proof. rewrite DMg2,(ba_disj_comm _),(ba_disj_comm (¬ _));apply A1. Qed.

  Lemma K1 x y z : (x∨(y∨z))∨¬((x∨y)∨z)⩵⊤.
  Proof.
    repeat rewrite DMg1.
    repeat rewrite ba_disj_conj.
    rewrite D1,F1,G1.
    repeat rewrite ba_true;reflexivity.
  Qed.
  
  Lemma K2 x y z : (x∧(y∧z))∧¬((x∧y)∧z)⩵⊥.
  Proof.
    repeat rewrite DMg2.
    repeat rewrite ba_conj_disj.
    rewrite D2,F2,G2.
    repeat rewrite ba_false;reflexivity.
  Qed.
  
  Lemma L1 x y z : (x∨(y∨z))∧¬((x∨y)∨z) ⩵ ⊥.
  Proof.
    rewrite (ba_conj_comm _).
    repeat rewrite ba_conj_disj.
    rewrite H1,I1,J1.
    repeat rewrite ba_false;reflexivity.
  Qed.
  
  Lemma L2 x y z : (x∧(y∧z))∨¬((x∧y)∧z) ⩵ ⊤.
  Proof.
    rewrite (ba_disj_comm _).
    repeat rewrite ba_disj_conj.
    rewrite H2,I2,J2.
    repeat rewrite ba_true;reflexivity.
  Qed.

  Lemma Ass1 x y z : x∨(y∨z)⩵(x∨y)∨z.
  Proof.
    rewrite <- (DNg ((x∨y)∨z));apply UNg.
    - rewrite (ba_disj_comm _);apply K1.
    - rewrite (ba_conj_comm _);apply L1.
  Qed.

  Lemma Ass2 x y z : x∧(y∧z)⩵(x∧y)∧z.
  Proof.
    rewrite <- (DNg ((x∧y)∧z));apply UNg.
    - rewrite (ba_disj_comm _);apply L2.
    - rewrite (ba_conj_comm _);apply K2.
  Qed.

  (** ** Boolean algebra as other structures*)
  Global Instance BooleanAlgebra_Join_Lattice : @Lattice A eqA conj disj.
  Proof.
    split.
    - intros x y z;apply Ass2.
    - apply ba_conj_comm.
    - intros x y z;apply Ass1.
    - apply ba_disj_comm.
    - apply Abs1.
    - apply Abs2.
  Qed.
  
  Global Instance BooleanAlgebra_Join_Semilattice : Semilattice A eqA disj.
  Proof.
    split.
    - apply lat_join_assoc.
    - apply lat_join_comm.
    - intros a;apply Idm1.
  Qed.

  Global Instance BooleanAlgebra_Meet_Semilattice : Semilattice A eqA conj.
  Proof.
    split.
    - apply lat_meet_assoc.
    - apply lat_meet_comm.
    - intros a;apply Idm2.
  Qed.

  Global Instance BooleanAlgebra_Meet_Monoid : @Monoid A eqA conj top.
  Proof.
    split.
    - apply lat_meet_assoc.
    - split.
      + intro a;etransitivity;[apply lat_meet_comm|apply ba_true].
      + apply ba_true.
  Qed.

  Global Instance BooleanAlgebra_Join_Monoid : @Monoid A eqA disj bot.
  Proof.
    split.
    - apply lat_join_assoc.
    - split.
      + intro a;etransitivity;[apply lat_join_comm|apply ba_false].
      + apply ba_false.
  Qed.

  Global Instance BooleanAlgebra_Semiring : SemiRing A eqA conj disj top bot.
  Proof.
    split.
    - eapply BooleanAlgebra_Meet_Monoid;eassumption.
    - eapply BooleanAlgebra_Join_Monoid;eassumption.
    - apply lat_join_comm.
    - split.
      + intros a;rewrite (ba_conj_comm _);apply Bnd2.
      + intros a;apply Bnd2.
    - apply ba_conj_disj.
    - intros x y z;rewrite (ba_conj_comm _),ba_conj_disj.
      repeat rewrite (ba_conj_comm z);reflexivity.
  Qed.

End booleanAlgebra.
  
(** * Join semi-lattices *)
Section joinSemiLattice.
  Context {A : Type} {eqA: relation A} {leqA : relation A}.
  Context {equivA : @Equivalence A eqA} {preA : @PreOrder A leqA}
          {partialA : @PartialOrder A eqA equivA leqA preA}.

  Infix " ≦ " := leqA (at level 80).
  Infix " ⩵ " := eqA (at level 80).
  Context {j : Join A} {semLatA: Semilattice A eqA join}.
  Context {proper_join: Proper (eqA ==> eqA ==> eqA) join}.

  Lemma refactor e f g h : (e ∪ f) ∪ (g ∪ h) ⩵ (e ∪ g) ∪ (f ∪ h).
  Proof.
    rewrite (lat_assoc (e∪f) g h).
    rewrite <- (lat_assoc e f g).
    rewrite (lat_comm f g).
    rewrite (lat_assoc e g f).
    rewrite (lat_assoc (e∪g) f h).
    reflexivity.
  Qed.

  Context {joA : JoinOrder A eqA leqA join}.
  
  Global Instance proper_join_inf : Proper (leqA ==> leqA ==> leqA) join.
  Proof.
    intros x y I x' y' I';rewrite join_is_order in *.
    rewrite I,I' at 1;apply refactor.
  Qed.

  Lemma inf_cup_left a b : a ≦ a ∪ b.
  Proof. apply join_is_order; rewrite (lat_assoc _ _ _),(lat_idem _);reflexivity. Qed.

  Lemma inf_cup_right a b : b ≦ a ∪ b.
  Proof. rewrite (lat_comm a b);apply inf_cup_left. Qed.

  Lemma inf_join_inf a b c : a ≦ c -> b ≦ c -> a ∪ b ≦ c.
  Proof. intros;rewrite <- (lat_idem c); apply proper_join_inf;assumption. Qed.

  Context {z : Zero A} {u : @Unit A eqA join zero}.
  
  Lemma zero_minimal x : zero ≦ x.
  Proof. rewrite join_is_order;symmetry ;apply left_unit. Qed.
  
End joinSemiLattice.

(** * Kleene algebras *)
Section ka_facts.
  Context {A : Type} {eqA: relation A} {leqA : relation A}.
  Context {equivA : @Equivalence A eqA} {preA : @PreOrder A leqA}
          {partialA : @PartialOrder A eqA equivA leqA preA}.

  Infix " ≦ " := leqA (at level 80).
  Infix " ⩵ " := eqA (at level 80).
  
  Context {j: Join A}{p: Product A}{z: Zero A}{u:Un A}{s:Star A}.
  Context {ka: KleeneAlgebra A eqA leqA}.


  Global Instance proper_join_eq : Proper (eqA ==> eqA ==> eqA) join.
  Proof. destruct ka;assumption. Qed.
  
  Global Instance proper_prod_inf : Proper (leqA ==> leqA ==> leqA) prod.
  Proof.
    intros e f I e' f' I'.
    rewrite join_is_order in *.
    rewrite I' at 1.
    rewrite semiring_left_distr.
    rewrite I at 1.
    rewrite semiring_right_distr.
    rewrite <- (mon_assoc _ _ _).
    rewrite <- semiring_left_distr.
    rewrite <- I'.
    reflexivity.
  Qed.    
  
  Global Instance join_semilattice : Semilattice A eqA join.
  Proof. destruct ka;eapply IdemSemiRing_Semilattice;eauto. Qed.
  
  Lemma ka_star_unfold_eq a : a⋆ ⩵ 𝟭 ∪ a · a ⋆.
  Proof.
    apply partialA;split.
    - etransitivity;[|apply ka_star_left_ind with (a0:=a)].
      + rewrite (semiring_left_distr _ _ _).
        rewrite right_unit. 
        apply inf_cup_left.
      + rewrite (semiring_left_distr _ _ _).
        rewrite right_unit.
        apply inf_join_inf.
        * rewrite <- inf_cup_right.
          rewrite <- ka_star_unfold.
          rewrite (semiring_left_distr _ _ _).
          rewrite <- inf_cup_left.
          rewrite right_unit.
          reflexivity.
        * rewrite <- ka_star_unfold at 2.
          rewrite <- inf_cup_right.
          rewrite (semiring_left_distr _ _ _).
          rewrite <- inf_cup_right.
          reflexivity.
    - unfold Basics.flip.
      apply ka_star_unfold.
  Qed.
  
  Lemma ka_star_dup a : a ⋆ · a ⋆ ⩵ a ⋆.
  Proof.
    apply partialA;split.
    - apply ka_star_left_ind.
      rewrite ka_star_unfold_eq at 2.
      apply inf_cup_right.
    - unfold Basics.flip.
      rewrite ka_star_unfold_eq at 1.
      apply inf_join_inf.
      + rewrite ka_star_unfold_eq.
        rewrite (semiring_left_distr _ _ _).
        rewrite (semiring_right_distr _ _ _).
        rewrite <- inf_cup_left.
        rewrite <- inf_cup_left.
        rewrite left_unit.
        reflexivity.
      + apply proper_prod_inf;[|reflexivity].
        rewrite ka_star_unfold_eq.
        rewrite <- inf_cup_right.
        rewrite ka_star_unfold_eq.
        rewrite (semiring_left_distr _ _ _).
        rewrite <- inf_cup_left.
        rewrite right_unit.
        reflexivity.
  Qed.

  Lemma one_inf_star e : 𝟭 ≦ e⋆.
  Proof. rewrite ka_star_unfold_eq;apply inf_cup_left. Qed.

  Lemma star_incr e : e ≦ e⋆.
  Proof. rewrite ka_star_unfold_eq, <- one_inf_star,right_unit;apply inf_cup_right. Qed.
    
  Global Instance proper_star_inf : Proper (leqA ==> leqA) star.
  Proof.
    intros e f I.
    transitivity (e⋆·𝟭);[rewrite right_unit;reflexivity|].
    rewrite (one_inf_star f).
    apply ka_star_left_ind.
    rewrite I,(star_incr f),ka_star_dup at 1;reflexivity.
  Qed.
  
  Lemma ka_star_star a : a⋆ ⩵ (a ⋆)⋆.
  Proof.
    apply partialA;split;unfold Basics.flip.
    - apply proper_star_inf.
      rewrite ka_star_unfold_eq.
      rewrite <- inf_cup_right.
      rewrite ka_star_unfold_eq.
      rewrite (semiring_left_distr _ _ _).
      rewrite right_unit.
      apply inf_cup_left.
    - rewrite ka_star_unfold_eq at 1.
      apply inf_join_inf.
      + rewrite ka_star_unfold_eq.
        apply inf_cup_left.
      + apply ka_star_right_ind.
        rewrite ka_star_dup.
        reflexivity.
  Qed.        
  
  Lemma ka_star_unfold_right a : 𝟭 ∪ a⋆ · a ≦ a⋆.
  Proof.
    apply inf_join_inf.
    - rewrite ka_star_unfold_eq.
      apply inf_cup_left.
    - rewrite <- ka_star_dup at 2.
      apply proper_prod_inf.
      + reflexivity.
      + rewrite ka_star_unfold_eq,ka_star_unfold_eq.
        rewrite semiring_left_distr,right_unit.
        rewrite <- inf_cup_right.
        apply inf_cup_left.
  Qed.

  Lemma star_join e f : (e ∪ f)⋆ ⩵ e ⋆ ∪ f⋆·(e·f⋆)⋆.
  Proof.
    apply partialA;unfold Basics.flip;split.
    - transitivity ((e ∪ f) ⋆ · un);[rewrite right_unit;reflexivity|].
      transitivity ((e ∪ f) ⋆ · (e ⋆ ∪ f ⋆ · (e · f ⋆) ⋆)).
      + apply proper_prod_inf;[reflexivity|].
        etransitivity;[|apply inf_cup_left].
        apply one_inf_star.
      + apply ka_star_left_ind.
        rewrite semiring_left_distr.
        repeat rewrite semiring_right_distr.
        repeat apply inf_join_inf.
        * etransitivity;[|apply inf_cup_left].
          rewrite (star_incr e) at 1.
          rewrite ka_star_dup;reflexivity.
        * etransitivity;[|apply inf_cup_right].
          apply proper_prod_inf;[apply star_incr|].
          rewrite <- (one_inf_star f),right_unit;reflexivity.
        * etransitivity;[|apply inf_cup_right].
          rewrite <- (one_inf_star f) at 3;rewrite left_unit.
          rewrite <- (ka_star_dup (e·f⋆)) at 2.
          rewrite <- (star_incr (e·f⋆)) at 2.
          rewrite (mon_assoc _ _ _).
          reflexivity.
        * etransitivity;[|apply inf_cup_right].
          rewrite (mon_assoc _ _ _).
          apply proper_prod_inf;[|reflexivity].
          rewrite (star_incr f) at 1;rewrite ka_star_dup;reflexivity.
    - apply inf_join_inf.
      + apply proper_star_inf,inf_cup_left.
      + rewrite <- (ka_star_dup (e∪f)).
        apply proper_prod_inf;[apply proper_star_inf,inf_cup_right|].
        rewrite (ka_star_star (e∪f)).
        apply proper_star_inf.
        rewrite <- (ka_star_dup (e∪f)).
        apply proper_prod_inf;[|apply proper_star_inf,inf_cup_right].
        rewrite <- star_incr;apply inf_cup_left.
  Qed.    

  Lemma un_star : un⋆ ⩵ un.
  Proof.
    apply partialA;unfold Basics.flip;split.
    - transitivity (un⋆·un);[rewrite right_unit;reflexivity|].
      apply ka_star_left_ind;rewrite left_unit;reflexivity.
    - apply star_incr.
  Qed.

  Lemma star_switch_side e : e⋆·e ⩵ e· e⋆.
  Proof.
    apply partialA;unfold Basics.flip;split.
    - transitivity (e⋆·e·e⋆).
      + rewrite <- one_inf_star at 3.
        rewrite right_unit;reflexivity.
      + rewrite <- (mon_assoc _ _ _).
        apply ka_star_left_ind.
        rewrite (star_incr e) at 2.
        rewrite ka_star_dup;reflexivity.
    - transitivity (e⋆·e·e⋆).
      + rewrite <- one_inf_star at 2.
        rewrite left_unit;reflexivity.
      + apply ka_star_right_ind.
        rewrite (star_incr e) at 2.
        rewrite ka_star_dup;reflexivity.
  Qed.

  Definition Σ l := fold_right (fun e f => join e f) zero l.

  Lemma Σ_distr_l e L : e · Σ L ⩵ Σ (map (prod e) L).
  Proof.
    induction L;simpl.
    - apply right_absorbing.
    - rewrite <- IHL,semiring_left_distr;reflexivity.
  Qed.
  
  Lemma Σ_distr_r e L : Σ L · e ⩵ Σ (map (fun f => f · e) L).
  Proof.
    induction L;simpl.
    - apply left_absorbing.
    - rewrite <- IHL,semiring_right_distr;reflexivity.
  Qed.

  Lemma Σ_app L M : Σ L ∪ Σ M ⩵ Σ (L++M).
  Proof.
    induction L;simpl;[|rewrite <- IHL].
    - apply left_unit.
    - symmetry;apply mon_assoc.
  Qed.
      
  Lemma Σ_incl L M : L ⊆ M -> Σ L ≦ Σ M.
  Proof.
    intro I;apply ka_joinOrder;rewrite Σ_app;revert M I;induction L;intros M I.
    - reflexivity.
    - simpl;rewrite <- IHL by (rewrite <- I;intro;simpl;tauto).
      assert (Ia : a ∈ M) by (apply I;now left).
      clear I L IHL.
      induction M as [|e L].
      + simpl in *;tauto.
      + simpl;destruct Ia as [->|Ia];simpl.
        * rewrite (mon_assoc _ _ _),(ka_idem _);reflexivity.
        * rewrite IHL at 1 by assumption.
          rewrite (mon_assoc _ _ _),(semiring_comm e a),(mon_assoc _ _ _);reflexivity.
  Qed.  
  
  Global Instance Σ_equivalent : Proper (@equivalent _ ==> eqA) Σ.
  Proof.
    intros l1 l2 E.
    apply incl_PartialOrder in E as (E1&E2);unfold Basics.flip in E2.
    apply Σ_incl,ka_joinOrder in E1; apply Σ_incl,ka_joinOrder in E2. 
    rewrite E1, E2 at 1;apply semiring_comm.
  Qed.

  Lemma Σ_bigger e L : e ∈ L -> e ≦ Σ L.
  Proof.
     intro I;transitivity (Σ [e]).
     - simpl;apply inf_cup_left.
     - apply Σ_incl;intros ? [<-|F];simpl in *;tauto.
  Qed.
  
  Lemma Σ_bounded e L : (forall f, f ∈ L -> f ≦ e) <-> Σ L ≦ e.
  Proof.
    split.
    - induction L;simpl;intro I.
      + apply zero_minimal.
      + rewrite IHL by (intros ? ?;apply I;now right).
        rewrite (I a) by now left.
        rewrite (ka_idem e);reflexivity.
    - intros E f If.
      rewrite <- E;apply Σ_bigger,If.
  Qed.

  Lemma ka_star_mid_split e : e⋆·e·e⋆ ≦ e⋆.
  Proof.
    etransitivity;[apply proper_prod_inf;[apply proper_prod_inf;
                                          [reflexivity|apply star_incr]|reflexivity]|].
    cut ((e ⋆ · e ⋆) · e ⋆ ⩵ e ⋆);[intros ->;reflexivity|].
    etransitivity;[apply proper_prod;[apply ka_star_dup|]|apply ka_star_dup].
    reflexivity.
  Qed.

  Lemma ka_zero_star :  𝟬 ⋆ ⩵ 𝟭.
  Proof.
    symmetry;apply partialA;unfold Basics.flip;split.
    - apply one_inf_star.
    - transitivity (𝟬 ⋆ · 𝟭).
      + rewrite right_unit;reflexivity.
      + apply ka_star_left_ind.
        rewrite left_absorbing;apply zero_minimal.
  Qed.

End ka_facts.

  

