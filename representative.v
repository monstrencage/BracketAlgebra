(** * RIS.representative : generic representation of nominal sets. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export nominalsetoid bijection words.

(** * Orbits *)
Section orbits.
  (** ** Definitions *)
  (** We fix for this section a set of atoms [atom]. *)
  Context {atom : Set}{𝐀 : Atom atom}.

  (** The base type for orbits is as follows: *)
  Definition orbit_base : Set := list atom * list (list (list atom)).

  (** It naturally forms a nominal set over [atom]. *)
  Global Instance Nominal_orbit_base : Nominal 𝐀 orbit_base :=
    Nominal_Pair (list atom) (list (list (list atom))).

  (** If [A] is a list of lists atoms, [E] is a partition of [A] if 
      - the lists appearing in [A] are exactly the lists appearing inside some [c ∈ E], i.e.: [{m|m∈A}={m|∃c∈E: m∈c}];
      - and the lists appearing in [E] are pairwise disjoint, meaning that if [c1] and [c2] are in [E] and there exists a list [l] appearing both in [c1] and [c2], then [c1] and [c2] must contain exactly the same elements.
   *)
  Definition partition E (A : list (list atom)) :=
    (forall m, m ∈ A <-> exists c, c ∈ E /\ m ∈ c)
    /\ (forall l c1 c2, c1 ∈ E -> c2 ∈ E -> l ∈ c1 -> l ∈ c2 -> c1 ≈ c2).

  (** This property is decidable, and may be checked by the following boolean function. *)
  Definition partitionb E (A : list (list atom)) :=
    (equivalentb A (concat E))
      && (forallb
            (fun c1 => forallb
                      (fun c2 => (equivalentb c1 c2)
                              ||(forallb (fun l => negb (inb l c2))c1))
                      E)
            E).

  Lemma partitionb_spec E A : partitionb E A = true <-> partition E A.
  Proof.
    unfold partitionb,partition.
    rewrite andb_true_iff,equivalentb_spec.
    rewrite forallb_forall;setoid_rewrite forallb_forall.
    setoid_rewrite orb_true_iff.
    setoid_rewrite equivalentb_spec.
    setoid_rewrite forallb_forall.
    setoid_rewrite negb_true_iff.
    setoid_rewrite inb_false.
    unfold equivalent at 1;setoid_rewrite in_concat.
    split.
    - intros (h1&h2);split.
      + intros m;rewrite h1;reflexivity.
      + intros l c1 c2 I1 I2 I3 I4.
        pose proof (h2 c1 I1 c2 I2) as [e|F].
        * assumption.
        * exfalso;apply (F l I3 I4).
    - intros (h1&h2);split.
      + intros m;rewrite h1;reflexivity.
      + intros c1 I1 c2 I2.
        case_eq (equivalentb c1 c2).
        * rewrite equivalentb_spec;tauto.
        * rewrite <- not_true_iff_false,equivalentb_spec.
          intros N;right;intros l I3 I4;apply N,(h2 l);tauto.
  Qed.

  (** A pair [l,E] of the orbit base type is an _orbit_ if:
      - [l] is duplication-free;
      - and [E] is a partition of the shuffles of [l].
   *)
  Definition is_orbit (o : orbit_base) :=
    NoDup (fst o) /\ partition (snd o) (shuffles (fst o)).

  (** This property is decidable. *)
  Definition is_orbitb (o : orbit_base) :=
    (NoDupb (fst o)) && partitionb (snd o) (shuffles (fst o)).

  Lemma is_orbitb_spec o : is_orbitb o = true <-> is_orbit o.
  Proof.
    destruct o as (l&p);unfold is_orbit,is_orbitb;simpl.
    rewrite andb_true_iff,NoDupb_NoDup,partitionb_spec.
    reflexivity.
  Qed.

  (** We can use set comprehension to define the type of orbits. Formally, [orbit] is a sigma-type, meaning its elements are pairs [o,P], where [o] has the orbit base type and [P] is a proof that [is_orbitb o=true]. Since we the latter is a boolean property, proof irrelevance holds, meaning that [(o,P)=(o',P')] if and only if [o=o']. *)
  Definition orbit : Set := { o : orbit_base | is_orbitb o = true }.

  Lemma orbit_eq (o1 o2 : orbit) : $ o1 = $ o2 <-> o1 = o2.
  Proof.
    destruct o1 as (o1&P1);destruct o2 as (o2&P2);simpl.
    split.
    - intro e.
      f_equal.
      apply eq_sig_hprop;simpl;auto.
      clear.
      intro x;destruct (is_orbitb x).
      + intros p q;apply UIP.
      + intro p;discriminate.
    - apply eq_sig_fst.
  Qed.

  (** If [o=((l,E),P)] is an orbit, we will call [l] the _index_ of [o], and [E] the [relation] associated with [o]. *)
  Notation index := (fun o : orbit =>fst ($ o)).
  Notation rel := (fun o : orbit => snd ($ o)).

  (** When [o] is an orbit, we may see its relation as binary relation between lists of atoms. [l1] and [l2] are said to be equivalent according to [o] if both [l1] and [l2] appear in some [c] in [o]'s relation. _Notice that despite it being called an equivalence, this relation is not actually reflexive, as lists that are not mentioned in [o]'s relation are not related to anybody, including themselves_. *)
  Definition eq_lists (o : orbit) : relation (list atom) :=
    fun l1 l2 => (exists c, c ∈ rel o /\ l1 ∈ c /\ l2 ∈ c).

  Notation " l1 ={ o }= l2" := (eq_lists o l1 l2) (at level 70).

  (** This relation is decidable. *)
  Definition eq_listsb (o : orbit) (l1 l2 : list atom) :=
    (existsb (fun c => inb l1 c && inb l2 c) (snd ($o))).

  Lemma eq_listsb_spec o l1 l2 : eq_listsb o l1 l2 = true <-> l1 ={o}= l2.
  Proof.
    unfold eq_listsb,eq_lists.
    destruct o as ((l&p)&P);simpl.
    rewrite existsb_exists.
    setoid_rewrite andb_true_iff.
    setoid_rewrite inb_spec;reflexivity.
  Qed.

  (** We finally define the equivalence of orbits by stating that [o1 ≃ o2] when:
      - the relations [={o1}=] and [={o2}=] coincide;
      - and the index of [o1] is related to the index of [o2] by the relation of [o1].
   *)
  Global Instance equiv_orbits : SemEquiv orbit :=
    fun o1 o2 => (forall l1 l2, l1 ={o1}= l2 <-> l1 ={o2}= l2) /\ index o1 ={o1}= index o2.

  (** ** Properties of orbits' relations *)

  (** Whenever [l1={o}=l2], [l1] must be a shuffle of the index of [o]. *)
  Lemma eq_lists_shuffle o l1 l2 : l1 ={o}= l2 -> l1 ∈ shuffles (index o).
  Proof.
    unfold eq_lists;intros (c&h1&h2&h3);simpl in *.
    destruct o as ((l&p)&P);simpl in *.
    apply is_orbitb_spec in P as (_&h&_);simpl in *.
    apply h;exists c;split;auto.
  Qed.
 
  (** The index of [o] is related to itself in [o]'s relation. *)
  Lemma eq_lists_fst o : index o ={o}= index o.
  Proof.
    destruct o as ((l&p)&P);simpl.
    unfold eq_lists;simpl.
    apply is_orbitb_spec in P as (ND&h1&h2).
    simpl in *.
    assert (I: l∈shuffles l) by (rewrite In_shuffles by assumption;split;[reflexivity|assumption]).
    apply h1 in I as (c&Ic&Il).
    exists c;split;auto.
  Qed.

  (** Furthermore, every shuffle of the index of [o] is related to itself in [o]'s relation. *)
  Lemma eq_lists_refl o l : l ∈ shuffles (index o) -> l ={o}= l.
  Proof.
    destruct o as ((l'&p)&P);unfold eq_lists;simpl in *.
    apply is_orbitb_spec in P as (ND&h1&h2);simpl in *.
    intros I;apply h1 in I as (c&Ic&Il).
    exists c;split;auto.
  Qed.

  (** The relation of [o] is transitive and symmetric. *)
  Global Instance eq_lists_trans o : Transitive (eq_lists o).
  Proof.
    destruct o as ((l&p)&P);simpl in *.
    unfold eq_lists;simpl.
    intros l1 l2 l3 (c&I&I1&I2) (c'&I'&I2'&I3). 
    apply is_orbitb_spec in P as (ND&P).
    exists c;repeat split;auto.
    destruct P as (p1&p2);apply (p2 l2 c c');simpl in *;assumption.
  Qed.

  Global Instance eq_lists_symmetric o : Symmetric (eq_lists o).
  Proof.
    destruct o as ((L,p),P);unfold eq_lists;simpl in *.
    intros l1 l2 (c&I&I1&I2);exists c;tauto.
  Qed.

  (** From these we can prove that the equivalence of orbits is indeed an equivalence relation. *)
  Global Instance equiv_orbits_Equivalence : Equivalence (@sequiv _ equiv_orbits).
  Proof.
    split;unfold sequiv,equiv_orbits.
    - intro o;split;[tauto|].
      apply eq_lists_fst.
    - intros o1 o2 (e1&e2);split.
      + intros l1 l2;rewrite e1;tauto.
      + apply e1;symmetry;apply e2.
    - intros o1 o2 o3 (e1&e2) (e3&e4);split.
      + intros l1 l2;rewrite e1,e3;reflexivity.
      + transitivity (fst ($o2)).
        * apply e2.
        * rewrite e1;apply e4.
  Qed.

  (** The equivalence of orbits is a decidable relation. *)
  Definition equiv_orbitsb (o1 o2 : orbit) :=
    (forallb (fun l1 => forallb (fun l2 => eq_listsb o1 l1 l2 =?= eq_listsb o2 l1 l2)
                             (shuffles (index o1)))
             (shuffles (index o1)))
      && eq_listsb o1 (index o1) (index o2).
  
  Lemma equiv_orbitsb_eq_shuffle o1 o2 :
    equiv_orbitsb o1 o2 = true -> shuffles (index o1) ≈ shuffles (index o2).
  Proof.
    unfold equiv_orbitsb.
    rewrite andb_true_iff,forallb_forall;
      setoid_rewrite forallb_forall;
      setoid_rewrite eqX_correct;
      setoid_rewrite eq_listsb_spec.
    intros (e0&e2).
    case_in (index o2) (shuffles (index o1)).
    - symmetry;apply eq_shuffles,I.
    - symmetry in e2;eapply eq_lists_shuffle in e2;tauto.
  Qed.
  
  Lemma equiv_orbitsb_spec o1 o2 : equiv_orbitsb o1 o2 = true <-> o1 ≃ o2.
  Proof.
    split.
    - intro e;pose proof e as e';apply equiv_orbitsb_eq_shuffle in e';revert e e'.
      unfold equiv_orbits,equiv_orbitsb.
      rewrite andb_true_iff,forallb_forall;
        setoid_rewrite forallb_forall;
        setoid_rewrite eqX_correct;
        setoid_rewrite eq_listsb_spec.
      intros (e1&e2) e;split;[|tauto].
      intros l1 l2.
      case_in l1 (shuffles (fst ($o1)));[case_in l2 (shuffles (fst ($o1)))|].
      + repeat rewrite <- eq_listsb_spec.
        apply eq_iff_eq_true,e1;tauto.
      + split;intro E'.
        * symmetry in E';apply eq_lists_shuffle in E';tauto.
        * symmetry in E';apply eq_lists_shuffle,e in E';tauto.
      + split;intro E'.
        * apply eq_lists_shuffle in E';tauto.
        * apply eq_lists_shuffle,e in E';tauto.
    - unfold equiv_orbits,equiv_orbitsb.
      repeat (rewrite andb_true_iff,forallb_forall;
              setoid_rewrite forallb_forall;
              setoid_rewrite eqX_correct;
              setoid_rewrite eq_listsb_spec).
      intros (e1&e2);(split;[|apply e2]).
      intros l1 I1 l2 I2;apply eq_iff_eq_true.
      repeat rewrite eq_listsb_spec.
      apply e1.
  Qed.

  (** ** Nominal setoid structure. *)
  (** If [E] is a partition of [A], then [π∙E] is a partition of [π∙A]. *)
  Lemma partition_act (π : perm) E A : partition E A -> partition (π∙E) (π∙A).
  Proof.
    unfold partition;setoid_rewrite In_act_lists.
    intros (h1&h2);split.
    - intro m;rewrite h1.
      split;intros (c&Ic&Im).
      + exists (π∙c);split.
        * rewrite act_pinv_p;assumption.
        * apply In_act_lists;assumption.
      + exists (π∗∙c);split.
        * assumption.
        * apply In_act_lists;rewrite act_pinv_p;assumption.
    - intros l c1 c2 I1 I2 I3 I4.
      cut (π∗∙c1 ≈π∗∙c2).
      + clear;intros E x;pose proof (E (π∗∙x)) as I.
        repeat rewrite In_act_lists,act_pinv_p in I.
        assumption.
      + apply (h2 (π∗∙l));try (apply In_act_lists;rewrite act_pinv_p);assumption.
  Qed.

  (** If [o] is an orbit, so is [π∙o]. *)
  Lemma is_orbit_act (π : perm) o : is_orbit o -> is_orbit (π∙o).
  Proof.
    destruct o as (l,p);unfold is_orbit;simpl.
    intros (ND&h);split.
    - apply NoDup_act,ND.
    - rewrite shuffles_act;apply partition_act,h.
  Qed.

  Lemma is_orbitb_act (π : perm) (o : orbit) : is_orbitb (π∙($o)) = true.
  Proof.
    apply is_orbitb_spec.
    destruct o as (o&P);simpl in *.
    apply is_orbit_act,is_orbitb_spec,P.
  Qed.

  (** This means that we may lift the action from the base type of orbits to the type of orbits. *)
  Global Instance ActOrb : ActionSetoid _ 𝐀 orbit :=
    (fun p o => exist _ (p∙ ($ o)) (is_orbitb_act p o)).

  (** We define the support of an orbit to be its index. *)
  Global Instance SuppOrbit : SupportSetoid _ 𝐀 orbit := fun o => index o.

  (** This structure satisfies the axioms of nominal setoids over [𝐀].*)
  Global Instance NomOrbit : NominalSetoid 𝐀 orbit.
  Proof.
    split.
    - apply equiv_orbits_Equivalence.
    - intros ((l1,p1),P1) ((l2,p2),P2) (E1&E2).
      unfold suppoid,SuppOrbit,eq_lists in *;simpl in *.
      apply is_orbitb_spec in P1 as (nd1&h1&_).
      apply is_orbitb_spec in P2 as (nd2&h2&_).
      simpl in *.
      destruct E2 as (c&Ic&I1&I2).
      apply shuffles_equiv,h1.
      exists c;split;auto.
    - intros π ((l1,p1),P1) ((l2,p2),P2) (E1&E2).
      unfold ActOrb,eq_lists,sequiv,equiv_orbits.
      unfold eq_lists in *;simpl in *.
      apply is_orbitb_spec in P1 as (nd1&h1&_).
      apply is_orbitb_spec in P2 as (nd2&h2&_).
      simpl in *.
      split.
      + intros m1 m2.
        split;(intros (c&I1&I2)).
        * assert (h:(exists c, c ∈ p1 /\ π∗∙m1 ∈ c /\ π∗∙m2 ∈ c)).
          -- exists (π∗∙c);split;auto.
             ++ rewrite <- In_act_lists;assumption.
             ++ repeat rewrite In_act_lists,act_pinv_p;tauto.
          -- apply E1 in h as (c'&Ic'&I1'&I2').
             rewrite <- In_act_lists in I1',I2'.
             rewrite <- (act_pinv_p π),In_act_lists,inverse_inv in Ic'.
             eauto.
        * assert (h:(exists c, c ∈ p2 /\ π∗∙m1 ∈ c /\ π∗∙m2 ∈ c)).
          -- exists (π∗∙c);split;auto.
             ++ rewrite <- In_act_lists;assumption.
             ++ repeat rewrite In_act_lists,act_pinv_p;tauto.
          -- apply E1 in h as (c'&Ic'&I1'&I2').
             rewrite <- In_act_lists in I1',I2'.
             rewrite <- (act_pinv_p π),In_act_lists,inverse_inv in Ic'.
             eauto.
      + destruct E2 as (c&Ic&I1&I2).
        exists (π∙c).
        repeat split;rewrite In_act_lists,act_pinv_p;assumption.
    - intros o π; pose proof (eq_lists_fst o) as E;revert E.
      destruct o as ((l,p),P);unfold suppoid,SuppOrbit,ActOrb,sequiv,equiv_orbits,eq_lists;simpl in *.
      apply is_orbitb_spec in P as (nd&h&_);simpl in *.
      intros E e.
      rewrite e;unfold act,act_lists in e;rewrite map_eq_id in e.
      assert (π∙p = p) as ->.
      + apply map_eq_id.
        intros c Ic;apply map_eq_id.
        intros l' Il';apply map_eq_id.
        intros a Ia;apply e.
        assert (el : exists c, c ∈ p /\ l' ∈ c) by (exists c;split;assumption).
        apply h,shuffles_equiv in el as ->;assumption.
      + tauto.
    - intros ((l,p),P) π;unfold suppoid,SuppOrbit,ActOrb,sequiv,equiv_orbits,eq_lists;simpl in *.
      reflexivity.
    - intros o π π';split.
      + unfold suppoid,SuppOrbit,ActOrb,sequiv,equiv_orbits,eq_lists;simpl in *.
        setoid_rewrite action_compose.
        clear;tauto.
      + pose proof (eq_lists_fst o) as (c&Ic&Il&_).
        destruct o as ((l,p),P);simpl.
        unfold actoid,ActOrb,eq_lists;simpl in *.
        setoid_rewrite <- action_compose.
        exists (π∙(π'∙c));repeat split;repeat rewrite In_act_lists|| rewrite act_pinv_p;tauto.
  Qed.      

End orbits.

Arguments orbit {atom} 𝐀.
Arguments orbit_base : clear implicits.

Notation index := (fun o : orbit _ =>fst ($ o)).

Notation rel := (fun o : orbit _ => snd ($ o)).

Notation " l1 ={ o }= l2" := (eq_lists o l1 l2) (at level 70).

(** * Lifting injections between sets of atoms as injective morphisms between sets of orbits. *)
Section eta.
  (** In this section, we fix two sets of atoms [A] and [B], and an injective function [f:A->B]. *)
  Context {A B : Set} {𝐀: Atom A} {𝐁 : Atom B}.
  Context {f : A -> B} {inj : injective f}.

  (** Given a permutation [π] over [A], we can define a permutation [⦅π⦆] over [B] by applying [f] to every atom appearing in [π]. *)
  Definition lift : @perm A _ -> @perm B _ := map (fun x => (f (fst x),f (snd x))).
  Notation " ⦅ p ⦆ " := (lift p).

  (** This lifting satisfies the following identity. *)
  Lemma lift_f π a : ⦅π⦆ ∙ (f a) = f (π ∙ a).
  Proof.
    revert a;induction π as [|(a,b) π];intros c;[reflexivity|simpl].
    repeat rewrite act_cons;simpl.
    destruct_eqX (π∙c) a.
    - rewrite <- E,IHπ;simpl_beq;tauto.
    - cut (⦅π⦆∙f c <> f a);[|intro E;apply N,inj;rewrite <- IHπ;assumption].
      intro N';simpl_beq.
      destruct_eqX (π∙c) b.
      + rewrite <- E,IHπ;simpl_beq;tauto.
      + cut (⦅π⦆∙f c <> f b);[|intro E;apply N0,inj;rewrite <- IHπ;assumption].
        intro N'';simpl_beq.
        apply IHπ.
  Qed.

  (** It preserves permutation equivalence. *)
  Global Instance lift_equiv : Proper (sequiv ==> sequiv) lift.
  Proof.
    intros π π' E x.
    case_in x (elements ⦅π⦆).
    - unfold elements,lift in I.
      rewrite flat_map_concat_map,map_map,<-flat_map_concat_map in I.
      apply in_flat_map in I as ((a,b)&I&[e|[e|F]]);simpl in *;tauto||subst.
      + repeat rewrite lift_f.
        rewrite E;reflexivity.
      + repeat rewrite lift_f.
        rewrite E;reflexivity.
    - case_in x (elements ⦅π'⦆).
      + unfold elements,lift in I0.
        rewrite flat_map_concat_map,map_map,<-flat_map_concat_map in I0.
        apply in_flat_map in I0 as ((a,b)&I0&[e|[e|F]]);simpl in *;tauto||subst.
        * repeat rewrite lift_f.
          rewrite E;reflexivity.
        * repeat rewrite lift_f.
          rewrite E;reflexivity.
      + repeat rewrite elements_inv_act_atom;reflexivity||assumption.
  Qed.

  (** Lifting commutes with taking the inverse of a permutation. *)
  Lemma lift_perm_inverse π : ⦅π⦆∗ = ⦅π∗⦆.
  Proof. unfold inverse,lift;rewrite map_rev;reflexivity. Qed.

  (** We can lift an orbit over [A] into an orbit over [B] by applying [f] pointwise. *)
  Definition inject_aux : orbit 𝐀 -> orbit_base B :=
    fun o => (map f (index o),map (map (map f)) (rel o)).

  (** This function indeed produces a valid orbit. *)
  Lemma inject_orbit (o : orbit 𝐀) : is_orbit (inject_aux o).
  Proof.
    destruct o as ((l,p),P);unfold inject_aux,is_orbit;simpl in *.
    apply is_orbitb_spec in P as (nd&h&d);simpl in *.
    split;[|split].
    - apply NoDup_map_injective;assumption.
    - intros m;rewrite shuffles_map,in_map_iff;setoid_rewrite h.
      clear;split.
      + intros (x&<-&c&Ic&Ix).
        exists (map (map f) c);split.
        * apply in_map_iff;exists c;tauto.
        * apply in_map_iff;exists x;tauto.
      + intros (c&Ic&Ix);apply in_map_iff in Ic as (c'&<-&Ic').
        apply in_map_iff in Ix as (m'&<-&Im).
        exists m';split;[reflexivity|].
        exists c';split;assumption.
    - setoid_rewrite in_map_iff.
      intros m' c1' c2' (c1&<-&I1) (c2&<-&I2) I3 I4.
      apply in_map_iff in I3 as (m&<-&I3).
      apply in_map_iff in I4 as (m'&E&I4).
      apply (map_injective_injective inj) in E as ->.
      rewrite (d m c1 c2 I1 I2 I3 I4).
      reflexivity.
  Qed.
  
  Lemma inject_orbitb (o : orbit 𝐀) : is_orbitb (inject_aux o) = true.
  Proof. apply is_orbitb_spec,inject_orbit. Qed.

  (** We encapsulate this in the following function between sigma-types. *)
  Definition inject : orbit 𝐀 -> orbit 𝐁 := fun o => exist _ (inject_aux o) (inject_orbitb o).

  (** This function is injective up-to equivalence. *)
  Lemma inject_injection o1 o2 : inject o1 ≃ inject o2 -> o1 ≃ o2.
  Proof.
    unfold inject,inject_aux,sequiv,equiv_orbits,eq_lists;destruct o1 as ((l1,E1),P1);
      destruct o2 as ((l2,E2),P2);simpl in *;apply is_orbitb_spec in P1 as (_&h1&_);
        apply is_orbitb_spec in P2 as (_&h2&_);simpl in *.
    intros (e1&e2);split.
    - intros m1 m2;split;intros I.
      + cut ((exists c, c ∈ map (map (map f)) E1 /\ map f m1 ∈ c /\ map f m2 ∈ c)).
        * rewrite e1;intros (c&Ic&Im1&Im2).
          apply in_map_iff in Ic as (c'&<-&Ic).
          apply in_map_iff in Im1 as (m1'&e&Im1).
          apply map_injective_injective in e as ->;[|assumption].
          apply in_map_iff in Im2 as (m2'&e&Im2).
          apply map_injective_injective in e as -> ;[|assumption].
          exists c';tauto.
        * destruct I as (c&Ic&Im1&Im2).
          exists (map (map f) c);split;[|split];apply in_map_iff.
          -- exists c;split;tauto.
          -- exists m1;split;tauto.
          -- exists m2;split;tauto.
      + cut ((exists c, c ∈ map (map (map f)) E2 /\ map f m1 ∈ c /\ map f m2 ∈ c)).
        * rewrite <- e1;intros (c&Ic&Im1&Im2).
          apply in_map_iff in Ic as (c'&<-&Ic).
          apply in_map_iff in Im1 as (m1'&e&Im1).
          apply map_injective_injective in e as ->;[|assumption].
          apply in_map_iff in Im2 as (m2'&e&Im2).
          apply map_injective_injective in e as -> ;[|assumption].
          exists c';tauto.
        * destruct I as (c&Ic&Im1&Im2).
          exists (map (map f) c);split;[|split];apply in_map_iff.
          -- exists c;split;tauto.
          -- exists m1;split;tauto.
          -- exists m2;split;tauto.
    - destruct e2 as (c&Ic&Im1&Im2).
      apply in_map_iff in Ic as (c'&<-&Ic).
      apply in_map_iff in Im1 as (m1'&e&Im1).
      apply map_injective_injective in e as ->;[|assumption].
      apply in_map_iff in Im2 as (m2'&e&Im2).
      apply map_injective_injective in e as -> ;[|assumption].
      exists c';tauto.
  Qed.

  (** The support of the image of [o] is the image of the support of [o] by [f]. *)
  Lemma inject_support o : ⌈inject o⌉ = (map f ⌈o⌉).
  Proof. reflexivity. Qed.

  (** [inject] is an equivariant function. *)
  Lemma inject_equivariant : forall π o, inject (π ⊙ o) ≃ ⦅π⦆ ⊙ (inject o).
  Proof.
    intros π o.
    pose proof (eq_lists_fst o) as e0;unfold eq_lists in e0.
    destruct o as ((l,E),P).
    unfold actoid,ActOrb,inject,inject_aux,sequiv,equiv_orbits,eq_lists;simpl in *.
    apply is_orbitb_spec in P as (_&h&_);simpl in *.
    split.
    - replace (⦅ π ⦆ ∙ map (map (map f)) E) with (map (map (map f)) (π ∙ E));[tauto|].
      unfold act,act_lists;repeat rewrite map_map.
      apply map_ext;intro l'.
      unfold act,act_lists;repeat rewrite map_map.
      apply map_ext;intro l''.
      unfold act,act_lists;repeat rewrite map_map.
      apply map_ext;intro a;symmetry;pose proof (lift_f π a) as e;apply e.
    - replace (⦅π⦆ ∙ map f l) with (map f (π∙l)).
      + destruct e0 as (c&Ic&Il&_).
        exists (map (map f) (π ∙ c));repeat split;apply in_map_iff.
        * exists (π∙c);split;auto.
          apply In_act_lists;rewrite act_pinv_p;apply Ic.
        * exists (π∙l);split;auto.
          apply In_act_lists;rewrite act_pinv_p;apply Il.
        * exists (π∙l);split;auto.
          apply In_act_lists;rewrite act_pinv_p;apply Il.
      + unfold act,act_lists;repeat rewrite map_map.
        apply map_ext;intro a;rewrite lift_f;reflexivity.
  Qed.

  (** It preserves equivalence. *)
  Lemma inject_equiv : Proper (sequiv ==> sequiv) inject.
  Proof.
    unfold inject,inject_aux,sequiv,equiv_orbits,eq_lists;intros ((l1,E1),P1) ((l2,E2),P2);simpl in *;
      apply is_orbitb_spec in P1 as (_&h1&_);apply is_orbitb_spec in P2 as (_&h2&_);simpl in *.
    intros (e1&e2);split.
    - intros m1 m2;split;
        (intros (c&Ic&I1&I2);
         apply in_map_iff in Ic as (c'&<-&Ic');
         apply in_map_iff in I1 as (m1'&<-&I1');
         apply in_map_iff in I2 as (m2'&<-&I2'));
        cut ((exists c, c ∈ E1 /\ m1' ∈ c /\ m2' ∈ c)).
      + rewrite e1;intros (c&Ic&I1&I2).
        exists (map (map f) c);split;[|split];apply in_map_iff.
        * exists c;tauto.
        * exists m1';tauto.
        * exists m2';tauto.
      + exists c';tauto.
      + intros (c&Ic&I1&I2).
        exists (map (map f) c);split;[|split];apply in_map_iff.
        * exists c;tauto.
        * exists m1';tauto.
        * exists m2';tauto.
      + rewrite e1;exists c';tauto.
    - destruct e2 as (c&Ic&I1&I2).
      exists (map (map f) c);split;[|split];apply in_map_iff.
      + exists c;tauto.
      + exists l1;tauto.
      + exists l2;tauto.
  Qed.
  
End eta.
Arguments lift {A B 𝐀 𝐁} f.
Arguments inject {A B 𝐀 𝐁} f {inj} o.

(** * Representation of a nominal set *)
Section orbitX.
  (** We fix a set of atoms [atom] and an alphabet [X], that is a decidable set nominal in [atom]. *)
  Context {atom X: Set}{𝐀 : Atom atom} {𝐗 : Alphabet 𝐀 X}.
  (** ** Hypothesis *)
  (** We assume to be given a function [⦃_⦄] from [X] to lists of atoms. We call it the _normalised support_. *)
  Parameter nf_supp : X -> list atom.
  Notation " ⦃ x ⦄ " := (nf_supp x).

  (** This function should satisfy the following properties: 
      - [⦃x⦄] is a shuffle of the list [{{⌊x⌋}}], meaning it contains exactly the elements of the support of [x] and it is duplication-free;
      - for every [x∈X] and every permutation [p], there exists a permutation [q] such that
        - [p] and [q] produce the same element when applied to [x], i.e. [p∙x=q∙x];
        - the normalised support of [p∙x] can be obtained by applying [q] to the normalised support of [x].
   *)
  Axiom nf_supp_shuffle_support : forall x : X, ⦃x⦄ ∈ shuffles {{⌊x⌋}}.
  Axiom coherent_support : forall (x : X) (p : perm), exists q, ⦃p∙x⦄ = q∙⦃x⦄ /\ p∙x = q∙x.

  Remark nf_supp_support : forall x : X, ⦃x⦄ ≈ ⌊x⌋.
  Proof.
    intros x.
    rewrite <- (undup_equivalent ⌊x⌋).
    symmetry;apply shuffles_equiv,nf_supp_shuffle_support.
  Qed.

  Remark nf_supp_nodup : forall x, NoDup ⦃x⦄.
  Proof.
    intro x;eapply shuffles_nodup;[|apply nf_supp_shuffle_support].
    apply NoDup_undup.
  Qed.
  
  Remark nf_supp_action x π : ⦃π∙x⦄ ≈ π ∙ ⦃x⦄.
  Proof.
    intros;rewrite nf_supp_support,support_action.
    intro a;repeat rewrite In_act_lists;rewrite nf_supp_support;reflexivity.
  Qed.
  
  (** The normalised support function enjoys a form of injectivity: the permutation [π] leaves [x] unchanged if and only if the normalised supports of [x] and [π∙x] coincide. *) 
  Proposition nf_supp_inj (x : X) π : ⦃x⦄ = ⦃π∙x⦄ <-> x = π ∙ x.
  Proof.
    split.
    - destruct (coherent_support x π) as (π'&->&->).
      intro e;symmetry;apply action_invariant.
      apply map_eq_id.
      setoid_rewrite <- nf_supp_support.
      apply map_eq_id.
      rewrite e at 2;reflexivity.
    - intros <- ;reflexivity.
  Qed.

  (** The proof of the following proposition relies on lemma [RIS.atoms.support_eq_action_eq], i.e. the fact that for any two permutations [π,π'] and any element [x], if [π∙a=π'∙a] for every [a] in the support of [x], then [π∙x=π'∙x]. *)
  Proposition act_make_perm (x : X) π : π ∙ x = (⦃x⦄ >> π∙⦃x⦄) ∙ x.
  Proof.
    apply support_eq_action_eq,map_bij;symmetry;repeat rewrite reform.
    apply (act_eq_equivalent _ _ (nf_supp_support x)).
    apply make_bij.
    - apply nf_supp_nodup.
    - apply NoDup_act,nf_supp_nodup.
    - solve_length.
  Qed.

  (** ** Group-theoretic orbits *)
  (** [x] and [y] are said to be _in the same orbit_ if there is a permutation sending [y] to [x]. *)
  Definition same_orbit (x y : X) := exists π, x = π ∙ y.

  (** The relation "being in the same orbit" is an equivalence. *)
  Global Instance same_orbit_Equivalence : Equivalence same_orbit.
  Proof.
    split;unfold same_orbit.
    - intro x;exists [];symmetry;apply act_nil.
    - intros x y (π&->);exists (π∗);symmetry;apply act_pinv_p.
    - intros x y z (π&->) (π'&->).
      exists (π++π');apply action_compose.
  Qed.

  (** If [x] and [y] are in the same orbit, then we may build a witnessing permutation by simply taking [⦃y⦄ >> ⦃x⦄]. The converse holds trivially. *)
  Corollary same_orbit_get_perm x y : same_orbit x y <-> x = (⦃y⦄ >> ⦃x⦄) ∙ y.
  Proof.
    split.
    - intros (π&->).
      destruct (coherent_support y π) as (π'&->&->).
      apply act_make_perm.
    - intros -> ;exists (⦃y⦄ >> ⦃x⦄);reflexivity.
  Qed.

  (** Using this last result, we can build the following boolean function to check whether two elements are in the same orbit. *)
  Definition same_orbitb (x y : X) := x =?= ((⦃y⦄ >> ⦃x⦄) ∙ y).

  Lemma same_orbitb_spec x y : same_orbitb x y = true <-> same_orbit x y.
  Proof. unfold same_orbitb;rewrite eqX_correct;symmetry;apply same_orbit_get_perm. Qed.
  
  (** ** Representation *)
  (** We can now map [X] into a set of orbits. First we define the function [orbitX_aux] sending elements of [X] to the base type of orbits. *)
  Definition orbitX_aux (x : X) : orbit_base atom :=
    (⦃x⦄,group_by_fst (map (fun l => ((⦃x⦄ >> l)∙x,l)) (shuffles ⦃x⦄))).

  (** We then proceed to show that for any [x] to the pair produced by [orbitX_aux x] is indeed an orbit. *)
  Lemma is_orbit_orbitX x : is_orbit (orbitX_aux x).
  Proof.
    unfold orbitX_aux;simpl.
    split;[|split];simpl.
    - apply nf_supp_nodup.
    - intros m.
      rewrite <- group_by_fst_map_supp;tauto.
    - intros l c1 c2 I1 I2 I3 I4.
      unfold group_by_fst in *.
      apply in_map_iff in I1 as (a&e1&I1).
      rewrite In_undup in I1.
      apply in_map_iff in I1 as ((y&l1)&<-&I1).
      simpl in *.
      apply in_map_iff in I1 as (m1&E1&I1).
      inversion E1;subst;clear E1.
      apply in_map_iff in I3 as ((a&m1)&<-&I3);simpl_In in I3.
      rewrite eqX_correct in I3;simpl in I3.
      destruct I3 as (I3&->).
      apply in_map_iff in I3 as (m1'&e1&I3);inversion e1 as [[E1 E2]];subst;clear e1;simpl in *.
      apply in_map_iff in I2 as (a&e2&I2).
      rewrite In_undup in I2.
      apply in_map_iff in I2 as ((y&l2)&<-&I2).
      simpl in *.
      apply in_map_iff in I2 as (m2&E2&I2).
      inversion E2;subst;clear E2.
      apply in_map_iff in I4 as ((a&m2)&<-&I4);simpl_In in I4.
      rewrite eqX_correct in I4;simpl in I4.
      destruct I4 as (I4&->).
      apply in_map_iff in I4 as (m2'&e2&I4);inversion e2 as [[E2 E3]];subst;clear e2;simpl in *.
      reflexivity.
  Qed.

  Corollary is_orbitb_orbitX x : is_orbitb (orbitX_aux x) = true.
  Proof. apply is_orbitb_spec,is_orbit_orbitX. Qed.

  (** Finally, we use these to build a valid orbit from any [x]. *)
  Definition orbitX x : orbit 𝐀 := exist _ (orbitX_aux x) (is_orbitb_orbitX x).

  (** This function satisfies the same kind of injectivity as normalised supports. *)
  Lemma orbitX_inj x π : orbitX x ≃ orbitX (π∙x) -> x = π∙x.
  Proof.
    unfold orbitX,orbitX_aux,sequiv,equiv_orbits;simpl.
    intros (E&h).
    pose proof h as h';rewrite E in h'.
    revert E h h';unfold eq_lists.
    setoid_rewrite group_by_fst_map_In.
    intros E (h1&h2&h3).
    intros (_&_&h3').
    rewrite make_perm_id,act_nil in h3',h3.
    rewrite <- h3';apply same_orbit_get_perm;exists (π∗);rewrite act_pinv_p;reflexivity.
  Qed.

  (** The following observation will be useful later on: two lists [l1] and [l2] are equivalent according to [orbitX x] if and only if there are two permutations [p1] and [p2] such that:
      - [p1] sends elements of the support of [x] to elements of the support of [x];
      - the actions of [p1] and [p2] on [x] coincide;
      - [l1] is [p1∙⦃x⦄] and [l2] is [p2∙⦃x⦄]. 
   *)
  Remark eq_lists_orbitX x l1 l2 :
    l1 ={orbitX x}= l2 <-> (exists p1 p2 : perm, p1 ∙ ⦃x⦄ ≈ ⦃x⦄ /\ p1 ∙ x = p2∙x
                                          /\ p1 ∙ ⦃x⦄ = l1 /\ p2 ∙ ⦃x⦄ = l2).
  Proof.
    unfold orbitX,orbitX_aux,eq_lists;simpl.
    setoid_rewrite group_by_fst_map_In;split;intros h.
    - destruct h as (h1&h2&h3);exists (⦃x⦄ >> l1),(⦃x⦄ >> l2);
        split;[|split;[|split]];auto.
      + etransitivity;[symmetry;apply map_equivalent_Proper;reflexivity|rewrite reform].
        replace ((_ >> _)∙ _) with l1;[symmetry;apply shuffles_equiv,h1|].
        symmetry;apply make_bij.
        * apply nf_supp_nodup.
        * eapply shuffles_nodup;[|apply h1];apply nf_supp_nodup.
        * apply shuffles_length,h1.
      + apply make_bij.
        * apply nf_supp_nodup.
        * eapply shuffles_nodup;[|apply h1];apply nf_supp_nodup.
        * apply shuffles_length,h1.
      + apply make_bij.
        * apply nf_supp_nodup.
        * eapply shuffles_nodup;[|apply h2];apply nf_supp_nodup.
        * apply shuffles_length,h2.
    - destruct h as (p1&p2&e1&e2&e3&e4);repeat split.
      + apply In_shuffles;[apply nf_supp_nodup|].
        split.
        * rewrite <-e1,<-e3;reflexivity.
        * rewrite <- e3;apply NoDup_act,nf_supp_nodup.
      + apply In_shuffles;[apply nf_supp_nodup|].
        split.
        * rewrite <-e1,<-nf_supp_action,e2,nf_supp_action,<-e4;reflexivity.
        * rewrite <- e4;apply NoDup_act,nf_supp_nodup.
      + etransitivity;[|etransitivity;[apply e2|symmetry]];
          apply support_eq_action_eq;apply map_bij;setoid_rewrite reform.
        * apply (act_eq_equivalent _ _ (nf_supp_support x)).
          rewrite e3;apply make_bij.
          -- apply nf_supp_nodup.
          -- rewrite <- e3;apply NoDup_act,nf_supp_nodup.
          -- rewrite <- e3;solve_length.
        * apply (act_eq_equivalent _ _ (nf_supp_support x)).
          rewrite e4;apply make_bij.
          -- apply nf_supp_nodup.
          -- rewrite <- e4;apply NoDup_act,nf_supp_nodup.
          -- rewrite <- e4;solve_length.
  Qed.

  (** [orbitX] is an equivariant function. *)
  Lemma orbitX_perm π x : orbitX (π∙x) ≃ π ⊙ orbitX x.
  Proof.
    destruct (coherent_support x π) as (π'&E1&E2);split.
    - setoid_rewrite eq_lists_orbitX.
      unfold orbitX,orbitX_aux,sequiv,equiv_orbits,eq_lists;simpl.
      rewrite group_by_fst_act.
      replace (group_by_fst _)
        with (group_by_fst (map (fun l => ((⦃x⦄>>l)∙x,l)) (shuffles (π ∙ ⦃x⦄)))).
      + setoid_rewrite group_by_fst_map_In.
        intros l1 l2;split.
        * intros (π1&π2&e1&e2&<-&<-);repeat split.
          -- rewrite shuffles_act,In_act_lists,In_shuffles;[split|].
             ++ rewrite e1,(nf_supp_action x π),act_pinv_p;reflexivity.
             ++ repeat apply NoDup_act;apply nf_supp_nodup.
             ++ apply nf_supp_nodup.
          -- rewrite shuffles_act,In_act_lists,In_shuffles;[split|].
             ++ rewrite <- (act_pinv_p π) at 1.
                apply equivalent_act;[reflexivity|].
                rewrite <- nf_supp_action,<-e1 at 1;repeat rewrite <- nf_supp_action.
                rewrite e2;reflexivity.
             ++ repeat apply NoDup_act;apply nf_supp_nodup.
             ++ apply nf_supp_nodup.
          -- rewrite E1,action_compose,action_compose,<-act_make_perm,<-act_make_perm.
             rewrite <-action_compose,<-action_compose,<-E2.
             exact e2.
        * intros (I1&I2&e).
          exists ((⦃x⦄ >> l1)++π'∗),((⦃x⦄ >> l2)++π'∗).
          repeat rewrite <- action_compose||rewrite E1||rewrite E2||rewrite act_pinv_p.
          repeat rewrite make_bij.
          -- split;[|split;[|split]];try assumption||reflexivity.
             rewrite <- E1,nf_supp_action. 
             symmetry;apply shuffles_equiv,I1.
          -- apply nf_supp_nodup.
          -- eapply shuffles_nodup,I2;apply NoDup_act,nf_supp_nodup.
          -- transitivity ⎢π∙⦃x⦄⎥;[solve_length|].
             apply shuffles_length,I2.
          -- apply nf_supp_nodup.
          -- eapply shuffles_nodup,I1;apply NoDup_act,nf_supp_nodup.
          -- transitivity ⎢π∙⦃x⦄⎥;[solve_length|].
             apply shuffles_length,I1.
      + clear E1 E2;f_equal;rewrite shuffles_act;unfold act at 2 3,act_lists.
        repeat rewrite map_map;apply map_ext_in.
        intros l Il;unfold act at 6,act_pair;simpl.
        f_equal;rewrite action_compose;apply support_eq_action_eq.
        setoid_rewrite <- nf_supp_support;apply map_bij.
        repeat rewrite reform||rewrite <- action_compose.
        repeat rewrite make_bij.
        * reflexivity.
        * apply nf_supp_nodup.
        * eapply (shuffles_nodup (nf_supp_nodup _) Il).
        * apply shuffles_length,Il.
        * apply nf_supp_nodup.
        * apply NoDup_map_injective;[apply injective_perm|].
          eapply (shuffles_nodup (nf_supp_nodup _) Il).
        * unfold act;rewrite (shuffles_length Il);solve_length.
    - rewrite eq_lists_orbitX.
      unfold orbitX,orbitX_aux;simpl.
      exists [],(π++π'∗).
      repeat rewrite act_nil||rewrite <- action_compose.
      split;[|split;[|split]].
      + reflexivity.
      + rewrite E2 at 2;rewrite act_pinv_p;reflexivity.
      + reflexivity.
      + rewrite E1,act_pinv_p;reflexivity.
  Qed.

End orbitX.
(** * Pointers *)
Section pointers.
  (** We fix a set of atoms [atom]. *)
  Context {atom: Set}{𝐀 : Atom atom}.

  (** A pointer over [atom] is either a free name [a!] or a natural number [n?]. *)
  Inductive pointer := free : atom -> pointer | bound : nat -> pointer.
  Notation " a ! " := (free a)(at level 20).
  Notation " a ? " := (bound a)(at level 20).

  (** Pointers can be treated as atoms. *)
  Global Instance 𝐏 : Atom pointer.
  Proof.
    split.
    - set (eq_pointer := fun p1 p2 =>
                           match (p1,p2) with
                           | (a!,b!) => a=?=b
                           | (a?,b?) => a=?=b
                           | _ => false
                           end).
      assert (eq_pointer_eq : forall x y, reflect (x=y) (eq_pointer x y)).
      + intros;apply iff_reflect;destruct x;destruct y;unfold eq_pointer;try rewrite eqX_correct;split;
          try discriminate;intro E;inversion E;auto.
      + exact (Build_decidable_set eq_pointer_eq).
    - intros l.
      set (f:= fun p => match p with a! => [a] | _? => [] end).
      destruct (exists_fresh (flat_map f l)) as (a&Ia).
      exists (a!);intro Ia'.
      apply Ia,in_flat_map.
      exists (a!);split;[tauto|].
      unfold f;simpl;tauto.
  Qed.

  (** As any constructor, the function [free] is injective. *)
  Global Instance injective_free : injective free.
  Proof. split;intros x y e;inversion e;reflexivity. Qed.

  (** The set of pointers is nominal in [atom]. *)
  Global Instance act_pointer : Action 𝐀 pointer :=
    fun p b => match b with a! => (p∙a)! | _ => b end.
  Global Instance support_pointer : Support 𝐀 pointer :=
    fun b => match b with a! => ⌊a⌋ | _ => [] end.

  Global Instance groupAct_pointer : Nominal 𝐀 pointer.
  Proof.
    split;intro;intros.
    - destruct x;auto.
      unfold support,support_pointer in H;unfold act,act_pointer;f_equal;f_equal.
      apply action_invariant,H.
    - destruct x;unfold support,support_pointer;simpl;auto.
      + apply support_action.
      + reflexivity.
    - destruct x;simpl;auto.
      unfold act,act_pointer;f_equal.
      apply action_compose.
  Qed.

  Notation " ⦅ π ⦆ " := (lift free π).
  
  (** Notice that applying a lifted permutation [⦅p⦆] to a free name is the same as applying [p] to that name, and applying it to a bound number leaves it unchanged. *)
  Remark act_free (π : @perm _ 𝐀) (a : atom) :  ⦅π⦆ ∙ (a!) = (π ∙ a)!.
  Proof.
    induction π as [|(b,c)π];simpl.
    - reflexivity.
    - repeat rewrite act_cons.
      rewrite IHπ;simpl_eqX;unfold_eqX;try reflexivity||tauto.
      + inversion E;subst;tauto.
      + inversion E;subst;tauto.
  Qed.

  Remark act_bound π n : ⦅π⦆ ∙ (n?) = n?.
  Proof.
    induction π as [|(a,b)π];[reflexivity|];simpl.
    unfold act in *;simpl;rewrite IHπ;simpl_eqX;reflexivity.
  Qed.

  (** Furthermore, the action of [⦅π⦆] on any pointer [p] coincide with the action of [π] on [p]. The first action comes from the nominal structure [RIS.atoms.Nominal_Atom pointer], while the second is an instance of [groupAct_pointer]. *)
  Remark lift_perm_invisible π (p : pointer) :  ⦅π⦆ ∙ p = π ∙ p.
  Proof.
    destruct p as [a|n].
    - rewrite act_free;reflexivity.
    - rewrite act_bound;reflexivity.
  Qed.

End pointers.

(** * The function [η] *)
Section s.
  (** We again fix a set of atoms and an alphabet. *)
  Context {atom X: Set}{𝐀 : Atom atom} {𝐗 : Alphabet 𝐀 X}.
  Notation " a ! " := (free a)(at level 20).
  Notation " a ? " := (@bound atom a)(at level 20).
  Notation " ⦅ p ⦆ " := (lift free p).
  
  (** We now proceed to map elements from [X] to elements of a nominal setoid over [pointer], namely the set [Repr] built out of pairs of an element from [X], considered up-to [same_orbit], and an orbit over [pointer], considered up-to [≃]. *)
  Definition Repr : Set :=  X * (orbit 𝐏).

  Global Instance eqRepr : SemEquiv Repr :=
    fun r1 r2 => (same_orbit (fst r1) (fst r2)) /\ snd r1 ≃ snd r2.

  (** The equivalence of representatives is decidable. *)
  Definition eqReprb : Repr -> Repr -> bool :=
    fun r1 r2 => same_orbitb (fst r1) (fst r2) && equiv_orbitsb (snd r1) (snd r2).

  Lemma eqReprb_spec : forall x y, reflect (x ≃ y) (eqReprb x y).
  Proof.
    intros r1 r2;apply iff_reflect.
    unfold eqReprb,sequiv,eqRepr.
    rewrite andb_true_iff,same_orbitb_spec,equiv_orbitsb_spec;reflexivity.
  Qed.

  (** [Repr] is a nominal setoid over [pointer]. *)
  Global Instance ActRepr : ActionSetoid _ 𝐏 Repr :=
    fun π r => (fst r,π⊙snd r).

  Global Instance SuppRepr : SupportSetoid _ 𝐏 Repr :=
    fun r => ⌈snd r⌉.

  Global Instance NomSetRepr : NominalSetoid 𝐏 Repr.
  Proof.
    split.
    - unfold sequiv,eqRepr;split.
      + intro r;split;reflexivity.
      + intros r1 r2 (e1&e2);split;symmetry;assumption.
      + intros r1 r2 r3 (e1&e2) (e3&e4);split;etransitivity;eauto.
    - unfold sequiv,eqRepr,suppoid,SuppRepr;intros (?&o1) (?&o2) (?&e);simpl in *;
        rewrite e;reflexivity.
    - unfold sequiv,eqRepr,actoid,ActRepr;intros π (x1&o1) (x2&o2) (ex&eo);simpl in *.
      split;[assumption|].
      apply eq_act_proper;assumption.
    - unfold sequiv,eqRepr,suppoid,SuppRepr,actoid,ActRepr;intros (x&o) π;simpl.
      intro h;split;[reflexivity|].
      apply action_invariant_eq,h.
    - unfold suppoid,SuppRepr,actoid,ActRepr;intros (x&o) π;simpl.
      apply support_action_eq.
    - unfold sequiv,eqRepr,actoid,ActRepr;intros (x&o) π π';simpl.
      split;[reflexivity|].
      apply action_compose_eq.
  Qed.

  (** The function [η] maps [x] to the pair [x,inject free (orbitX x)]. *)
  Definition η : X -> Repr := fun x => (x,inject free (orbitX x)).

  (** It is injective up-to [≃]. *)
  Lemma η_inj : forall x y, η x ≃ η y -> x = y.
  Proof.
    intros x y;unfold η,sequiv,eqRepr;simpl.
    intros ((π&->)&e).
    symmetry;apply orbitX_inj;symmetry.
    apply (inject_injection e).
  Qed.

  (** [η] is equivariant. *)
  Lemma η_equivariant : forall p x, η (p∙x) ≃ ⦅p⦆⊙(η x).
  Proof.
    intros π x;unfold η,sequiv,eqRepr,actoid,ActOrb;simpl;split.
    - exists π;reflexivity.
    - rewrite <- inject_equivariant.
      apply inject_equiv, orbitX_perm.
  Qed.

  (** The support of [η x] is the set of [a!] such that [a] is in the support of [x]. *)
  Lemma η_support : forall x, ⌈η x⌉ ≈ (map free ⌊x⌋).
  Proof.
    intros x;unfold η,inject,inject_aux,orbitX.
    unfold suppoid,SuppRepr,suppoid,SuppOrbit;simpl.
    rewrite nf_supp_support.
    reflexivity.
  Qed.

End s.

Notation " ⦅ p ⦆ " := (lift free p).
Notation " a ! " := (free a)(at level 20).
