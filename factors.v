(** * RIS.factors : square bindings and binding division. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools words.

(** * Enumerate bindings *)
(** [Bindupto N] returns a list containing every element of [𝖡] of
size not exceeding [N]. *)
Fixpoint Bindupto n : list 𝖡 :=
  match n with
  | 0 => [ε;(0,true,0)]
  | S n =>
    flat_map (fun b : 𝖡 =>
                b::(S (fst (fst b)),snd(fst b),snd b)
                 ::[(fst (fst b),snd(fst b),S (snd b))]
             )
             (Bindupto n)
  end.
Lemma Bindupto_spec n b : size b <= n <-> b ∈ Bindupto n.
Proof.
  revert b;induction n;intro b;simpl.
  - destruct b as (([],m),p);unfold size;simpl.
    + split.
      * intro h;replace p with 0 by lia;destruct m;tauto.
      * intros [e|[e|F]];tauto||inversion e;subst;reflexivity.
    + firstorder (discriminate || lia).
  - rewrite in_flat_map;setoid_rewrite <- IHn.
    destruct b as ((d,f),c);unfold size,d_binding;simpl.
    split.
    + destruct d;[destruct c|];intro I.
      * exists (0,f,0);simpl;split;[lia|tauto].
      * exists (0,f,c);simpl;split;[lia|tauto].
      * exists (d,f,c);simpl;split;[lia|tauto].
    + intros (((d'&f')&c')&L&I);simpl in *.
      repeat (destruct I as [E|I];[inversion E;clear E;subst;lia|]).
      tauto.
Qed.

(** * Factors *)
(* begin hide *)
Definition Factors (b : 𝖡) N : list (𝖡 * 𝖡) :=
  (fun p => (fst p ⋅ snd p) =?= b)
    :> pairs (Bindupto N) (Bindupto N).

Lemma Factors_spec b N α β :
  (α,β) ∈ Factors b N <-> (α⋅β = b /\ size α <= N /\ size β <= N).
Proof.
  unfold Factors;simpl_In;simpl.
  rewrite pairs_spec,eqX_correct;repeat rewrite Bindupto_spec.
  tauto.
Qed.
(* end hide *)
(** [factors b N] is a list containing pairs of bindings [(α,β)] such
that [α⋅β=b]. This list is not exhaustive, as there are in general an
infinite number of such pairs. The parameter [N] is used as a bound,
to collect only a finite number of pairs. The following lemmas will
outline the properties of this function. *)

Definition factors (b : 𝖡) N : list (𝖡 * 𝖡) :=
  (fun p => (fst p ⋅ snd p) =?= b)
    :> pairs
    (pairs (pairs (seq 0 (S N)) [true;false]) (seq 0 (S N)))
    (pairs (pairs (seq 0 (size b + S N)) [true;false]) (seq 0 (size b + S N))).

(** Every pair [(a1,a2)] in [factors b N] satisfies [a1⋅a2=b]. *)
Lemma factors_prod b N a1 a2 : (a1,a2) ∈ factors b N -> a1 ⋅ a2 = b.
Proof. unfold factors;simpl_In;rewrite eqX_correct;simpl;tauto. Qed.

(** If the size of [a1] is below [N] and if the product [a1⋅a2] equals
[b], then [(a1,a2)] belongs to [factors b N]. *)
Lemma factors_In b N a1 a2 : size a1 <= N -> a1 ⋅ a2 = b -> (a1,a2) ∈ factors b N.
Proof.
  intros h E.
  unfold factors;simpl_In;rewrite eqX_correct;split;[|assumption].
  assert (h3 : size a2 <= size b + N)
    by (pose proof (size_prod_bound_inf_right a1 a2) as h3;rewrite E in h3;lia).
  revert h3;generalize (size b);clear E b;intros k h'.
  destruct a1 as ((n1,m1),p1), a2 as ((n2,m2),p2);repeat rewrite pairs_spec.
  rewrite (pairs_spec _ _ (n1,m1) p1),pairs_spec.
  rewrite (pairs_spec _ _ (n2,m2) p2),pairs_spec.
  repeat rewrite in_seq;unfold size,d_binding in *;simpl in *.
  repeat split;try lia.
  - clear;destruct m1;simpl;tauto.
  - clear;destruct m2;simpl;tauto.
Qed.

(** For any pair [(a1,a2)] in [factors b N], the size of [a1] does not
exceed [2*N]. *)
Lemma factors_size a1 a2 b N : (a1,a2) ∈ factors b N -> size a1 <= 2*N.
Proof.
  destruct a1 as ((?&?)&?);unfold factors;simpl_In.
  rewrite pairs_spec;intros ((I&_)&_).
  apply pairs_spec in I as (I1&I2).
  apply pairs_spec in I1 as (I1&_).
  rewrite in_seq in *;unfold size,d_binding;simpl.
  lia.
Qed.

(** * Division when one projection is 0*)
(** [factors (N,t,0) k] contains only pairs of the shape
[((D,F,C),(N',t',0))] such that [C<=N']. *)
Lemma factors_open_balanced β1 β2 N t k :
  (β1,β2) ∈ factors (N,t,0) k ->
  exists N' t', β2 = (N',t',0) /\ c_binding β1 <= N'.
Proof.
  intros If;apply factors_prod in If;revert If;unfold prod_binding.
  destruct β2 as ((N',t'),C),β1 as ((x,y),z);simpl.
  destruct_ltb z N';[destruct_ltb N' z;[replace z with N' in * by lia|]|];
    intro heq;inversion heq;simpl_nat;subst.
  - exists N',t';tauto.
  - exists N',t';split;[f_equal|];lia.
  - exists N',t;split;[reflexivity|lia].
Qed.

(** [divide_by_open β] yields a list containing every [α] such that
[(0,false,1)⋅β=(0,false,1)⋅α]. *)
Definition divide_by_open β :=
  match β with
  | (0,false,n) | (0,true,n)| (1,false,S n) => [(0,false,n);(0,true,n);(1,false,S n)]
  | _ => [β]
  end.

Lemma divide_by_open_spec β1 β2 : (0,false,1) ⋅ β1 = (0,false,1) ⋅ β2 <-> β1 ∈ divide_by_open β2.
Proof.
  destruct β1 as ((x1,y1),z1),β2 as ((x2,y2),z2);unfold divide_by_open,prod_binding;simpl;simpl_eqX;
    destruct x2 as [|[]];simpl;simpl.
  - destruct y2;simpl.
    + destruct x1 as [|[]];simpl;simpl_nat;intuition.
      * inversion H.
        replace z1 with z2 by lia.
        destruct y1;tauto.
      * inversion H0;subst;reflexivity.
      * inversion H;subst;reflexivity.
      * discriminate.
      * inversion H;subst.
        right;right;left.
        f_equal;lia.
      * discriminate.
      * discriminate.
      * inversion H0;subst.
        f_equal;lia.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
    + destruct x1 as [|[]];simpl;simpl_nat;intuition.
      * inversion H.
        replace z1 with z2 by lia.
        destruct y1;tauto.
      * inversion H0;subst;reflexivity.
      * inversion H;subst;reflexivity.
      * discriminate.
      * inversion H;subst.
        right;right;left.
        f_equal;lia.
      * discriminate.
      * discriminate.
      * inversion H0;subst.
        f_equal;lia.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
  - destruct x1 as [|[]];simpl;destruct y2;simpl;intuition.
    + discriminate.
    + discriminate.
    + inversion H;subst.
      case_eq (z1+1-0);[lia|intros ? h].
      replace n with z1 by lia.
      destruct y1;simpl;tauto.
    + destruct z2;simpl in H;intuition.
      * discriminate.
      * inversion H0;f_equal;lia.
      * inversion H;subst;f_equal;lia.
      * discriminate.
    + inversion H;subst;tauto.
    + inversion H0;subst;reflexivity.
    + inversion H;subst.
      destruct z2;simpl;tauto.
    + destruct z2;simpl in H;intuition.
      * inversion H0;subst;reflexivity.
      * discriminate.
      * discriminate.
      * inversion H0;subst;reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct z2;simpl in H;intuition discriminate.
  - destruct x1 as [|[]];simpl;intuition try discriminate.
    + inversion H;subst;tauto.
    + inversion H0;subst;tauto.
Qed.

(** * Square bindings *)
(** A binding [α:𝖡] is called [square] when its creation and destruction projections are equal. *) 
Definition square α := c_binding α = d_binding α.
(** This property can be checked using the [is_square] boolean predicate. *)
Definition is_square β := c_binding β =?= d_binding β.

(** We define the following binary operation on bindings. *)
Definition maxBind (α β : 𝖡) : 𝖡 :=
  if Nat.ltb (d_binding α) (d_binding β) then β
  else if Nat.ltb (d_binding β) (d_binding α) then α
       else (d_binding α,snd(fst α)||snd(fst β),max (c_binding α) (c_binding β)).
Infix " ⊓ " := maxBind (at level 45).

(** On square bindings, this operation coincides with multiplication. *)
Lemma prod_binding_maxBind a b : square a -> square b -> a ⊓ b = a ⋅ b.
Proof.
  unfold square,maxBind,d_binding,prod_binding;destruct a as ((a1&a2)&a3),b as ((b1&b2)&b3);simpl.
  intros -> -> .
  destruct_ltb a1 b1;[destruct_ltb b1 a1|];f_equal;f_equal;try lia.
Qed.

(** The structure [(𝖡,⊓,ε)] forms a commutative idempotent monoid. *)
Lemma maxBind_neutral a : a ⊓ ε = a.
Proof.
  unfold maxBind,d_binding;destruct a as ((a1&a2)&a3);simpl.
  rewrite orb_false_r.
  rewrite PeanoNat.Nat.max_0_r.
  destruct a1;reflexivity.
Qed.
Lemma maxBind_assoc a b c : a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c.
Proof.
  unfold maxBind,d_binding.
  destruct a as ((a1&a2)&a3),b as ((b1&b2)&b3),c as ((c1&c2)&c3);simpl.
  destruct_ltb a1 b1;[destruct_ltb b1 a1;[replace a1 with b1 in * by lia|]|];
    (destruct_ltb b1 c1;[destruct_ltb c1 b1;[replace c1 with b1 in * by lia|]|]);simpl;
      repeat rewrite PeanoNat.Nat.ltb_irrefl;
      repeat match goal with
             | [ h : ?a < ?b |- _ ] => pose proof h as tmp;apply PeanoNat.Nat.ltb_lt in tmp as ->
             | [ h : ?a <= ?b |- _ ] => pose proof h as tmp;apply PeanoNat.Nat.ltb_ge in tmp as ->
             end;try reflexivity.
  - f_equal;[f_equal|lia].
    auto with bool.
  - destruct_ltb a1 c1;[|lia].
    destruct_ltb c1 a1;[lia|reflexivity].
  - destruct_ltb a1 c1;[lia|reflexivity].
Qed.
Lemma maxBind_comm a b : a ⊓ b = b ⊓ a.
Proof.
  unfold square,maxBind,d_binding,prod_binding;destruct a as ((a1&a2)&a3),b as ((b1&b2)&b3);simpl.
  destruct_ltb a1 b1;destruct_ltb b1 a1;(f_equal;[f_equal|])||f_equal;try lia.
  auto with bool.
Qed.
Lemma maxBind_idem a : a ⊓ a = a.
Proof.
  unfold square,maxBind,d_binding,prod_binding;destruct a as ((a1&a2)&a3);simpl.
  rewrite PeanoNat.Nat.ltb_irrefl;f_equal;f_equal.
  - destruct a2;reflexivity.
  - lia.
Qed.

(** If [a] and [b] are square, [a ⊓ b] is either [a] or [b]. *)
Lemma maxBind_square_disj a b : 
  square a -> square b -> a ⊓ b = a \/ a ⊓ b = b.
Proof.
  unfold square,maxBind,d_binding,prod_binding;
    destruct a as ((a1&a2)&a3),b as ((b1&b2)&b3);simpl.
  intros -> -> .
  destruct_ltb a1 b1;[destruct_ltb b1 a1|];simpl.
  - replace b1 with a1 by lia.
    rewrite PeanoNat.Nat.max_id.
    destruct a2,b2;simpl;tauto.
  - tauto.
  - tauto.
Qed.
(** Hence, [⊓] maps pairs of square bindings to square bindings. *)
Lemma maxBind_square a b :
  square a -> square b -> square (a ⊓ b).
Proof.
  intros h1 h2;destruct (maxBind_square_disj h1 h2) as [-> | ->];assumption.
Qed.

(** Since [⊓] is commutative, associative and idempotent, applying on
equivalent lists yields the same result. *)
Lemma maxBind_lists A B : A ≈ B -> fold_right maxBind ε A = fold_right maxBind ε B.
Proof.
  revert B;induction A as [|a A];intros B.
  - destruct B as [|b B];[reflexivity|].
    intro h;exfalso.
    assert (I:b∈[]) by (apply h;now left).
    apply I.
  - intros h;case_in a A;simpl.
    + assert (e: A ≈ B) by (intro x;rewrite <- h;simpl;split;[tauto|intros [<-|Ix];tauto]).
      assert (e': A ≈ a::A) by (intro x;simpl;split;[tauto|intros [<-|Ix];tauto]).
      rewrite <- (IHA _ e).
      rewrite (IHA _ e') at 2.
      reflexivity.
    + rewrite (IHA (B∖a))
        by (intro x;rewrite rm_In,<-h;simpl;split;destruct_eqX a x;tauto).
      assert (Ia : a ∈ B) by (apply h;now left).
      clear A h IHA I.
      induction B as [|b B].
      * exfalso;apply Ia.
      * simpl;unfold_eqX;subst;simpl.
        -- case_in b B.
           ++ rewrite <- IHB by assumption.
              rewrite maxBind_assoc,maxBind_idem.
              reflexivity.
           ++ rewrite (rm_notin I);reflexivity.
        -- destruct Ia as [<-|Ia];[tauto|].
           rewrite <- IHB by assumption.
           repeat rewrite maxBind_assoc.
           rewrite (maxBind_comm a b);reflexivity.
Qed.

(** * Square factors of square bindings *)
(** [lower_squares], when applied to a square binding [β], produces the list of square bindings [α] such that [α⋅β=β]. *)
Definition lower_squares (β : 𝖡) : list 𝖡 :=
  if (snd(fst β))
  then flat_map (fun m => [(m,true,m);(m,false,m)]) (seq 0 (S (snd β)))
  else β::flat_map (fun m => [(m,true,m);(m,false,m)]) (seq 0 (snd β)).

Lemma lower_squares_spec α β :
  square β -> α ∈ lower_squares β <-> square α /\ α ⋅ β = β.
Proof.
  intros Sq;unfold lower_squares.
  destruct β as ((n0,b),n);replace (snd (fst (n0, b, n))) with b by reflexivity.
  destruct b;[|simpl];rewrite in_flat_map;simpl;setoid_rewrite in_seq;split;rewrite <-Sq;simpl.
  - intros (x&Ix&[<-|[<-|F]]);try (exfalso;apply F);(split;[reflexivity|]);
      unfold prod_binding;simpl;simpl_nat.
    + destruct_ltb x n;[destruct_ltb n x;[replace x with n in * by lia|exfalso;lia]|];reflexivity.
    + destruct_ltb x n;[destruct_ltb n x;[replace x with n in * by lia|exfalso;lia]|];reflexivity.
  - destruct α as ((n'&m')&p').
    intros (E1&E2);replace p' with n' in * by apply E1.
    revert E2;unfold prod_binding;destruct_ltb n' n;[destruct_ltb n n'|];simpl;intro E2.
    + replace n' with n in * by lia.
      exists n;split;[lia|destruct m';tauto].
    + exfalso;inversion E2;lia.
    + exists n';split;[lia|destruct m';tauto].
  - intros [<-|(x&Ix&[<-|[<-|F]])];try (exfalso;apply F);(split;[reflexivity|]);
      unfold prod_binding;simpl;simpl_nat.
    + destruct_ltb n n;[reflexivity|lia].
    + destruct_ltb x n;[lia|reflexivity].
    + destruct_ltb x n;[lia|reflexivity].
  - destruct α as ((n'&m')&p').
    intros (E1&E2);replace p' with n' in * by apply E1.
    revert E2;unfold prod_binding;destruct_ltb n' n;[destruct_ltb n n'|];simpl;intro E2.
    + replace n' with n in * by lia.
      rewrite orb_false_r in E2;inversion E2;subst;tauto.
    + exfalso;inversion E2;lia.
    + right;exists n';split;[lia|destruct m';tauto].
Qed.

(** We may write the following detailed characterisation of the elements of [lower_squares β]. *)
Lemma lower_squares_alt  α β :
  square β -> α ∈ lower_squares β
              <-> square α /\ (c_binding α < c_binding β
                               \/ (c_binding α = c_binding β /\ negb (snd (fst α))||snd(fst β) = true)).
Proof.
  intros S;rewrite (lower_squares_spec _ S).
  split;intros (S'&E);(split;[assumption|]).
  - revert E;destruct α as ((m1&n1)&p1),β as ((m2&n2)&p2);unfold prod_binding;simpl;
      unfold square,d_binding in *;simpl in *;subst.
    destruct_ltb m1 m2;[destruct_ltb m2 m1|];intro E;inversion E.
    + right;split;[reflexivity|].
      rewrite H1.
      destruct n1;simpl;[|reflexivity].
      rewrite <- H1;reflexivity.
    + simpl_nat;subst;lia.
    + left;lia.
  - revert E;destruct α as ((m1&n1)&p1),β as ((m2&n2)&p2);unfold prod_binding;simpl;
      unfold square,d_binding in *;simpl in *;subst.
    intros [I|(->&E)].
    + apply PeanoNat.Nat.ltb_lt in I as ->.
      simpl_nat;reflexivity.
    + destruct_ltb m2 m2;[|lia].
      destruct n1;[|reflexivity].
      simpl in E;subst;reflexivity.
Qed.

(** If the product of two squares belongs to [lower_squares γ], so does its arguments. *)
Lemma lower_squares_prod α β γ :
  square α -> square β -> square γ -> α ⋅ β ∈ lower_squares γ ->
  α ∈ lower_squares γ /\ β ∈ lower_squares γ.
Proof.
  intros s1 s2 s3 I.
  rewrite lower_squares_spec in I by assumption;destruct I as (_&E). 
  repeat rewrite lower_squares_spec by assumption.
  rewrite <- E.
  repeat rewrite <- prod_binding_maxBind;repeat apply maxBind_square;try assumption.
  split;(split;[assumption|]).
  - repeat rewrite maxBind_assoc.
    rewrite maxBind_idem;reflexivity.
  - repeat rewrite (maxBind_comm _ β),maxBind_assoc.
    rewrite maxBind_assoc,maxBind_idem;reflexivity.
Qed.

(** [lower_squares b] only contains bindings of smaller size. *)
Lemma lower_squares_size a b : square b -> a ∈ lower_squares b -> size a <= size b.
Proof.
  intros S I.
  pose proof I as E;apply (lower_squares_alt _ S) in E as (S'&E).
  unfold size.
  rewrite <- S,<-S'.
  destruct E as [E|(->&_)];lia.
Qed.

(** Technical remark: *)
Remark product_square_close_balanced β1 β2 β3 :
  square β1 -> β1 ⋅ β2 = β3 -> c_binding β3 = 0 ->
  exists N1 N2 N3 t1 t2 t3,
    β1 = (N1,t1,N1)
    /\ β2 = (N2,t2,0)
    /\ β3 = (N3,t3,0)
    /\ N1 <= N2
    /\ N2 = N3
    /\ ((t2 = t3 /\ (forall β, β ∈ lower_squares β1 -> β ⋅ β2 = β2))
        \/ (t1 = true /\ t2 = false /\ t3 = true /\ N1 = N2
            /\ lower_squares β1 ≈ β1 :: lower_squares (N1,false,N1)
            /\(forall β, β ∈ lower_squares (N1,false,N1) -> β ⋅ β2 = β2))).
Proof.
  intros Sq E eq.
  destruct β1 as ((N1,t1),x),β2 as ((N2,t2),x'),β3 as ((N3,t3),x'').
  replace x with N1 in * by (apply Sq);clear Sq x.
  replace x'' with 0 in * by apply eq;clear eq x''.
  pose proof E as E0;revert E;unfold prod_binding at 1.
  destruct_ltb N1 N2;[destruct_ltb N2 N1;[replace N2 with N1 in * by lia|]|];
    intros heq;inversion heq;clear heq;subst.
  - exists N3, N3, N3, t1, t2, (t1||t2).
    repeat (split;[reflexivity|]).
    destruct t2.
    + rewrite orb_true_r.
      left;split;[reflexivity|].
      intros β Iβ.
      apply lower_squares_spec in Iβ as (Sq&E);[|reflexivity].
      transitivity ((N3,t1,N3)⋅(N3, true, 0)).
      * rewrite <- E,<- prod_assoc.
        f_equal.
        unfold prod_binding.
        destruct_ltb N3 N3;[|lia].
        rewrite orb_true_r;reflexivity.
      * unfold prod_binding.
        destruct_ltb N3 N3;[|lia].
        rewrite orb_true_r;reflexivity.
    + destruct t1.
      * right.
        repeat (split;[reflexivity|]).
        split.
        -- unfold lower_squares.
           simpl.
           intros ((x,t),y);simpl.
           repeat rewrite in_flat_map.
           setoid_rewrite in_seq.
           intuition.
           ++ inversion H0;subst.
              destruct N3;[tauto|].
              right;right;exists 0;split;[lia|simpl;tauto].
           ++ inversion H;subst.
              destruct N3;[tauto|].
              right;right;exists 0;split;[lia|simpl;tauto].
           ++ destruct H as (k&Lk&Ik).
              destruct_eqX k N3;subst.
              ** simpl in Ik;tauto.
              ** right;right;exists k;split;[lia|assumption].
           ++ symmetry in H0;inversion H0;subst.
              destruct N3;[tauto|].
              right;right;exists (S N3);simpl;split;[lia|simpl;tauto].
           ++ symmetry in H;inversion H;subst.
              destruct N3;[tauto|].
              right;right;exists (S N3);simpl;split;[lia|simpl;tauto].
           ++ destruct H as (k&Lk&Ik).
              destruct k;[simpl in Ik;tauto|].
              right;right;exists (S k);simpl;split;[lia|simpl;tauto].
        -- intros β Iβ.
           apply lower_squares_spec in Iβ as (Sq&E);[|reflexivity].
           transitivity ((N3,false,N3)⋅(N3, false, 0)).
           ++ rewrite <- E,<- prod_assoc.
              f_equal.
              unfold prod_binding.
              destruct_ltb N3 N3;[|lia].
              reflexivity.
           ++ unfold prod_binding.
              destruct_ltb N3 N3;[reflexivity|lia].
      * left;split;[reflexivity|].
        intros β Iβ.
        apply lower_squares_spec in Iβ as (Sq&E);[|reflexivity].
        transitivity ((N3,false,N3)⋅(N3, false, 0)).
        -- rewrite <- E,<- prod_assoc.
           f_equal.
           unfold prod_binding.
           destruct_ltb N3 N3;[|lia].
           reflexivity.
        -- unfold prod_binding.
           destruct_ltb N3 N3;[reflexivity|lia].
  - lia.
  - simpl_nat.
    exists N1,N2,N2,t1,t3,t3.
    repeat (split;[reflexivity||lia|]).
    left;split;[reflexivity|].
    intros β Iβ.
    apply lower_squares_spec in Iβ as (Sq&E);[|reflexivity].
    rewrite <- E0 at 1;rewrite prod_assoc,E;assumption.
Qed.


