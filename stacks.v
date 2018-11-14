(** * RIS.stacks : an algebra of stacks. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export tools atoms bijection.

Section s.
  Context {atom : Set}{𝐀 : Atom atom}.
(** * Definitions *)
(** The main data structure in this module is stacks. These are lists of pairs of names. *)
Definition stack {A : Atom atom}:= list (atom * atom).

(** A stack is accepting exactly when its two projections coincide. *)
Notation " s  ✓ " := (prj1 s = prj2 (s : stack)) (at level 30).
 
(** The predicate [absent s a b] holds when [a] does not appear in the first component of a pair in [s], and [b] does not appear in second components. *)
Definition absent (s : stack) a b :=
  ~ a ∈ prj1 s /\ ~ b ∈ prj2 s.

(** The boolean predicate [absentb] is meant to reflects [absent]. *)
Definition absentb (s:stack) a b := negb (inb a (prj1 s) || inb b (prj2 s)).

(** [a] and [b] are paired in [s] if either:
    - [a] and [b] are equal and [a] is not mentioned anywhere in [s];
    - [s] can be decomposed as [s1++(a,b)::s2], such that [absent s1 a b].
*)
Definition paired s a b :=
  (b=a /\ absent s a a)
  \/ (exists s1 s2, s = s1++(a,b)::s2 /\ absent s1 a b).

Notation " s ⊨ a ↦ b  " := (paired s a b) (at level 80).

(** The boolean predicate [pairedb] is meant to reflects [paired]. *)
Fixpoint pairedb (s:stack) a b :=
  match s with
  | [] => a=?=b
  | (c,d)::s =>
    (c,d)=?=(a,b)
    || (negb(c=?=a) && (negb(d=?= b) && pairedb s a b))
  end.


(** * Simple properties *)
(** ** Accepting *)
(** A stack is accepting if it only contains reflexive pairs. *)
Lemma Accepting_refl s : s ✓ <-> (forall a b, (a,b) ∈ s -> a=b).
Proof.
  induction s as [|(a,b) s];simpl;try tauto;split.
  - intros E1 c d [E2|I];inversion E1;[inversion E2|];subst;auto.
    apply IHs;auto.
  - intro h;f_equal.
    + apply h;tauto.
    + apply IHs;intros;apply h;tauto.    
Qed.

(** [l⊗l] is always accepting, and so is the empty stack. *)
Remark Accepting_combine l : (l⊗l) ✓.
Proof. rewrite combine_fst,combine_snd;auto. Qed.

Remark Accepting_nil : (@nil (atom*atom)) ✓.
Proof. reflexivity. Qed.


Remark Accepting_cons p s : (p::s) ✓ <-> s ✓ /\ fst p = snd p.
Proof.
  simpl;split.
  - intro E;inversion E;auto.
  - intros (->&->);auto.
Qed.

Remark Accepting_cons_refl a s : ((a,a)::s) ✓ <-> s ✓.
Proof. rewrite Accepting_cons;simpl;tauto. Qed.

Remark Accepting_app s s' : (s++s') ✓ <-> s ✓ /\ s' ✓.
Proof.
  repeat rewrite map_app;split.
  - intro E;apply length_app in E as (->&->);auto.
    rewrite map_length,map_length;reflexivity.
  - intros (->&->);reflexivity.
Qed.

(** If [s] is accepting, so is [s ⊖ (a,b)]. *)
Remark Accepting_rmfst s a b : s ✓ -> (s ⊖ (a,b)) ✓.
Proof. repeat rewrite Accepting_refl;intros h x y I;apply rmfst_decr in I;apply h,I. Qed.

(** ** absent *)
(** [absent s a b] holds if and only if for any pair in [s] the first component differs from [a] and the second differs from [b]. *)
Lemma absent_alt_def s a b : absent s a b <-> forall x y, (x,y) ∈ s -> x <> a /\ y <> b.
Proof.
  unfold absent;repeat rewrite in_map_iff;split.
  - intros (h1&h2) x y I;split;intros -> .
    + apply h1;exists (a,y);split;auto.
    + apply h2;exists (x,b);split;auto.
  - intro h;split;intros ((x,y)&E&I);simpl in E;subst;apply h in I;tauto.
Qed.

Remark absent_app s1 s2 a b :
  absent (s1++s2) a b <-> absent s1 a b /\ absent s2 a b.
Proof. unfold absent;repeat rewrite map_app;simpl_In;tauto. Qed.

Remark absent_cons s a b c d :
  absent ((a,b)::s) c d <-> a<>c /\ b<>d /\ absent s c d.
Proof. unfold absent;simpl;simpl;tauto. Qed.

Remark absent_flip s a b :
  absent s a b <-> absent (s`) b a.
Proof.
  revert s a b;cut (forall s a b, absent s a b -> absent (s`) b a).
  - intros h s a b;split;auto.
    intro I;apply h in I;rewrite flip_involutive in I;apply I.
  - intros s a b (I1&I2);split;unfold flip;rewrite in_map_iff in *;setoid_rewrite in_map_iff;
      intros ((x&y)&<-&(c&d)&E&I);inversion E;subst.
    + apply I2;eexists;split;[|eauto];auto.
    + apply I1;eexists;split;[|eauto];auto.
Qed.

Remark absent_mix s1 s2 a b c :
  absent s1 a b -> absent s2 b c -> absent (s1 ⋈ s2) a c.
Proof.
  intros (I1&_) (_&I2);unfold absent;repeat rewrite in_map_iff;
    split;intros ((x,y)&<-&I);simpl in *.
  - apply in_combine_l in I;tauto.
  - apply in_combine_r in I;tauto.
Qed.

(** The [absent] predicate commutes with the action of permutations. *)
Lemma absent_perm p s a b : absent (p∙s) a b <-> absent s (p∗∙a) (p∗∙b).
Proof.
  revert p s a b;cut(forall p s a b, absent s (p∗∙a) (p∗∙b) ->  absent (p∙s) a b).
  - intros h p s a b;split;auto.
    intros P;rewrite <- (act_pinv_p p) at 1;apply h;repeat rewrite inverse_comp_l;auto.
  - intros p s a b (A1&A2).
    split;rewrite in_map_iff in *;setoid_rewrite In_act_lists; intros ((c,d)&E&I);simpl in *;subst.
    + apply A1;exists (p∗∙(a,d));split;auto.
    + apply A2;exists (p∗∙(c,b));split;auto.
Qed.

(** [absentb] reflects [absent]. *)
Lemma absentb_correct a b s : absent s a b <-> absentb s a b = true.
Proof.
  unfold absentb;rewrite negb_true_iff,<-not_true_iff_false,orb_true_iff,inb_spec,inb_spec;
    unfold absent;tauto.
Qed.

Remark absentb_false a b s : ~ absent s a b <-> absentb s a b = false.
Proof. rewrite <- not_true_iff_false,absentb_correct;tauto. Qed.

Remark absentb_cons s a b c d :
  absentb ((a,b)::s) c d = negb (a=?=c) && negb (b=?=d) && absentb s c d.
Proof.
  apply eq_true_iff_eq;repeat rewrite andb_true_iff||rewrite negb_true_iff,eqX_false.
  repeat rewrite <-absentb_correct;rewrite absent_cons;tauto.
Qed.

Remark absentb_app s1 s2 a b :
  absentb (s1++s2) a b = absentb s1 a b && absentb s2 a b.
Proof.
  apply eq_true_iff_eq;rewrite andb_true_iff.
  repeat rewrite <-absentb_correct;rewrite absent_app;tauto.
Qed.

(** If [s] and [s'] are equivalent (contain the same pairs), then [a,b] is absent from [s] if and only if it is absent from [s']. *)
Global Instance absent_equivalent :
  Proper ((@equivalent (atom*atom)) ==> eq ==> eq ==> iff) absent.
Proof. intros s1 s2 e a' a -> b' b ->;unfold absent;rewrite e;tauto. Qed.

Global Instance absentb_equivalent :
  Proper ((@equivalent (atom*atom)) ==> eq ==> eq ==> eq) absentb.
Proof.
  intros s1 s2 e a' a -> b' b ->;apply eq_true_iff_eq;repeat rewrite <- absentb_correct;rewrite e;tauto.
Qed.

(** We can simplify [rmfst]. *)
Lemma rmfst_absent s a b : absent s a b -> s ⊖ (a,b) = s.
Proof. intros (A1&A2);apply rmfst_notin;intro I;apply A1,in_map_iff;exists (a,b);auto. Qed.

Lemma rmfst_present s s' a b : absent s a b -> (s++(a,b)::s') ⊖ (a,b) = s++s'.
Proof. intros (A1&A2);apply rmfst_in;intro I;apply A1,in_map_iff;exists (a,b);auto. Qed.

(** ** paired *)
(** For accepting stacks, [a] and [b] are paired if and only if they are equal. *)
Remark paired_Accepting s a b : s ✓ -> (s ⊨ a ↦ b) <-> b = a.
Proof.
  unfold paired;intros Ac;rewrite Accepting_refl in Ac;split.
  - intros [(->&A)|(s1&s2&->&A)];auto.
    symmetry;apply Ac;simpl_In;auto.
  - intros -> ; case_in (a,a) s.
    + apply decomposition in I as (s1&s2&->&I).
      right;exists s1,s2;split;auto.
      apply absent_alt_def;intros x y I'.
      replace y with x in * by (apply Ac;simpl_In;tauto).
      split;intros ->;tauto.
    + left;split;auto.
      apply absent_alt_def;intros x y I'.
      replace y with x in * by (apply Ac;simpl_In;tauto).
      split;intros ->;tauto.
Qed.

Remark paired_app s s' a b :
  (s++s' ⊨ a ↦ b) <-> ((s ⊨ a ↦ b) /\ (a,b) ∈ s) \/ (absent s a b /\ s' ⊨ a ↦ b).
Proof.
  unfold paired;split.
  - intros [(->&A)|(t1&t2&E&A)].
    + apply absent_app in A as (A1&A2);auto.
    + levi E;subst;clear E.
      * right;split;auto;right;exists [],t2;simpl;split;auto;split;simpl;tauto.
      * inversion E1;subst;clear E1.
        simpl_In;left;split;auto.
        right;exists t1,w;auto.
      * rewrite absent_app in A;right;split;[tauto|].
        right;exists(a0::w),t2;split;tauto.
  - intros [([(->&A1)|(t1&t2&->&A1)]&I)|(A1&[(->&A2)|(t1&t2&->&A2)])].
    + exfalso;apply A1,in_map_iff;exists (a,a);simpl;auto.
    + right;exists t1,(t2++s');rewrite app_ass;simpl;auto.
    + left;rewrite absent_app;auto.
    + right;exists (s++t1),t2;rewrite app_ass,absent_app;simpl;auto.
Qed.

Remark paired_flip s a b : (s ⊨ a ↦ b) <-> s` ⊨ b ↦ a.
Proof.
  revert s a b;cut (forall s a b, (s ⊨ a ↦ b) -> s` ⊨ b ↦ a).
  - intros h s a b;split;auto;intro I;apply h in I;rewrite flip_involutive in I;apply I.
  - intros s a b [(->&A)|(s1&s2&->&A)];apply absent_flip in A.
    + left;auto.
    + right;rewrite flip_app;simpl.
      exists (s1`),(s2`);auto.
Qed.

Remark paired_mix s1 s2 a b c :
  prj2 s1 = prj1 s2 -> (s1 ⊨ a ↦ b) -> (s2 ⊨ b ↦ c) ->
  (s1 ⋈ s2 ⊨ a ↦ c)
  /\ (s1⋈s2)⊖(a,c) = (s1⊖(a,b))⋈(s2⊖(b,c))
  /\ prj2 (s1⊖(a,b)) = prj1 (s2⊖(b,c)).
Proof.
  intros E [(->&A1)|(t1&t2&->&A1)][(->&A2)|(r1&r2&->&A2)].
  - split.
    + left;split;auto;eapply absent_mix;eauto.
    + repeat rewrite rmfst_absent;auto;eapply absent_mix;eauto.
  - rewrite map_app in E;simpl in E.
    exfalso;destruct A1 as (_&A);apply A;rewrite E;simpl_In;auto.
  - rewrite map_app in E;simpl in E.
    exfalso;destruct A2 as (A&_);apply A;rewrite <- E;simpl_In;auto.
  - repeat rewrite rmfst_present;auto.
    repeat rewrite map_app in *;simpl in *.
    pose proof A1 as (I1&I2);pose proof A2 as (I3&I4).
    apply decomp_unique in E as (E1&E2);auto.
    repeat rewrite mix_app;auto using proj_length;simpl.
    split;[|split;[|congruence]].
    + right;exists (t1⋈r1),(t2⋈r2);split;auto.
      split;rewrite mix_fst||rewrite mix_snd;auto using proj_length.
    + apply rmfst_present;simpl;eapply absent_mix;eauto.
Qed.

Remark paired_cons s a b c d :
  ((c,d)::s ⊨ a ↦ b) <-> (c,d)=(a,b) \/ (c<>a /\ d<>b /\ s ⊨ a ↦ b).
Proof.
  replace ((c,d)::s) with ([(c,d)]++s) by reflexivity.
  rewrite paired_app;split.
  - intros [(_&[E|F])|((a1&a2)&E)];simpl in *;try tauto.
  - intros [E|(N1&N2&E)].
    + rewrite E;left;split;simpl;auto;right;exists [],[];repeat split;simpl;auto.
    + right;split;auto;split;simpl;tauto.
Qed.

Remark rmfst_paired s a b c d :
  (a, b) <> (c, d) -> (s ⊨ c ↦ d) -> s ⊖ (a, b) ⊨ c ↦ d.
Proof.
  intros N [(->&a1&a2)|(?&?&->&A)].
  - left;split;auto.
    split;rewrite rmfst_decr;auto.
  - case_in (a,b) (x++(c,d)::x0).
    + apply decomposition in I as (?&?&E0&Ia);rewrite E0.
      rewrite rmfst_in;auto.
      right;levi E0;subst;inversion E1;subst;clear E0 E1.
      * tauto.
        * exists (x1++w),x0;rewrite app_ass;split;auto.
          rewrite absent_app in *;rewrite absent_cons in A;tauto.
        * rewrite app_ass;exists x,(w++x2);simpl;split;auto.
    + rewrite rmfst_notin;auto.
      right;exists x,x0;split;auto.
Qed.

Remark paired_rmfst s a b c d :
  a<>c -> b <> d -> (s ⊖ (a, b) ⊨ c ↦ d) -> s ⊨ c ↦ d.
Proof.
  intros n1 n2;case_in (a,b) s.
  - apply decomposition in I as (?&?&->&Ia).
    rewrite rmfst_in;auto;intros [(->&A)|(?&?&E&A)].
    + left;split;repeat rewrite absent_app in *||rewrite absent_cons in *;tauto.
    + right;levi E;subst;clear E.
      * exists (x1++[(a,b)]),x2;rewrite app_ass;simpl;split;auto.
        rewrite absent_app,absent_cons;repeat (split;auto).
      * inversion E1;subst;clear E1.
        exists x1,(w++(a,b)::x0);rewrite app_ass;simpl;split;auto.
      * exists (x++(a,b)::a0::w),x2;rewrite app_ass;simpl;split;auto.
        repeat rewrite absent_app in *||rewrite absent_cons in *;tauto.
  - rewrite rmfst_notin;tauto.
Qed.

(** The boolean predicate [pairedb] reflects [paired]. *)
Lemma pairedb_spec s a b : (s⊨a↦b) <-> pairedb s a b = true.
Proof.
  induction s as [|(c,d)s];simpl;auto.
  - rewrite eqX_correct;split;[intros [(->&_)|(?&?&F&_)]|intros ->;left;repeat split;simpl];auto.
    simpl_words.
  - rewrite paired_cons,IHs,orb_true_iff.
    repeat rewrite andb_true_iff||rewrite negb_orb||rewrite negb_true_iff.
    repeat rewrite eqX_correct||rewrite eqX_false;tauto.
Qed.
(* begin hide *)
Ltac case_paired s a b :=
  let hp := fresh "hp" in
  case_eq (pairedb s a b);intro hp;
  [|rewrite <- not_true_iff_false in hp];rewrite <- pairedb_spec in hp.
(* end hide *)

(** It is worth noticing that is [s] pairs [a] with [b] with [d], then [b] and [d] are equal. Symmetrically, if both [a] and [b] are paired with [c], then they are equal. *)
Remark paired_inj s a b c d : (s ⊨ a ↦ b) -> (s ⊨ c ↦ d) -> a=c <-> b=d.
Proof.
  intros [(->&A1)|(t1&t2&E1&A1)] [(->&A2)|(u1&u2&E2&A2)].
  - tauto.
  - rewrite E2 in A1;destruct A1 as (A11&A12).
    split;intros ->;exfalso.
    + apply A11;simpl;rewrite map_app;simpl; simpl_In;tauto.
    + apply A12;simpl;rewrite map_app;simpl; simpl_In;tauto.
  - rewrite E1 in A2;destruct A2 as (A21&A22).
    split;intros ->;exfalso.
    + apply A21;simpl;rewrite map_app;simpl; simpl_In;tauto.
    + apply A22;simpl;rewrite map_app;simpl; simpl_In;tauto.
  - rewrite E1 in E2;levi E2.
    + inversion E0;tauto.
    + inversion E0;subst;try tauto.
      destruct A1 as (A11&A12).
      split;intros ->;exfalso.
      * apply A11;simpl;rewrite map_app;simpl; simpl_In;tauto.
      * apply A12;simpl;rewrite map_app;simpl; simpl_In;tauto.
    + inversion E0;subst;try tauto.
      destruct A2 as (A11&A12).
      split;intros ->;exfalso.
      * apply A11;simpl;rewrite map_app;simpl; simpl_In;tauto.
      * apply A12;simpl;rewrite map_app;simpl; simpl_In;tauto.
Qed.

(** The pairing predicate commutes with permutation actions. *)
Lemma paired_perm p s a b : (p∙s ⊨ a ↦ b) <-> s ⊨ p∗∙a ↦ p∗∙b.
Proof.
  revert p s a b;cut (forall p a b s, (s ⊨ p∗∙a ↦ p∗∙b) -> p∙s ⊨ a ↦ b).
  - intros h p s a b;split;auto.
    intro P;rewrite <- (act_pinv_p p) at 1.
    apply h;repeat rewrite inverse_comp_l;auto.
  - intros p a b s [(E&A)|(s1&s2&E&A)].
    + apply perm_bij in E;subst.
      left;split;auto.
      apply absent_perm;auto.
    + subst;right;exists (p∙s1),(p∙s2);split.
      * rewrite (act_lists_app p s1),act_lists_cons;simpl.
        unfold act at 2,act_pair;simpl;repeat rewrite inverse_comp_r;auto.
      * apply absent_perm,A.
Qed.

(** If a stack [s1++s2] validates the pair [a,b], then three cases are possible:
    - [s1] validates the pair by containing it;
    - [a,b] is absent from [s1], and [s2] validates the pair by containing it;
    - [a] and [b] are equal, and both [s1] and [s2] validate the pair by absence.
    The following technical lemma witnesses this case analysis, and provides a closed formula for [s1++s2 ⊖ (a,b)] in each case.
 *)
Lemma rmfst_app_dec_stacks s1 s2 a b :
  (s1++s2 ⊨ a ↦ b) ->
  (exists l1 l2, s1 = l1++(a,b)::l2 /\ absent l1 a b
            /\ (s1++s2)⊖(a,b) = l1++l2++s2)
  \/ (exists m1 m2, s2 = m1++(a,b)::m2 /\ absent (s1++m1) a b
              /\ (s1++s2)⊖(a,b) = s1++m1++m2)
  \/ (a=b /\ absent (s1++s2) a b
     /\ (s1++s2)⊖(a,b) = s1++s2).
Proof.
  intro p;apply paired_app in p as [([(->&A1)|(l1&l2&->&A1)]&I1)
                                   |(A1&[(->&A2)|(l1&l2&->&A2)])].
  - exfalso;apply A1,in_map_iff;exists (a,a);split;auto.
  - left;exists l1,l2;repeat (split;auto).
    rewrite app_ass;apply rmfst_present;auto.
  - right;right;rewrite rmfst_absent;rewrite absent_app;tauto.
  - right;left;exists l1,l2;rewrite <- app_ass;rewrite rmfst_present,app_ass;rewrite absent_app;tauto.
Qed.


(** * Converting a stack into a permutation *)
(** [image s] converts the stack [s] into a function from atoms to atoms:
    - if [a] does not appear in the first projection of [s], [image s a] is [a] itself;
    - otherwise, [image s a] returns an atom [b] such that [s] can be decomposed as [s1++(a,b)::s2], where [a] does not appear in the first projection of [s1]. Note that [b] may appear in the second projection of [s1], therefore it is not always the case that [s⊨ a ↦ image s a].
*)
Fixpoint image (s:stack) a :=
  match s with
  | [] => a
  | (c,d)::s => if a=?=c then d else image s a
  end.

(** However, if there exists a [b] such that [s⊨ a↦b], then [image s a] will coincide with that [b]. *)
Lemma image_spec s a b : (s⊨ a↦b) -> image s a = b.
Proof.
  induction s as [|(c,d)s];simpl.
  - intros [(->&_)|(?&?&F&_)];[reflexivity|simpl_words].
  - rewrite paired_cons.
    intros [e|(n1&n2&p)].
    + inversion e;subst;clear e.
      simpl_beq;auto.
    + simpl_beq;apply IHs,p.
Qed.

(** [var_perm l s] tries to compute a permutation sending names from [l] to their image by [s]. *)
Definition var_perm (l:list atom) s := l >> (map (image s) l).

Fixpoint var_perm'  (l:list atom) s : option perm :=
  match s with
  | [] => Some []
  | (a,b)::s =>
      match var_perm' (l∖a) s with
      | None => None
      | Some p => 
        if (existsb (fun c => p ∙ c =?= b) (l ∖ a))
        then None
        else
          if inb a l
          then Some ((p∙a,b)::p)
          else Some p
      end 
  end.

Lemma var_perm'_Some l s p a :
  var_perm' l s = Some p -> a ∈ l -> s ⊨ a ↦ p ∙ a.
Proof.
  revert a l p;induction s as [|(a,b) s];intros c l p;simpl.
  - intros E;inversion E;subst.
    intros I;left;repeat split;auto.
  - case_eq (var_perm' (l∖a) s);[|discriminate].
    intros p' E.
    case_eq (existsb (fun c : atom => (p' ∙ c) =?= b) (l∖a)).
    + rewrite existsb_exists;intros (d&Id&Ed).
      apply rm_In in Id as (Id&N);rewrite eqX_correct in Ed;subst.
      discriminate.
    + rewrite <- not_true_iff_false,existsb_exists;intros h.
      setoid_rewrite eqX_correct in h.
      case_in a l.
      * intro E0;inversion E0;subst;clear E0.
        intro Ic;apply paired_cons.
        destruct_eqX a c;subst;rewrite act_cons.
        -- simpl_beq;tauto. 
        -- pose proof N as N';rewrite <- (act_bij p') in N'.
           repeat simpl_beq.
           destruct_eqX (p'∙c) b.
           ++ exfalso;apply h;exists c;split;[|tauto].
              apply rm_In;tauto.
           ++ right;split;[tauto|split].
              ** intros ->;apply h;exists c;split;[|tauto].
                 apply rm_In;tauto.
              ** apply (IHs _ _ _ E).
                 apply rm_In;tauto.
      * intro E0;inversion E0;subst;clear E0.
        intros Ic;destruct_eqX a c;[tauto|].
        apply paired_cons;right;split;[tauto|split].
        -- intros ->;apply h;exists c;split;[|reflexivity].
           apply rm_In;tauto.
        -- apply (IHs _ _ _ E).
           apply rm_In;tauto.
Qed.
Lemma var_perm'_None l s :
  var_perm' l s = None -> exists a, a ∈ l /\ forall b, ~ (s ⊨ a ↦ b).
Proof.
  revert l;induction s as [|(a,b) s];intros l;simpl.
  - discriminate.
  - case_eq (var_perm' (l∖a) s).
    + intros p' E.
      case_eq (existsb (fun c : atom => (p' ∙ c) =?= b) (l∖a)).
      * rewrite existsb_exists;intros (d&Id&Ed) _.
        apply rm_In in Id as (Id&N);rewrite eqX_correct in Ed;subst.
        assert (I : d ∈ l∖a) by (apply rm_In;tauto).
        pose proof (var_perm'_Some E I) as P.
        exists d;split;auto.
        intros b;rewrite paired_cons.
        intros [F|(_&N'&P')].
        ++ inversion F;tauto.
        ++ pose proof (paired_inj P P');tauto.
      * case_in a l;discriminate.
    + intros E _.
      destruct (IHs _ E) as (c&Ic&hc).
      apply rm_In in Ic as (Ic&N).
      exists c;split;[tauto|].
      intros d;rewrite paired_cons.
      intros [e|(_&N'&P)].
      * inversion e;tauto.
      * exact (hc d P).
Qed.

Lemma var_perm'_spec l s p :
  (forall a, a ∈ l -> s ⊨ a ↦ p ∙ a)
  <-> (exists p', var_perm' l s = Some p' /\ (forall a, a ∈ l -> p ∙ a = p' ∙ a)).
Proof.
  case_eq (var_perm' l s).
  - intros p' E;split.
    + intros h;exists p';split;[reflexivity|].
      intros a Ia; apply (paired_inj (h a Ia) (var_perm'_Some E Ia)).
      reflexivity.
    + intros (q&Eq&hq);inversion Eq;subst;clear Eq.
      intros a Ia;rewrite (hq a Ia).
      eapply var_perm'_Some;eauto.
  - intros E;destruct (var_perm'_None E) as (a&Ia&ha).
    split;[|intros (?&F&_);discriminate].
    intros F;exfalso;apply (ha (p∙a)),F,Ia.
Qed.
    
(** If [l] is duplication-free, and if a permutation [p] exists such that [s⊨a↦p∙a] for every name [a] in [l], then for each of these names the action of [var_perm l s] and that of [p] coincide. *)
Lemma var_perm_paired s l p :
  NoDup l -> (forall a, a∈l -> s⊨a↦p∙a) -> forall a, a ∈ l -> var_perm l s ∙ a = p∙a.
Proof.
  intros nd h.
  cut (var_perm l s ∙ l =  p ∙ l);[apply map_bij|].
  unfold var_perm;symmetry.
  replace (map (image s) l) with  (p∙l).
  - symmetry;apply make_bij.
    + apply nd.
    + apply NoDup_map_injective;[|apply nd].
      apply injective_perm.
    + solve_length.
  - apply map_ext_in;intros b Ib.
    rewrite <-(image_spec (h b Ib));auto.
Qed.

(** If [s] is accepting, then [var_perm l s] is the identity permutation. *)
Remark var_perm_accepting s l: s✓ -> var_perm l s ≃ [].
Proof.
  unfold var_perm;intro Ac.
  transitivity (l >> l).
  - intro a;f_equal;f_equal.
    apply map_eq_id;intros b _;apply image_spec,paired_Accepting;auto.
  - clear;induction l;auto.
    + unfold make_perm;reflexivity.
    + simpl;rewrite IHl,act_atom_nil.
      intro b;rewrite act_cons;repeat rewrite IHl,act_atom_nil.
      destruct_eqX b a;auto.
Qed.

(** If [s] is accepting, then [var_perm' l s] is the identity permutation. *)
Remark var_perm'_accepting s l: s✓ -> exists p, var_perm' l s = Some p /\ p ≃ [].
Proof.
  revert l;induction s as [|(a,b) s];intros l;simpl.
  - intros _;exists [];split;reflexivity.
  - intros e0;inversion e0 as [[e1 E]];subst;clear e0.
    apply (IHs (l∖b)) in E as (p&->&Ep).
    case_eq (existsb (fun c : atom => (p ∙ c) =?= b) (l∖b)).
    + rewrite existsb_exists;intros (d&Id&Ed).
      apply rm_In in Id as (Id&N);rewrite eqX_correct in Ed;subst.
      rewrite Ep,act_nil in N;tauto.
    + rewrite <- not_true_iff_false,existsb_exists;intros h.
      rewrite Ep,act_nil.
      setoid_rewrite eqX_correct in h.
      case_in b l.
      * exists ((b,b)::p);split;auto.
        intro c;rewrite act_nil,act_cons.
        repeat rewrite Ep,act_nil.
        destruct_eqX c b;reflexivity.
      * exists p;split;tauto.
Qed.

End s.

Notation " s ⊨ a ↦ b  " := (paired s a b) (at level 80).
Notation " s  ✓ " := (prj1 s = prj2 (s : stack)) (at level 30).

(* begin hide *)
Ltac case_paired s a b :=
  let hp := fresh "hp" in
  case_eq (pairedb s a b);intro hp;
  [|rewrite <- not_true_iff_false in hp];rewrite <- pairedb_spec in hp.
(* end hide *)
