(** * RIS.equiv_stacks : dynamic properties of the binding transducer. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export transducer.

Section s.
  Context {atom X: Set}{𝐀 : Atom atom} {𝐗 : Alphabet 𝐀 X}.

(** * Static equivalence *)
(** We may define the following relation on stacks. *)
Fixpoint equiv_stacks s1 s2 :=
  match s1 with
  | [] => s2 ✓
  | (a,b)::s1 => (s2 ⊨ a ↦ b) /\ equiv_stacks s1 (s2 ⊖ (a,b))
  end.
Infix " == " := equiv_stacks (at level 80).

(** This relation may easily be translated as a boolean relation. *)
Fixpoint equiv_stacksb s1 s2 :=
  match s1 with
  | [] => prj1 s2 =?= prj2 s2
  | (a,b)::s1 => pairedb s2 a b && equiv_stacksb s1 (s2 ⊖ (a,b))
  end.

(** [equiv_stacksb] reflects [equiv_stacks]. *)
Lemma equiv_stacksb_spec s1 s2: s1 == s2 <-> equiv_stacksb s1 s2 = true.
Proof.
  revert s2;induction s1 as [|(a,b)s1];intros s2;simpl.
  - symmetry;apply eqX_correct.
  - rewrite andb_true_iff,pairedb_spec,IHs1;tauto.
Qed.

(** We will now show that [equiv_stacks] is an equivalence relation. Reflexivity is straightforward. *)
Lemma equiv_stacks_Reflexive s : s == s.
Proof.
  induction s as [|(a,b)s];simpl;[|simpl_beq;split];auto.
  right;exists [],s;repeat split;auto.
Qed.

(** Two equivalent stacks validate the same pairs. *)
Lemma equiv_stacks_paired s1 s2 a b : s1 == s2 -> (s1 ⊨ a ↦ b) <-> (s2 ⊨ a ↦ b).
Proof.
  revert s2 a b;induction s1 as [|(a,b)s1];intros s2 c d;simpl.
  - intro A;rewrite (paired_Accepting _ _ A).
    rewrite paired_Accepting;tauto.
  - intros (h1&IH);pose proof (IHs1 _ c d IH) as Eq.
    rewrite paired_cons,Eq;clear Eq IH IHs1.
    destruct h1 as [(->&A)|(t1&t2&->&A)].
    + rewrite (rmfst_absent A) in *.
      split.
      * intros [E|h];[|tauto].
        inversion E;subst;clear E.
        left;auto.
      * intro h;pose proof h as [(->&A')|(?&?&->&A')].
        -- destruct_eqX a c;auto.
        -- right;split;[|split;[|apply h]];intros ->;destruct A as (a1&a2);[apply a1|apply a2];
             rewrite map_app;simpl;simpl_In;tauto.
    + rewrite rmfst_present;auto.
      repeat rewrite paired_app;rewrite paired_cons.
      split.
      * intros [E|(n1&n2&[(P&I)|(A'&P)])];auto.
        -- inversion E;subst;clear E;auto.
        -- right;split;auto.
      * intros [(P&I)|(A'&[E|(n1&n2&P)])];auto.
        -- right;split;[|split];auto;intros ->;destruct A as (a1&a2);[apply a1|apply a2];
             apply in_map_iff;exists (c,d);simpl;auto.
        -- right;split;auto.
Qed.
(* begin hide *)
Global Instance equiv_stacks_paired_bis :
  Proper (equiv_stacks ==> Logic.eq ==> Logic.eq ==> Logic.iff) paired.
Proof. intros s1 s2 E ? a -> ? b -> ;apply equiv_stacks_paired,E. Qed.
Global Instance equiv_stacks_pairedb :
  Proper (equiv_stacks ==> Logic.eq ==> Logic.eq ==> Logic.eq) pairedb.
Proof.
  intros s1 s2 E ? a -> ? b -> .
  apply eq_true_iff_eq;repeat rewrite <- pairedb_spec;apply equiv_stacks_paired,E.
Qed.
(* end hide *)

(** If two stacks are equivalent, then either both are accepting or none of them are. *)
Lemma equiv_stacks_Accepting s1 s2 : s1 == s2 -> s1 ✓ <-> s2 ✓.
Proof.
  revert s2;induction s1 as [|(a,b)s1];intro s2;simpl;[tauto|].
  intros (h&e);apply IHs1 in e;clear IHs1.
  destruct h as [(->&A)|(?&?&->&A)].
  - rewrite rmfst_absent in e;auto.
    rewrite <-e;clear e;split;[intro e;inversion e|intros ->];reflexivity.
  - rewrite rmfst_present in e;auto.
    repeat rewrite map_app in *;simpl;split.
    + intro E;inversion E as [[h e']];subst.
      rewrite e in e';apply length_app in e' as (->&->);[|solve_length];reflexivity.
    + intro e';apply length_app in e' as (e1&e2);[|solve_length].
      inversion e2 as [[e3 e4]];subst;clear e2.
      f_equal;apply e;congruence.
Qed.

(** Two accepting stacks are always equivalent. *)
Lemma Accepting_equiv_stacks s1 s2 : s1 ✓ -> s2 ✓ -> s1 == s2.
Proof.
  revert s2;induction s1 as [|(a,b)s1];intro s2;simpl;[tauto|].
  intros e0 e2;inversion e0 as [[e0' e1]];subst;clear e0.
  rewrite (paired_Accepting _ _ e2);split;auto.
  apply IHs1;auto.
  apply Accepting_rmfst;auto.
Qed.

(** We may therefore show that [==] is a symmetric relation. *)
Lemma equiv_stacks_Symmetric s1 s2 : s1 == s2 -> s2 == s1.
Proof.
  revert s1;induction s2 as [|(a,b) s2];intros s1;simpl;auto.
  - intro E;rewrite equiv_stacks_Accepting;eauto;reflexivity.
  - intro E;cut (s1 ⊨ a ↦ b ).
    + intro h;split;auto.
      apply IHs2;clear IHs2;revert E.
      revert s2;induction s1 as [|(c,d) s1];intros s2;simpl;
        destruct h as [(->&A)|(t1&t2&E&A)].
      -- intro E;inversion E;subst;auto.
      -- simpl_words.
      -- apply absent_cons in A as (n1&n2&A).
         destruct_eqX (c,d)(a,a);[inversion E;tauto| simpl_beq].
         intros ([(->&A')|(t1&t2&E&A')]&IH);simpl;split.
         ++ apply absent_cons in A' as (_&_&A').
            left;split;auto.
         ++ apply IHs1;auto.
            left;split;auto.
         ++ destruct t1;simpl in *;inversion E;subst;[tauto|].
            apply absent_cons in A' as (_&_&A').
            right;exists t1,t2;split;auto.
         ++ apply IHs1;auto.
            left;split;auto.
      -- destruct_eqX (c,d) (a,b);[tauto|].
         destruct t1;simpl in *;inversion E;subst;[tauto|clear E;simpl_beq].
         apply absent_cons in A as (n1&n2&A).
         intros (P&E);apply paired_cons in P as [F|(_&_&P)];[rewrite F in N;tauto|].
         simpl;split;[tauto|].
         apply IHs1;[|tauto].
         right;exists t1,t2;split;[reflexivity|tauto].
    + eapply equiv_stacks_paired;eauto.
      right;exists [],s2;repeat split;auto.
Qed.

(** The operation [rmfst] is monotonic with respect to [==]. *)
Global Instance equiv_stacks_rmfst :
  Proper (Logic.eq ==> equiv_stacks ==> equiv_stacks) rmfst.
Proof.
  intros x (a,b) -> s1;induction s1 as [|(c,d)s1];intros s2;simpl.
  - intro E;apply Accepting_rmfst;auto.
  - destruct_eqX (a,b)(c,d).
    + inversion E;subst;clear E;intros (p&e);auto.
    + intros (p&e);simpl;split.
      * clear e IHs1 s1;apply rmfst_paired;auto.
      * rewrite rmfst_comm;apply IHs1,e.
Qed.

(** We these facts established we can prove that [==] is transitive. *)
Lemma equiv_stacks_Transitive s1 s2 s3 : s1 == s2 -> s2 == s3 -> s1 == s3.
Proof.
  revert s2 s3;induction s1 as [|(a,b)s1];intros s2 s3;simpl.
  - intros Ok E;rewrite <- equiv_stacks_Accepting;eauto.
  - intros (p&E);destruct s2 as [|(c,d) s2];simpl in *.
    + apply equiv_stacks_Symmetric in E as Ok1;simpl in Ok1.
      intro Ok2;destruct p as [(->&_)|(?&?&F&_)];[|simpl_words].
      rewrite (paired_Accepting _ _ Ok2);split;auto.
      apply Accepting_equiv_stacks;auto.
      apply Accepting_rmfst;auto.
    + apply paired_cons in p.
      revert E;destruct_eqX (a,b)(c,d).
      * clear p;inversion E;subst;clear E.
        intros E1 (p&E2);split;auto.
        eapply IHs1;eauto.
      * destruct p as [F|(n1&n2&p2)];[inversion F;subst;tauto|].
        intros E1 (p'&E2).
        cut (s3 ⊨ a ↦ b ).
        -- intro p3;split;auto.
           eapply IHs1;[eauto|].
           replace ((c, d) :: s2 ⊖ (a, b)) with (((c, d) :: s2) ⊖ (a, b))
             by (simpl;simpl_beq;reflexivity).
           apply equiv_stacks_rmfst;auto.
           simpl;split;auto.
        -- apply paired_rmfst with (a0:=c) (b0:=d);try (intros ->;tauto).
           rewrite <- equiv_stacks_paired;eauto.
Qed.

(** Having proved reflexivity, symmetricity and transitivity, we now know that [==] is indeed an equivalence relation. *)
Global Instance equiv_stacks_equivalence : Equivalence equiv_stacks.
Proof.
  split.
  - intro;apply equiv_stacks_Reflexive.
  - intro;intros;eapply equiv_stacks_Symmetric;eauto.
  - intro;intros;eapply equiv_stacks_Transitive;eauto.
Qed.

(** [cons] is monotonic with respect to [==]. *)
Global Instance equiv_stacks_cons :
  Proper (Logic.eq ==> equiv_stacks ==> equiv_stacks) cons.
Proof.
  intros ? (a,b) -> s1 s2 E.
  simpl;split.
  - right;exists [],s2;repeat split;auto.
  -  simpl_beq;auto.
Qed.

(** If two stacks are equivalent, then their associated [image] functions are extensionally equivalent.  *)
Global Instance equiv_stacks_image :
  Proper (equiv_stacks ==> Logic.eq ==> Logic.eq) image.
Proof.
  intros s1;intros s2 E ? c ->;revert s2 E c;induction s1 as [|(a,b) s1];intros s2 E c;simpl in *.
  - symmetry;apply image_spec,paired_Accepting;auto.
  - destruct E as (p&E).
    rewrite (IHs1 _ E c).
    destruct p as [(->&A)|(t1&t2&->&A)].
    + rewrite rmfst_absent;auto.
      destruct_eqX c a;auto.
      symmetry;apply image_spec;left;auto.
    + rewrite rmfst_present in *;auto.
      destruct_eqX c a;auto.
      * symmetry;apply image_spec;right;exists t1,t2;auto.
      * revert N;clear;intro N;induction t1 as [|(x,y) t1];simpl;auto.
        -- simpl_beq;reflexivity.
        -- destruct_eqX c x;auto.
Qed.

(** It follows that two equivalent stacks yield equivalent permutations for any list. *)
Global Instance equiv_stacks_var_perm :
  Proper (Logic.eq ==> equiv_stacks ==> sequiv) var_perm.
Proof.
  intros ? x -> s1 s2 E;unfold var_perm;revert s1 s2 E;induction x;simpl;auto.
  - intros s1 s2 _; reflexivity.
  - intros s1 s2 E;setoid_rewrite E at 2.
    intro b;repeat rewrite act_cons||rewrite (IHx _ _ E);reflexivity.
Qed.


(** * Definitions *)

Notation " s1 -- α -->> s2 " := (path (fst α) (snd α) s1 s2) (at level 80).
Notation " s1 -- α ---> s2 " := (step s1 (fst α) (snd α) s2) (at level 80).

(** As will be shown later on, the pair of words [w1 s,w2 s] characterises the stack [s]. *)
Definition w1 (s : stack) : word := map close (prj1 s).
Definition w2 (s : stack) : word := map close (prj2 s).
Definition 𝐰 (s : stack) := (w1 s,w2 s).

(** We define bissimilarity of stacks by coinduction, saying that [s1∼s2] holds if for every pair of letters [l1,l2], if [s1] can perform one transition labelled with [l1|l2] to [s3] then [s2] can can follow a transition with the same label to reach [s4] with [s3∼s4], and conversely. *)
Reserved Notation " s1 ∼ s2 " (at level 80).
CoInductive bissimilar : relation stack :=
| prog s1 s2 :
    (forall α, (forall s3, s1 -- α ---> s3 -> exists s4, s2 --α---> s4 /\ s3 ∼ s4)
          /\ (forall s4, s2 --α---> s4 -> exists s3, s1 --α---> s3 /\ s3 ∼ s4))
    -> s1 ∼ s2
where " s1 ∼ s2 " := (bissimilar s1 s2).

(** Similarity is defined analogously. *)
Reserved Notation " s1 ≺ s2 " (at level 80).
CoInductive similar : relation stack :=
| prog2 s1 s2 :
    (forall α, (forall s3, s1 --α---> s3 -> exists s4, s2 --α---> s4 /\ s3 ≺ s4))
    -> s1 ≺ s2
where " s1 ≺ s2 " := (similar s1 s2).

(** We consider here languages to be sets of pairs of words, i.e. predicates over [words*words]. *)
Definition lang := (word * word)%type -> Prop.

(** Two languages are equivalent if they contain the same words. *)
Global Instance eq_sem : SemEquiv lang := fun L M => forall σ, L σ <-> M σ.

(** The language [L] is smaller that the language [M] if every word in [L] belongs to [M]. *)
Global Instance inf_sem : SemSmaller lang := fun L M => forall σ, L σ -> M σ.
(* begin hide *)
Global Instance eq_sem_equivalence : Equivalence (@sequiv _ eq_sem).
Proof. split;intro;intros;firstorder. Qed.
Global Instance inf_sem_preorder : PreOrder (@ssmaller _ inf_sem).
Proof. split;intro;intros;firstorder. Qed.
Global Instance inf_sem_partialorder : PartialOrder (@sequiv _ eq_sem) (@ssmaller _ inf_sem).
Proof. split;intro;intros;firstorder. Qed.
(* end hide *)

(** The semantics of a stack [s] is the set of pairs [u,v] such that there is a path from [s] to some accepting stack labelled with [u,v]. *)
Definition semantics s : lang := fun σ => (exists s', s' ✓ /\ s --σ-->> s').
Notation " ⟦ s ⟧ " := (semantics s).

(** * Lemmas *)
(** ** equiv_stacks *)
(** [fun s => δt s u v] preserves the relation [==]. *)
Global Instance equiv_stacks_δt :
  Proper (equiv_stacks ==> Logic.eq ==> Logic.eq ==> equiv_stacks) δt.
Proof.
  intros s1 s2 E1 ? u -> ? v -> .
  revert s1 s2 v E1;induction u as [|[a|a|x]u];intros s1 s2 [|[b|b|y] v];simpl;auto.
  - intro;apply IHu;rewrite E1;reflexivity.
  - intro E;rewrite E at 1.
    case_paired s2 a b;auto.
    + apply IHu;rewrite E;reflexivity.
    + reflexivity.
  - intro E;case_var s1 x y;case_var s2 x y;try reflexivity.
    + apply IHu,E.
    + exfalso;apply N;rewrite <- E0.
      apply support_eq_action_eq.
      intros a Ia.
      pose proof (var_perm'_Some e Ia) as p1.
      pose proof (var_perm'_Some e0 Ia) as p2.
      rewrite equiv_stacks_paired in p1 by (apply E).
      apply (paired_inj p2 p1);reflexivity. 
    + exfalso;apply var_perm'_None in e0 as (a&Ia&h).
      pose proof (var_perm'_Some e Ia) as p1.
      apply (h (p∙a)).
      rewrite equiv_stacks_paired by (symmetry;apply E).
      apply p1.
    + exfalso;apply N;rewrite <- E0.
      apply support_eq_action_eq.
      intros a Ia.
      pose proof (var_perm'_Some e Ia) as p1.
      pose proof (var_perm'_Some e0 Ia) as p2.
      rewrite equiv_stacks_paired in p1 by (apply E).
      apply (paired_inj p1 p2);reflexivity. 
    + exfalso;apply var_perm'_None in e as (a&Ia&h).
      pose proof (var_perm'_Some e0 Ia) as p1.
      apply (h (p∙a)).
      rewrite equiv_stacks_paired by (apply E).
      apply p1.
Qed.

(** If [s==s'], then [u,v] is compatible with [s] if and only if [s'] is. *)
Global Instance equiv_stacks_compatible :
  Proper (equiv_stacks ==> Logic.eq ==> Logic.eq ==> Logic.eq) compatible.
Proof.
  intros s1 s2 E1 ? u -> ? v -> .
  revert s1 s2 v E1;induction u as [|[a|a|x]u];intros s1 s2 [|[b|b|y] v];simpl;auto.
  - intro;apply IHu;rewrite E1;reflexivity.
  - intro E;rewrite E at 1.
    case_paired s2 a b;auto.
    apply IHu;rewrite E;reflexivity.
  - intro E;case_var s1 x y;case_var s2 x y;auto.
    + apply IHu,E.
    + exfalso;apply N;rewrite <- E0.
      apply support_eq_action_eq.
      intros a Ia.
      pose proof (var_perm'_Some e Ia) as p1.
      pose proof (var_perm'_Some e0 Ia) as p2.
      rewrite equiv_stacks_paired in p1 by (apply E).
      apply (paired_inj p2 p1);reflexivity. 
    + exfalso;apply var_perm'_None in e0 as (a&Ia&h).
      pose proof (var_perm'_Some e Ia) as p1.
      apply (h (p∙a)).
      rewrite equiv_stacks_paired by (symmetry;apply E).
      apply p1.
    + exfalso;apply N;rewrite <- E0.
      apply support_eq_action_eq.
      intros a Ia.
      pose proof (var_perm'_Some e Ia) as p1.
      pose proof (var_perm'_Some e0 Ia) as p2.
      rewrite equiv_stacks_paired in p1 by (apply E).
      apply (paired_inj p1 p2);reflexivity. 
    + exfalso;apply var_perm'_None in e as (a&Ia&h).
      pose proof (var_perm'_Some e0 Ia) as p1.
      apply (h (p∙a)).
      rewrite equiv_stacks_paired by (apply E).
      apply p1.
Qed.

(** ** Characteristic words *)
(** The pair [w1 s,w2 s] belongs to the semantics of [s]. *)
Lemma w_path s : ⟦s⟧ (𝐰 s).
Proof.
  induction s as [|(a,b)s].
  - exists [];split;auto.
    apply pathϵ.
  - simpl in *.
    destruct IHs as (s'&Ok&P).
    exists s';split;auto.
    eapply pathl;[|apply P];simpl.
    split.
    + right;exists [],s;repeat split;auto.
    + simpl;simpl_beq;auto.
Qed.

(** If [w1 s1,w2 s1] is in the semantics of [s2], then [s1==s2]. *)
Lemma w_equiv_stacks s1 s2 :
  ⟦s2⟧ (𝐰 s1) -> s1 == s2.
Proof.
  revert s2;induction s1 as [|(a,b)s1];intros s2 (s3&A&E);simpl in *.
  - inversion E;subst;auto.
  - inversion E;subst;destruct H5 as (h&->);split;auto.
    eapply IHs1;exists s3;auto.
Qed.

(** ** Bissimilarity *)
(** Bissimilarity is an equivalence relation. *)
Global Instance bissimilar_equivalence : Equivalence bissimilar.
Proof.
  split.
  - intro s;revert s;cofix ch;intro s;apply prog;intros α;split;intros s' st;exists s';split;auto.
  - intro s;revert s;cofix ch;intros s1 s2 E;inversion E as [? ? h];subst.
    apply prog;intros α;split;intros s' st;apply h in st as (s''&st&E');
      apply ch in E';eauto.
  - intro s;revert s;cofix ch;intros s1 s2 s3 E1 E2;
      inversion E1 as [? ? h1];inversion E2 as [? ? h2];subst;apply prog;intros α;split;
        intros s' st.
    + apply h1 in st as (s4&st&E1');apply h2 in st as (s5&st&E2').
      pose proof (ch _ _ _ E1' E2') as E;eauto.
    + apply h2 in st as (s4&st&E2');apply h1 in st as (s5&st&E1').
      pose proof (ch _ _ _ E1' E2') as E;eauto.
Qed.

(** Although we have defined bissimilarity in terms of transitions, it may be naturally extended to paths. *)
Lemma bissimilar_path s1 s2 σ s3 :
  s1 ∼ s2 -> s1 --σ-->> s3 -> exists s4, s2 --σ-->> s4 /\ s3 ∼ s4.
Proof.
  intros E P;revert s2 E;induction P as [|s1 u v l1 l2 s s3 st P];intros s2 E.
  - exists s2;split;auto.
  - inversion E as [? ? B];clear E;subst.
    apply (B (l1,l2)) in st as (s4&st&E);clear B.
    destruct (IHP _ E) as (s5&P'&E').
    exists s5;split;eauto.
Qed.

(** In fact [s1] is bissimilar to [s2] exactly when for every pair of words [u,v], there is a path labelled with [u|v] from [s1] if and only if there is one from [s2]. *)
Lemma bissimilar_alt s1 s2 :
  s1 ∼ s2 <-> forall σ, (exists s, s1 --σ-->> s) <-> (exists s, s2 --σ-->> s).
Proof.
  split.
  - intros E σ;split;intros (s&P);eapply bissimilar_path in P as (s'&P'&_);try (exists s';apply P');
      rewrite E;reflexivity.
  - revert s1 s2;cofix ch;intros s1 s2 B;apply prog;intros (l1,l2);split;intros s3 P.
    + cut (exists s, s1 ⊣ [l1]|[l2] ⤅ s);[|exists s3;eapply pathl;eauto].
      intro P';apply (B ([l1],[l2])) in P' as (s4&P').
      inversion P' as [|s' ? ? ? ? ? ? st P''];subst;clear P'.
      inversion P'';subst;clear P''.
      exists s4;split;auto.
      apply ch;intros (u,v).
      transitivity (exists s : stack, s1 ⊣ l1::u | l2::v ⤅ s) ;
        [|transitivity (exists s : stack, s2 ⊣ l1::u | l2::v ⤅ s);[apply (B (_,_))|]];
        split;intros(s&P'); exists s;try eapply pathl';eauto;
          inversion P' as [|s' ? ? ? ? ? ? st' P''];subst.
      * rewrite (step_det P st') in *;auto.
      * rewrite (step_det st st') in *;auto.
    + cut (exists s, s2 ⊣ [l1]|[l2] ⤅ s);[|exists s3;eapply pathl;eauto].
      intro P';apply (B(_,_)) in P' as (s4&P').
      inversion P' as [|s' ? ? ? ? ? ? st P''];subst;clear P'.
      inversion P'';subst;clear P''.
      exists s4;split;auto.
      apply ch;intros (u,v).
      transitivity (exists s : stack, s1 ⊣ l1::u | l2::v ⤅ s) ;
        [|transitivity (exists s : stack, s2 ⊣ l1::u | l2::v ⤅ s);[apply (B(_,_))|]];
        split;intros(s&P'); exists s;try eapply pathl';eauto;
          inversion P' as [|s' ? ? ? ? ? ? st' P''];subst.
      * rewrite (step_det st st') in *;auto.
      * rewrite (step_det P st') in *;auto.
Qed.

(** Bissimilar stacks are equivalent with respect to acceptance. *)
Lemma bissimilar_accepting s1 s2 : s1 ∼ s2 -> s1 ✓ -> s2 ✓.
Proof.
  revert s2;induction s1 as [|(a,b)s1];intros s2 B.
  - intros _;induction s2 as [|(a,b) s2];auto.
    inversion B as [? ? h];subst.
    assert (st: (a, b) :: s2 -- (close a,close b)---> s2).
    + split;[|simpl;simpl_beq;auto].
      right;exists [],s2;repeat split;auto.
    + apply h in st as (s'&st&B').
      destruct st as ([(->&_)|(?&?&F&_)]&->).
      * simpl in *;f_equal;auto.
      * simpl_words.
  - simpl;intro E1;inversion E1 as [[E2 E]];subst;clear E1.
    inversion B as [? ? h];subst.
    assert (st: (b, b) :: s1 -- (close b,close b) ---> s1).
    + split;[|simpl;simpl_beq;auto].
      right;exists [],s1;repeat split;auto.
    + apply h in st as (s'&st&B').
      destruct st as ([(_&A)|(t1&t2&->&A)]&->).
      * rewrite rmfst_absent in B';auto.
      * rewrite rmfst_present in B';auto.
        apply IHs1 in B';auto;repeat rewrite map_app in *;simpl.
        apply length_app in B' as (->&->);[|solve_length];auto.
Qed.

(** Static equivalence implies bissimilarity. *)
Lemma equiv_stacks_bissimilar s1 s2 : s1 == s2 -> s1 ∼ s2.
Proof.
  revert s1 s2;cofix ch;intros s1 s2 E;apply prog;intros α;split;intros s3 P.
  - pose proof P as st;apply path_single_letter in P.
    apply δt_compatible_spec in P as (<-&C).
    exists (δt s2 [fst α] [snd α]);split;auto.
    + apply path_single_letter,δt_compatible_spec;split;auto.
      rewrite <- E,C;auto.
    + apply ch;rewrite E;reflexivity.
  - pose proof P as st;apply path_single_letter in P.
    apply δt_compatible_spec in P as (<-&C).
    exists (δt s1 [fst α] [snd α]);split;auto.
    + apply path_single_letter,δt_compatible_spec;split;auto.
      rewrite E,C;auto.
    + apply ch;rewrite E;reflexivity.
Qed.

(** If [s1] and [s2] are bissimilar, then the semantics of [s2] contains [w1 s1,w2 s2]. *)
Lemma bissimilar_w s1 s2 :
  s1 ∼ s2 -> ⟦s2⟧ (𝐰 s1).
Proof.
  intros E;pose proof (w_path s1) as (s0&A&P).
  eapply bissimilar_path in P as (s3&P&E');eauto.
  exists s3;split;auto;apply (bissimilar_accepting E'),A.
Qed.


(** ** Similarity *)
(** Bissimilarity implies similarity. *)
Lemma bissimilar_similar s1 s2 : s1 ∼ s2 -> s1 ≺ s2.
Proof.
  revert s1 s2;cofix ch;intros s1 s2 E;apply prog2;intros α s3 st.
  inversion E as [? ? h];subst.
  apply (h α) in st as (s4&st&E').
  exists s4;split;auto.
Qed.
 
(** Similarity implies static equivalence. *)
Lemma similar_equiv_stacks s1 s2 : s1 ≺ s2 -> s1 == s2.
Proof.
  revert s2;induction s1 as [|(a,b)s1];intros s2 B;auto.
  - simpl;induction s2 as [|(a,b)s2];auto.
    assert (st : [] -- (close a,close a) ---> [])
      by (split;auto;left;repeat split;auto).
    inversion B as [? ? h];subst;clear B.
    apply h in st as (s1&(st&->)&B);clear h.
    destruct st as [(_&A)|(t1&t2&E&A)].
    + exfalso;rewrite absent_cons in A;tauto.
    + destruct t1 as [|x t1];simpl in *.
      * inversion E;subst;f_equal;auto.
        apply IHs2;revert B;simpl_beq;auto.
      * inversion E;subst;rewrite absent_cons in A;tauto.
  - inversion B as [? ? h];subst;clear B.
    assert (st : (a,b)::s1 -- (close a,close b) ---> s1)
      by (split;simpl;[right;exists [],s1;repeat split|simpl_beq];auto).
    apply h in st as (s3&st&B).
    apply IHs1 in B as ->.
    destruct st as (p&->);simpl;split;reflexivity||auto.
Qed.

(** ** Semantics *)
(** Bissimilarity implies semantic equivalence. *)
Lemma bissimilar_eq_sem s1 s2 : s1 ∼ s2 -> ⟦s1⟧ ≃ ⟦s2⟧.
Proof.
  intros E σ;split; intros (s3&A&P).
  - pose proof (bissimilar_path E P) as (s4&P'&E').
    exists s4;split;auto.
    apply (bissimilar_accepting E');auto.
  - symmetry in E;pose proof (bissimilar_path E P) as (s4&P'&E').
    exists s4;split;auto.
    apply (bissimilar_accepting E');auto.
Qed.

(** Semantic equivalence implies semantic inclusion. *)
Lemma eq_lang_incl_sem s1 s2 : ⟦s1⟧ ≃ ⟦s2⟧ -> ⟦s1⟧ ≲ ⟦s2⟧.
Proof. firstorder. Qed.

(** Semantic inclusion of [s1] in [s2] implies that [w1 s1,w2 s1] is in the semantics of [s2]. *)
Lemma incl_sem_w s1 s2 : ⟦s1⟧ ≲ ⟦s2⟧ -> ⟦s2⟧ (𝐰 s1).
Proof. intro h;apply h;apply w_path. Qed.


End s.