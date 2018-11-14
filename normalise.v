(** * RIS.normalise : normal form for words up-to alpha-equivalence. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export transducer representative traces alternate_eq.

Section s.
  (** * Adding natural numbers in the set of atoms *)
  (** Let us fix a set of atoms and an alphabet. *)
  Context {atom X : Set}{𝐀 : Atom atom} {𝐗 : Alphabet 𝐀 X}.

  (** ** Lifting variables *)
  (** We write [𝐎] for the set of representatives of [X], as constructed in [RIS.representative]. *)
  Definition 𝐎 := (@Repr _ X 𝐀).
  
  (** For technical reasons, in the following we need the set of representatives to be a nominal _set_ rather than a nominal _setoid_. This is due to our definition of an alphabet. Therefore, we assume we have a function [ϕ] from [𝐎] to some set [R], decidable and nominal over [pointer], such that: *)
  Parameter R : Set.
  Context {𝐑 : Alphabet 𝐏 R}.
  Parameter ϕ : 𝐎 -> R.
  (** - [ϕ] is injective up-to [≃]; *)
  Axiom ϕ_inj : forall x y : 𝐎, x ≃ y <-> ϕ x = ϕ y.
  (** - [ϕ] is equivariant; *)
  Axiom ϕ_equivariant : forall p x, ϕ (p⊙x) = p∙(ϕ x).
  (** - and [ϕ] preserves supports. *)
  Axiom ϕ_support : forall x, ⌊ϕ x⌋ ≈ ⌈x⌉.

  (** ** Lifting letters *)
  Notation " a ? " := (@bound atom a) (at level 20).

  (** We can build using [η, ϕ] and [!] a map [⦑ ⦒: letter 𝐀 𝐗 -> letter 𝐏 𝐑]. *)
  Definition repr_letter : @letter _ _ 𝐀 𝐗 -> @letter _ _ 𝐏 𝐑 :=
    fun l =>
      match l with
      | ⟨ a => ⟨ (a!)
      | a ⟩ => (a!) ⟩
      | var x => var (ϕ(η x))
      end.
  Notation " ⦑ l ⦒ " := (repr_letter l).
  
  (** The resulting function is injective and equivariant. *)
  Lemma repr_letter_injective : injective (fun l => ⦑l⦒).
  Proof.
    split;unfold repr_letter;intros [] [];firstorder (try discriminate).
    - inversion H;reflexivity.
    - inversion H;reflexivity.
    - inversion H;f_equal;apply η_inj,ϕ_inj;assumption.
  Qed.

  Lemma repr_letter_equivariant :
    forall (x : @letter _ _ 𝐀 𝐗) (π : @perm _ 𝐀), ⦅π⦆ ∙ ⦑ x ⦒ = ⦑ π∙x ⦒.
  Proof.
    intros [] π;simpl;unfold act at 1;simpl;f_equal.
    - rewrite lift_perm_invisible;reflexivity.
    - rewrite lift_perm_invisible;reflexivity.
    - rewrite <- ϕ_equivariant,<-ϕ_inj,η_equivariant;reflexivity.
  Qed.

  (** Furthermore, the support of [⦑x⦒] is the set of free names [a!] such that [a] is in the support of [x]. *)
  Lemma repr_letter_support : forall x, ⌊⦑x⦒⌋ ≈ map free ⌊x⌋.
  Proof.
    intros [];simpl.
    - reflexivity.  
    - reflexivity.
    - unfold support;simpl;rewrite ϕ_support,<-η_support;reflexivity.
  Qed.

  
  (** [⦑_⦒] preserves binding powers. *)
  Lemma repr_letter_binding a l : 𝗳 a l = 𝗳 (a!) ⦑l⦒.
  Proof.
    destruct l as [b|b|n];simpl.
    - unfold_eqX;try reflexivity.
      inversion E;tauto.
    - unfold_eqX;try reflexivity.
      inversion E;tauto.
    - case_in a ⌊n⌋;case_in (a!) ⌊ϕ(η n)⌋;try reflexivity.
      + exfalso;apply I0.
        rewrite ϕ_support,(η_support n).
        apply in_map_iff;exists a;tauto.
      + exfalso;apply I.
        rewrite ϕ_support,(η_support n) in I0.
        apply in_map_iff in I0 as (b&e&I0).
        inversion e;subst;tauto.
  Qed.
  
  (** ** Lifting words *)
  (** We write [W] for words built out of [⟨p], [p⟩] and [var r], were [p] ranges over pointers and [r] ranges over [R]. *)
  Notation W := (@word _ _ _ 𝐑).
  (** We may naturally lift [⦑ ⦒: X -> R] as [⟪ ⟫ : word 𝐀 𝐗 -> W]. *)
  Notation " ⟪ w ⟫ " := (map repr_letter w).

  (** [⟪_⟫] is injective and equivariant. *)
  Lemma repr_word_injective : injective (fun u => ⟪u⟫).
  Proof. split;intros ? ?;apply map_injective_injective,repr_letter_injective. Qed.

  Lemma repr_word_perm π u : ⟪π∙u⟫ = ⦅π⦆ ∙ ⟪u⟫.
  Proof.
    symmetry;unfold act,act_lists;rewrite map_map,map_map;apply map_ext.
    intro;apply repr_letter_equivariant.
  Qed.
  
  (** [⟪_⟫] behaves well with supports. *)
  Lemma repr_word_support a u : a ∈ ⌊u⌋ <-> a! ∈ ⌊⟪u⟫⌋.
  Proof.
    unfold support,SupportList;simpl_In.
    repeat rewrite flat_map_concat_map.
    rewrite map_map.
    repeat rewrite <- flat_map_concat_map.
    repeat rewrite in_flat_map.
    setoid_rewrite repr_letter_support;setoid_rewrite in_map_iff.
    firstorder.
    inversion H0;subst;eauto.
  Qed.

  (** [⟪_⟫] preserves binding powers. *)
  Corollary repr_word_binding a u : 𝗙 a u = 𝗙 (a!) ⟪u⟫.
  Proof.
    unfold 𝗙;f_equal.
    rewrite map_map;apply map_ext;apply repr_letter_binding.
  Qed.

  (** [⟪_⟫] is injective up-to alpha-equivalence. *)
  Theorem repr_word_equiv u v : u ≡ v <-> ⟪u⟫ ≡ ⟪v⟫.
  Proof.
    split.
    - intro E;induction E.
      + etransitivity;eauto.
      + reflexivity.
      + repeat rewrite map_app.
        apply αr,IHE.
      + simpl;apply αl,IHE.
      + simpl;repeat rewrite map_app.
        rewrite repr_word_perm;apply αα.
        * unfold fresh__α in *;rewrite <- repr_word_binding;apply H.
        * unfold balanced in *;rewrite <- repr_word_binding;apply H0.
    - revert u v;cut (forall u' v', u' ≡ v' -> forall u v, ⟪u⟫ = u' -> ⟪v⟫ = v' -> u ≡ v);
        [intros h u v E;apply (h _ _ E);reflexivity|].
      intros u' v' E.
      apply αequiv_to_αequiv2 in E;induction E;intros u' v' e1 e2.
      + apply map_eq_nil in e1 as ->.
        apply map_eq_nil in e2 as ->.
        reflexivity.
      + apply map_app_inverse in e1 as (u''&[|l'[|]]&->&e&->);inversion e;subst;clear e.
        apply map_app_inverse in e2 as (v''&[|l''[|]]&->&e&->);inversion e;subst;clear e.
        symmetry in H0;apply repr_letter_injective in H0;subst.
        apply αr,IHE;reflexivity.
      + apply map_app_inverse in e1 as (u1'&[|x w]&->&e1&->);[discriminate|].
        inversion e1 as [[e e1']];clear e1;symmetry in e1'.
        destruct x as [a'|a'|x];inversion e;subst;clear e.
        apply map_app_inverse in e1' as (u2'&[|x[|]]&->&e1'&->);[discriminate| |discriminate].
        inversion e1' as [[e1]];clear e1';symmetry in e1.
        destruct x as [b'|b'|x];inversion e1;subst;clear e1.
        apply map_app_inverse in e2 as (v1'&[|x w]&->&e2&->);[discriminate|].
        inversion e2 as [[e e2']];clear e2;symmetry in e2'.
        destruct x as [b'|b'|x];inversion e;subst;clear e.
        apply map_app_inverse in e2' as (v2'&[|x[|]]&->&e2'&->);[discriminate| |discriminate].
        inversion e2' as [[e2]];clear e2';symmetry in e2.
        destruct x as [c'|c'|x];inversion e2;subst;clear e2.
        destruct (exists_fresh (a'::b'::⌊u1'++u2'++v1'++v2'⌋)) as (c&F).
        repeat rewrite support_list_app in F;simpl_In in F.
        apply αequiv_alternate with (c0:=c).
        * apply αfresh_support;tauto.
        * apply αfresh_support;tauto.
        * unfold balanced;rewrite repr_word_binding;apply H. 
        * unfold balanced;rewrite repr_word_binding;apply H0.
        * apply (H2 (c!));clear H1 H2 H H0.
          -- simpl;intros [e|e];[inversion e;tauto|tauto].
          -- simpl;intros [e|e];[inversion e;tauto|tauto].
          -- repeat rewrite support_list_app;simpl_In.
             repeat rewrite <- repr_word_support.
             intros [e|[e|I]];apply F;[left|right;left|tauto];tauto.
          -- repeat rewrite map_app;simpl.
             rewrite repr_word_perm;simpl;reflexivity.
          -- repeat rewrite map_app;simpl.
             rewrite repr_word_perm;simpl;reflexivity.
  Qed.

  (** * Valid words  and dynamic sequences *)
  (** ** Validity *)
  (** *** Definition *)
  (** A word [u] is valid with respect to opening brackets if for every way of splitting [u] into [u1++⟨n?::u2], [n] is exactly the length of [u1] and there is a match bracket [?n⟩] in [u2]. *)
  Definition valid_open (u : W) :=
    forall u1 u2 n, u = u1++open(n?)::u2 ->
               n = ⎢u1⎥ /\ close(n?) ∈ u2.

  (** [u] is valid with respect to variable if for any decomposition [u=u1++var r::u2], and any bound number [n?∈⌊r⌋], there are match brackets [⟨n?] in [u1] and [?n⟩] in [u2]. *)
  Definition valid_var (u : W) :=
    forall u1 u2 r n, u = u1++var r::u2 -> n? ∈ ⌊var r⌋ ->
                 open(n?)∈ u1 /\ close (n?) ∈ u2.

  (** Finally, [u] is valid with respect to closing brackets if for every decomposition [u=u1++?n⟩::u2] there is a matching bracket [⟨?n] in [u1] and no other [n?⟩] anywhere in [u1++u2]. *)
  Definition valid_close (u : W) :=
    forall u1 u2 n, u = u1++close (n?)::u2 ->
               open (n?) ∈ u1 /\ ~ close (n?) ∈ (u1++u2).

  (** A word is valid if it is valid with respect to all three kinds of letters. *)
  Definition valid u := valid_open u /\ valid_var u /\ valid_close u.

  Remark is_valid_open u1 u2 n :
    valid (u1++open(n?)::u2) -> n = ⎢u1⎥ /\ close(n?) ∈ u2.
  Proof. intros (V&_);apply V;reflexivity. Qed.

  Remark is_valid_var u1 u2 x n :
    valid (u1++var x::u2) -> n? ∈ ⌊x⌋ -> open(n?)∈ u1 /\ close (n?) ∈ u2.
  Proof. intros (_&V&_);apply V;reflexivity. Qed.

  Remark is_valid_close u1 u2 n :
    valid(u1++close (n?)::u2) -> open (n?) ∈ u1 /\ ~ close (n?) ∈ (u1++u2).
  Proof. intros (_&_&V);apply V;reflexivity. Qed.

  (** *** Boolean predicate *)
  (** [test_var w1 w2 p] is true if [p] is a free name [a!] or a bound number [k?] such that [⟨k?] appears in [w1] and [k?⟩] appears in [w2]. *)
  Definition test_var w1 w2 (p : @pointer atom) :=
    match p with
    | a! => true
    | bound k => inb (open(k?)) w1 && inb (close(k?)) w2
    end.

  (** [test_valid_aux w1 w2] is the auxiliary function that we use to test validity of a string. Intuitively, when testing a word [u], we will successively test its suffixes [w2], while remembering the matching prefix [rev w1] to check for instance the presence of an opening bracket to the left of some closing bracket. *)
  Fixpoint test_valid_aux w1 w2 :=
    match w2 with
    | [] => true
    | open (bound k)::w2 => k =?= ⎢w1⎥ && inb (close (k?)) w2
                             && test_valid_aux (open(k?)::w1) w2
    | close (bound k)::w2 => (inb (open (k?)) w1)
                              && (negb (inb (close (k?)) (w1++w2)))
                              && test_valid_aux (close(k?)::w1) w2
    | var r::w2 => forallb (test_var w1 w2) ⌊r⌋
                    && test_valid_aux (var r::w1) w2
    | b::w2 => test_valid_aux (b::w1) w2
    end.

  Definition test_valid w := test_valid_aux [] w.

  (** We now prove that [test_valid w] correctly tests if [w] is valid. Before doing so, we establish the following two facts. *)
  (** If [test_valid_aux (rev u1++w) u2] is [false], then this value is propagated and therefore [test_valid_aux w (u1++u2)] is also [false]. *)
  Fact test_valid_aux_false_app w u1 u2 :
    test_valid_aux (rev u1++w) u2 = false -> test_valid_aux w (u1++u2) = false.
  Proof.
    revert u2 w;induction u1 as [|[[]|[]|]];intros u2 w;simpl.
    - tauto.
    - rewrite app_ass;simpl;intro h;apply IHu1 in h as ->;reflexivity.
    - rewrite app_ass;simpl;intro h;apply IHu1 in h as ->.
      apply andb_false_r.
    - rewrite app_ass;simpl;intro h;apply IHu1 in h as ->;reflexivity.
    - rewrite app_ass;simpl;intro h;apply IHu1 in h as ->.
      apply andb_false_r.
    - rewrite app_ass;simpl;intro h;apply IHu1 in h as ->.
      apply andb_false_r.
  Qed.

  (** [test_valid w] is [true] if and only if every test of suffixes of [w] is [true], i.e. : *)
  Fact test_valid_true w :
    test_valid w = true <-> forall u v, w = rev u ++ v -> test_valid_aux u v = true.
  Proof.
    split.
    + intros h u v -> ;case_eq (test_valid_aux u v);[reflexivity|].
      replace u with (rev(rev u)++[])
        by (rewrite rev_involutive,app_nil_r;reflexivity).
      intro F;apply test_valid_aux_false_app in F;unfold test_valid in h;rewrite h in F;discriminate.
    + intros h;unfold test_valid.
      apply (h [] w);reflexivity.
  Qed.

  (** We may now check that a word is valid if and only if [test_valid] of that word is [true]. *)
  Lemma test_valid_spec w : valid w <-> test_valid w = true.
  Proof.
    rewrite test_valid_true;split.
    - intros V u v ->;revert u V;induction v as [|[[]|[]|]];intros u;simpl.
      + reflexivity.
      + intros V;apply IHv;simpl.
        rewrite app_ass;apply V.
      + intro V;pose proof (is_valid_open V) as (->&I).
        rewrite rev_length in *.
        rewrite PeanoNat.Nat.eqb_refl.
        apply inb_spec in I as ->.
        simpl.
        apply IHv;simpl.
        rewrite app_ass;apply V.
      + intros V;apply IHv;simpl.
        rewrite app_ass;apply V.
      + intro V;pose proof (is_valid_close V) as (I1&I2).
        simpl_In in *;apply inb_spec in I1 as ->.
        rewrite <- in_app_iff in I2;apply inb_false in I2 as ->.
        simpl;apply IHv;simpl.
        rewrite app_ass;apply V.
      + intro V.
        replace (forallb _ _) with true.
        -- simpl;apply IHv;simpl.
           rewrite app_ass;apply V.
        -- symmetry;apply forallb_forall.
           intros [a|n] I;[reflexivity|simpl].
           apply (is_valid_var V) in I as (I1&I2);simpl_In in I1.
           apply inb_spec in I1 as ->.
           apply inb_spec in I2 as ->.
           reflexivity.
    - intros h;split;[|split].
      + intros w1 w2 n ->.
        cut (w1 ++ open (n?) :: w2 = rev (rev w1) ++ open (n?) :: w2);
          [|rewrite rev_involutive;reflexivity].
        intro e;apply h in e;simpl in e.
        repeat rewrite andb_true_iff in e.
        rewrite PeanoNat.Nat.eqb_eq,rev_length,inb_spec in e.
        tauto.
      + intros w1 w2 x n -> I.
        cut (w1 ++ var x :: w2 = rev (rev w1) ++ var x :: w2);
          [|rewrite rev_involutive;reflexivity].
        intro e;apply h in e;simpl in e.
        apply andb_true_iff in e as (e&_).
        rewrite forallb_forall in e;apply e in I;clear e.
        apply andb_true_iff in I as (e1&e2).
        rewrite inb_spec in e1,e2;simpl_In in e1.
        tauto.
      + intros w1 w2 n ->.
        cut (w1 ++ close (n?) :: w2 = rev (rev w1) ++ close (n?) :: w2);
          [|rewrite rev_involutive;reflexivity].
        intro e;apply h in e;simpl in e.
        repeat rewrite andb_true_iff in e.
        rewrite negb_true_iff,inb_spec,inb_false in e.
        simpl_In in *.
        tauto.
  Qed.

  (** *** Remarks about validity *)
  (** [⟪_⟫] always produces valid words. *)
  Proposition valid_repr_word u : valid ⟪u⟫.
  Proof.
    split;[|split].
    - intros w1 w2 n e.
      apply map_app_inverse in e as (m1&[|[] m2]&_&e&_);inversion e.
    - intros w1 w2 r n e I.
      apply map_app_inverse in e as (m1&[|[] m2]&_&e&_);inversion e as [[e1 e2]].
      rewrite e1 in I;apply (repr_letter_support (var x)),in_map_iff in I.
      destruct I as (?&?&_);discriminate.
    - intros w1 w2 n e.
      apply map_app_inverse in e as (m1&[|[] m2]&_&e&_);inversion e.
  Qed.

  (** If a bound number appears in the support of a valid word [w], then an opening bracket labelled with that number must be present in [w]. *)
  Lemma valid_support_open w n : valid w -> (n?) ∈ ⌊w⌋ -> open (n?) ∈ w.
  Proof.
    rewrite (In_support_list _ w);intros V ([[a|k]|[a|k]|]&I&e);
      try (destruct e as [e|e];inversion e;subst;clear e).
    - assumption.
    - apply in_split in I as (w1&w2&->).
      apply is_valid_close in V;simpl_In;tauto.
    - apply in_split in I as (w1&w2&->).
      apply (is_valid_var V) in e;simpl_In;tauto.
  Qed.

  (** We may strengthen this remark, by noticing that [n?] belongs to the support of a valid word [w] if and only if [w]'s [n]th letter is [⟨n?]. *)
  Lemma valid_support_open_explicit w n :
    valid w ->
    (n?) ∈ ⌊w⌋ <-> exists w1 w2, w = w1 ++ open(n?)::w2 /\ n = ⎢w1⎥.
  Proof.
    rewrite (In_support_list _ w).
    intro V;split.
    - intros ([[a|k]|[a|k]|]&I&e);
        try (destruct e as [e|e];inversion e;subst;clear e);
        apply in_split in I as (w1&w2&->).
      + exists w1,w2;split;[reflexivity|].
        apply is_valid_open in V;tauto.
      + destruct (is_valid_close V) as (I&_).
        apply in_split in I as (w1'&w2'&->).
        rewrite app_ass in *;simpl in *.
        exists w1',(w2'++close(n?)::w2);split;[reflexivity|].
        apply is_valid_open in V;tauto.
      + destruct (is_valid_var V e) as (I&_).
        apply in_split in I as (w1'&w2'&->).
        rewrite app_ass in *;simpl in *.
        exists w1',(w2'++var r::w2);split;[reflexivity|].
        apply is_valid_open in V;tauto.
    - intros (w1&w2&->&_).
      exists (open(n?));split;simpl_In;simpl ;tauto.
  Qed.

  (** The support of a valid word may only contain bound numbers smaller than its length. *)
  Lemma valid_bound_support_lt u n : valid u -> n? ∈ ⌊u⌋ -> n < ⎢u⎥.
  Proof.
    intro V;rewrite (In_support_list _ u);intros (x&I1&I2).
    apply in_split in I1 as (u1&u2&->).
    destruct x as [[a|k]|[a|k]|r];try (inversion I2 as [e|e];inversion e;subst;clear e).
    - destruct (is_valid_open V) as (->&_);solve_length.
    - destruct (is_valid_close V) as (I1&_).
      apply in_split in I1 as (u1'&u2'&->).
      rewrite app_ass in V;simpl in V.
      destruct (is_valid_open V) as (->&_);solve_length.
    - destruct (is_valid_var V I2) as (I1&_).
      apply in_split in I1 as (u1'&u2'&->).
      rewrite app_ass in V;simpl in V.
      destruct (is_valid_open V) as (->&_);solve_length.
  Qed.

  (** Numbers are always α-fresh in valid words. *)
  Lemma valid_bound_αfresh u n : valid u -> n? #α u.
  Proof.
    case_in (n?) ⌊u⌋;[|intros;apply αfresh_support;assumption].
    intro V;apply valid_support_open in I;[|assumption].
    apply in_split in I as (u1&u2'&->).
    destruct (is_valid_open V) as (->&I).
    apply in_split in I as (u2&u3&->).
    cut (⎢ u1 ⎥? ⋄ u2 /\ ⎢ u1 ⎥? #α u1 /\ ⎢ u1 ⎥? #α u3).
    - unfold fresh__α;simpl_binding.
      intros ((e1&e2)&->&->).
      revert e1 e2.
      destruct (𝗙 (_?) u2) as ((n&m)&p);simpl in *;simpl_binding.
      intros -> -> ;reflexivity.
    - split.
      + apply balanced_open_close.
        * intro I;apply in_split in I as (v1&v2&->).
          rewrite app_ass in V.
          rewrite app_comm_cons,<-app_ass in V;simpl in V.
          apply is_valid_open in V as (E&_);solve_length.
        * rewrite app_comm_cons,<-app_ass in V.
          apply is_valid_close in V as (_&I).
          simpl_In in I;tauto.
      + cut (⎢u1⎥? # u1++u3);
          rewrite support_list_app;simpl_In;[intro;split;apply αfresh_support;tauto|].
        intros [I|I].
        * revert V;set (w :=  ⟨ (⎢ u1 ⎥?) :: u2 ++ (⎢ u1 ⎥?) ⟩ :: u3);intro V.
          apply In_support_list in I as (x&I'&I);apply in_split in I' as (v1&v2&->).
          rewrite app_ass in V;simpl in V.
          destruct x as [[a|k]|[a|k]|r];try (inversion I as [e|e];inversion e;subst;clear e).
          -- apply is_valid_open in V as (->&_);solve_length.
          -- destruct (is_valid_close V) as (I1&_).
             apply in_split in I1 as (u1'&u2'&->).
             rewrite app_ass in V;simpl in V.
             destruct (is_valid_open V) as (->&_);solve_length.
          -- destruct (is_valid_var V I) as (I1&_).
             revert V;apply in_split in I1 as (u1'&u2'&e);rewrite e;intro V.
             rewrite app_ass in V;simpl in V.
             destruct (is_valid_open V) as (E&_);rewrite e in E;solve_length.
        * replace (cons(close(bound⎢u1⎥))) with (app[close(bound⎢u1⎥)]) in V by reflexivity.
          rewrite app_comm_cons,<-app_ass,<-app_ass in V.
          revert V;set (w := (u1++ ⟨ (⎢ u1 ⎥?) :: u2) ++ [(⎢ u1 ⎥?) ⟩]);intro V.
          apply In_support_list in I as (x&I'&I);apply in_split in I' as (v1&v2&->).
          rewrite <- app_ass in V;simpl in V.
          destruct x as [[a|k]|[a|k]|r];try (inversion I as [e|e];inversion e;subst;clear e).
          -- apply is_valid_open in V as (E&_);unfold w in E;solve_length.
          -- destruct (is_valid_close V) as (_&I1).
             apply I1;unfold w;simpl_In;tauto.
          -- destruct (is_valid_var V I) as (_&I2).
             replace ((w ++ v1) ++ var r :: v2)
               with ((u1 ++ ⟨ (⎢ u1 ⎥?) :: u2) ++ (⎢ u1 ⎥?) ⟩ :: v1 ++ var r :: v2)
               in V by (unfold w;repeat (rewrite app_ass;simpl);reflexivity).
             apply is_valid_close in V as (_&I');apply I'.
             simpl_In;tauto.
  Qed.        

  (** Validity may be characterised by the following property : [u] is valid if and only if it has no α-free numbers and opening brackets labelled with a number only appear at the correct position. *)
  Proposition alternate_validity u :
    valid u <-> (forall n, n? #α u) /\ (forall u1 u2 n, u = u1++open(n?)::u2 -> n = ⎢u1⎥).
  Proof.
    split.
    - intros V;split.
      + intros;apply valid_bound_αfresh,V.
      + intros ? ? ? ->;apply is_valid_open in V;tauto.
    - intros (h1&h2);split;[|split].
      + split.
        * apply (h2 u1 u2 n);assumption.
        * case_in (close (n?)) u2;[assumption|].
          exfalso;apply close_balanced_no_close in I.
          unfold close_balanced in I.
          pose proof (h1 n) as F;revert F;rewrite H;unfold fresh__α.
          simpl_binding.
          destruct (𝗙 (n?) u2) as ((p2&q2)&r2);simpl in *.
          destruct (𝗙 (n?) u1) as ((p1&q1)&r1);simpl.
          unfold d_binding in I;simpl in I;rewrite I.
          unfold prod_binding;simpl.
          destruct r1;simpl;intro E;inversion E;lia.
      + split.
        * case_in (open(n?)) u1;[assumption|].
          exfalso.
          apply open_balanced_no_open in I.
          unfold open_balanced in I.
          pose proof (h1 n) as F;revert F;rewrite H;unfold fresh__α.
          simpl_binding.
          destruct (𝗙 (n?) u2) as ((p2&q2)&r2);simpl in *.
          destruct (𝗙 (n?) u1) as ((p1&q1)&r1);simpl.
          unfold d_binding in I;simpl in I;rewrite I.
          unfold prod_binding;simpl.
          unfold support in H0;simpl in H0;apply inb_spec in H0 as ->.
          destruct p2;simpl;intro E;inversion E.
          -- destruct q1;discriminate.
          -- lia.
        * case_in (close(n?)) u2;[assumption|].
          exfalso.
          exfalso;apply close_balanced_no_close in I.
          unfold close_balanced in I.
          pose proof (h1 n) as F;revert F;rewrite H;unfold fresh__α.
          simpl_binding;simpl.
          unfold support in H0;simpl in H0;apply inb_spec in H0 as ->.
          destruct (𝗙 (n?) u2) as ((p2&q2)&r2);simpl in *.
          destruct (𝗙 (n?) u1) as ((p1&q1)&r1);simpl.
          unfold d_binding in I;simpl in I;rewrite I.
          unfold prod_binding;simpl.
          destruct r1;simpl;intro E;inversion E.
          -- destruct q1;discriminate.
          -- lia.
      + intros u1 u2 n E.
        * case_in (open(n?)) u1.
          -- split;[assumption|];apply in_split in I as (v1&v2&->).
             rewrite app_ass in E;pose proof (h2 _ _ _ E) as En.
             case_in (open(n?)) (v1++v2++u2).
             ++ exfalso;simpl_In in I;repeat destruct I as [I|I];apply in_split in I as (w1&w2&->).
                ** rewrite app_ass in E;pose proof (h2 _ _ _ E) as Em.
                   solve_length.
                ** rewrite (h2 (v1++open(n?)::w1) (w2++close(n?)::u2) n) in En
                    by (rewrite E;repeat (rewrite app_ass;simpl);reflexivity).
                   solve_length.
                ** rewrite app_comm_cons,<- app_ass,<- app_ass in E ;pose proof (h2 _ _ _ E) as Em.
                   solve_length.
             ++ simpl_In in I.
                assert (~open (n ?) ∈ v1 /\ ~ open(n ?) ∈ v2 /\ ~open (n ?) ∈ u2)
                  as (B1&B2&B3)
                    by tauto.
                apply open_balanced_no_open in B1.
                apply open_balanced_no_open in B2.
                apply open_balanced_no_open in B3.
                unfold open_balanced in *.
                assert (B:d_binding (𝗙 (n?) u) = 0) by (rewrite (h1 n);reflexivity).
                simpl_In;intros In.
                revert B;rewrite E;simpl_binding;simpl.
                rewrite B2,B1;simpl;simpl_nat.
                repeat destruct In as [In|In];try discriminate;
                  apply in_split in In as (w1&w2&->);simpl_binding;simpl_In in I;simpl;
                    repeat rewrite open_balanced_no_open by tauto;simpl;lia.
          -- exfalso.
             apply open_balanced_no_open in I.
             unfold open_balanced in I.
             pose proof (h1 n) as F;revert F;rewrite E;unfold fresh__α.
             simpl_binding.
             destruct (𝗙 (n?) u2) as ((p2&q2)&r2);simpl in *.
             destruct (𝗙 (n?) u1) as ((p1&q1)&r1);simpl.
             unfold d_binding in I;simpl in I;rewrite I.
             unfold prod_binding;simpl.
             destruct p2;simpl;intro e;inversion e;lia.
  Qed.
      
          
  (** ** Defects *)
  (** [w] has a defect if it can be decomposed as [w1++⟨a!::w2++a!⟩++w3]. *)
  Definition match_defect w :=
    exists w1 w2 w3 a, w = w1 ++ ⟨(a!) ::w2++(a!)⟩::w3.

  (** [match_defectb a w] checks if [w] has a decomposition [w1++a!⟩::w2] such that [w1] does not contain the letter [⟨a!]. *)
  Fixpoint match_defectb a w :=
    match w with
    | [] => false
    | l::w => (l=?=close(a!))
             || ((negb (l=?= open (a!)))
                  && match_defectb a w)
    end.

  Remark match_defectb_spec a w :
    match_defectb a w = true <-> exists w1 w2, w = w1 ++ close (a!) :: w2
                                        /\ ~ open (a!) ∈ w1
                                        /\ ~ close (a!) ∈ w1.
  Proof.
    induction w as [|l w];simpl.
    - split;[discriminate|intros (?&?&?&_);simpl_words].
    - replace (eq_letter l) with (eqX l) by reflexivity;unfold_eqX;simpl;try discriminate.
      + split;[intros _|tauto].
        exists [],w;simpl;tauto.
      + split;[discriminate|].
        intros ([|l' w1]&w2&e&I1&I2);inversion e as [[e1 e2]].
        exfalso;subst;apply I1;now left.
      + rewrite IHw;clear IHw;split;intros (w1&w2&e&E).
        * subst;exists (l::w1),w2;simpl;split;[reflexivity|tauto].
        * destruct w1 as [|c w1];inversion e as [[e1 e2]];subst;[tauto|].
          exists w1,w2;simpl in *;tauto.
  Qed.

  (** With the predicate [match_defectb], we can reformulate [match_defect] as follows. *)
  Lemma match_defect_match_defectb w :
    match_defect w <-> exists w1 w2 a, w = w1 ++ open (a!) :: w2
                                /\ match_defectb a w2 = true.
  Proof.
    split.
    - induction w as [|l w];unfold match_defect.
      + intros (w1&w2&w3&a&e);simpl_words.
      + intros ([|b w1]&w2&w3&a&e);inversion e as [[e1 e2]];clear e;subst.
        * case_in (open(a!)) w2.
          -- cut (match_defect (w2++close (a!) ::w3)).
             ++ intro h;apply IHw in h as (v1&v2&b&e&eb).
                exists (open(a!)::v1),v2,b.
                rewrite e;simpl;tauto.
             ++ apply in_split in I as (v1&v2&->);exists v1,v2,w3,a;rewrite app_ass;reflexivity.
          -- case_in (close(a!)) w2.
             ++ apply decomposition in I0 as (v1&v2&->&I').
                exists [],(v1++close(a!)::v2++close(a!)::w3),a.
                simpl;repeat rewrite app_ass;simpl;split;auto.
                apply match_defectb_spec.
                exists v1,(v2++close(a!)::w3);simpl_In in *;tauto.
             ++ exists [],(w2++(close(a!))::w3),a;simpl;split;[reflexivity|].
                apply match_defectb_spec;exists w2,w3;tauto.
        * case_in (open(a!)) w2.
          -- cut (match_defect (w1 ++ open (a!) ::w2++close (a!) ::w3)).
             ++ intro h;apply IHw in h as (v1&v2&c&->&eb).
                exists (b::v1),v2,c;simpl;tauto.
             ++ apply in_split in I as (v1&v2&->).
                exists (w1++open(a!)::v1),v2,w3,a;repeat rewrite app_ass;reflexivity.
          -- case_in (close(a!)) w2.
             ++ apply decomposition in I0 as (v1&v2&->&I').
                exists (b::w1),(v1++close(a!)::v2++close(a!)::w3),a.
                simpl;repeat rewrite app_ass;simpl;split;auto.
                apply match_defectb_spec.
                exists v1,(v2++close(a!)::w3);simpl_In in *;tauto.
             ++ exists (b::w1),(w2++(close(a!))::w3),a;simpl;split;[reflexivity|].
                apply match_defectb_spec;exists w2,w3;tauto.
    - intros (w1&w2'&a&->&E).
      apply match_defectb_spec in E as (w2&w3&->&_).
      exists w1,w2,w3,a;reflexivity.
  Qed.

  (** [w] has a defect at [n] means that [w] can be decomposed as [w1++⟨a!::w2], with [w1] having length [n] and [match_defectb a w2] holds. *)
  Definition match_defect_at_n w n :=
    exists w1 w2 a, ⎢w1⎥ = n /\ w = w1++open (a!)::w2 /\ match_defectb a w2 = true.

  (** Notice that [w] has a defect if and only if it has a defect at some [n]. *)
  Remark match_defect_at_n_spec (w : @word _ _ _ 𝐑) :
    match_defect w <-> exists n, match_defect_at_n w n.
  Proof.
    rewrite match_defect_match_defectb.
    split.
    - intros (w1&w2&a&->&m).
      exists ⎢w1⎥,w1,w2,a;tauto.
    - intros (n&w1&w2&a&_&->&h).
      exists w1,w2,a;tauto.
  Qed.

  Remark match_defect_at_Sn l w n :
    match_defect_at_n (l::w) (S n) <-> match_defect_at_n w n.
  Proof.
    split.
    - intros ([|l' w1]&w2&a&len&e&m);[discriminate|inversion e;subst].
      exists w1,w2,a;split;[solve_length|tauto].
    - intros (w1&w2&a&len&->&m).
      exists (l::w1),w2,a;simpl;split;[solve_length|tauto].
  Qed.
  
  (** [first_defect w n] holds when [w] has a defect at [n] and [n] is the minimal such number. *)
  Definition first_defect w n :=
    match_defect_at_n w n /\ forall k, match_defect_at_n w k -> n <= k.

  Remark first_defect_Sn l w n : first_defect (l::w) (S n) -> first_defect w n.
  Proof.
    intros (h1&h2);split.
    - apply match_defect_at_Sn in h1;assumption.
    - intros k hk.
      rewrite <- (match_defect_at_Sn l) in hk.
      apply h2 in hk;lia.
  Qed.

  (** We may also check that if [w] has a defect then it has a first defect. *)
  Remark match_defect_first_defect (w : @word _ _ _ 𝐑) :
    match_defect w -> exists n, first_defect w n.
  Proof.
    induction w as [|l w];simpl.
    - intros (?&?&?&?&?);simpl_words.
    - cut ((exists a, l = open(a!) /\ match_defectb a w = true)
           \/ (~match_defect_at_n (l::w) 0)).
      + intros [(a&->&m)|m].
        * intros _;exists 0;split.
          -- exists [],w,a;simpl;split;tauto.
          -- intros k;lia.
        * rewrite match_defect_at_n_spec.
          intros ([|n]&h);[tauto|].
          rewrite match_defect_at_Sn in h.
          destruct IHw as (N&IH).
          -- apply match_defect_at_n_spec;exists n;assumption.
          -- exists (S N);split.
             ++ rewrite match_defect_at_Sn;apply IH.
             ++ intros [|k];[tauto|].
                rewrite match_defect_at_Sn;intro F;apply IH in F;lia.
      + destruct l as [[a|n]| |].
        * case_eq (match_defectb a w).
          -- intro m;left;exists a;tauto.
          -- intro m;right;intros ([]&w2&b&len&e&h);[|discriminate].
             inversion e;subst;rewrite m in h;discriminate.
        * right;intros ([]&w2&b&len&e&h);discriminate.
        * right;intros ([]&w2&b&len&e&h);discriminate.
        * right;intros ([]&w2&b&len&e&h);discriminate.
  Qed.

  (** [defect_count] will be used later on to guess the number of rewrite steps needed to put a word in normal form. It counts the number of decompositions [w1++⟨a!::w2] such that [a!] is not open-balanced in [w2]. *)
  Fixpoint defect_count w :=
    match w with
    | [] => 0
    | open (a!)::w =>
      if d_binding (𝗙 (a!) w) =?= 0
      then defect_count w
      else S (defect_count w) 
    | b::w => defect_count w
    end.

  (** Notice that the following case distinction holds: *)
  Remark defect_count_disj b w :
    (exists a, b = open(a!))
    \/ ((forall a, b <> open(a!))/\ defect_count (b::w) = defect_count w).
  Proof.
    destruct b as [[a|]|[]|];(left;exists a;reflexivity)||(right;split;[intro;discriminate|reflexivity]).
  Qed.

  (** In particular, having a positive [defect_count] is equivalent to having a defect. *)
  Lemma defect_count_spec w : match_defect w <-> 0 < defect_count w.
  Proof.
    rewrite match_defect_match_defectb.
    induction w as [|b w].
    - simpl;split;[|lia].
      intros (?&?&?&?&?);simpl_words.
    - destruct (defect_count_disj b w) as [(a&->)|(f&->)].
      + simpl;case_eq (d_binding (𝗙 (a!) w));[|intro k];intro e;simpl.
        * rewrite <- IHw;clear IHw;split.
          -- intros ([|l w1]&w2&b&e'&h);inversion e';subst.
             ++ exfalso;clear e'.
                apply match_defectb_spec in h as (u1&u2&->&I1&I2).
                revert e;simpl_binding.
                destruct (balanced_open_close I1 I2) as (->&->);simpl.
                lia.
             ++ exists w1,w2,b;tauto.
          -- intros (w1&w2&b&->&e');exists (open(a!)::w1),w2,b;tauto.
        * split;[lia|intros _;clear IHw].
          cut (d_binding (𝗙 (a!) w) <> 0);[clear e k|lia].
          induction w as [|[[b|n]| |] w];simpl_binding;simpl;simpl_eqX;unfold_eqX;simpl_binding.
          intro e;exfalso;apply e;reflexivity.
          -- intro e;destruct IHw as (w1&w2&c&e'&m);simpl_binding in *;[lia|].
             destruct w1;inversion e';subst.
             ++ exists [open(free c)],w2,c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
             ++ exists (open(free b)::open(free b)::w1),w2,c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
          -- intro e;destruct IHw as (w1&w2&c&e'&m);simpl_binding in *;[lia|].
             destruct w1;inversion e';subst.
             ++ exists [],(open(free b)::w2),c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
             ++ exists (open(a!)::open(free b)::w1),w2,c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
          -- intro e;destruct IHw as (w1&w2&c&e'&m);simpl_binding in *;[lia|].
             destruct w1;inversion e';subst.
             ++ exists [],(open(n?)::w2),c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
             ++ exists (open(a!)::open(n?)::w1),w2,c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
          -- intros _;exists [],(close p::w),a;subst;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
          -- intro e;destruct IHw as (w1&w2&c&e'&m);simpl_binding in *;[lia|].
             destruct w1;inversion e';subst.
             ++ exists [],(close p::w2),c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
             ++ exists (open(a!)::close p::w1),w2,c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
          -- intro e;destruct IHw as (w1&w2&c&e'&m);simpl_binding in *;[lia|].
             destruct w1;inversion e';subst.
             ++ exists [],(var r::w2),c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
             ++ exists (open(a!)::var r::w1),w2,c;simpl;unfold eq_letter;simpl_eqX;simpl;tauto.
      + rewrite <- IHw;clear IHw;split.
        * intros ([|l w1]&w2&c&e'&h);inversion e';subst.
          -- exfalso;apply (f c);reflexivity.
          -- exists w1,w2,c;tauto.
        * intros (w1&w2&c&->&e');exists (b::w1),w2,c;tauto.
  Qed.

  (** The following case distinction will be useful: either [w] has no defect, otherwise it may be decomposed as [w1++open(a!)::w2++close(a!)::w3] such that the first defect of [w] is at [⎢w1⎥] and [w2] does not contain a bracket labelled with [a!]. *)
  Remark case_defect w :
    {~ match_defect w} + {exists w1 w2 w3 a, w = w1++open(a!)::w2++close(a!)::w3
                                        /\ first_defect w ⎢w1⎥
                                        /\ ~ open (a!) ∈ w2
                                        /\ ~ close (a!) ∈ w2}.
  Proof.
    destruct_ltb 0 (defect_count w).
    - left;rewrite defect_count_spec;lia.
    - right;rewrite <- defect_count_spec in L.
      apply match_defect_first_defect in L as (n&f).
      pose proof f as ((w1&w'&a&<-&->&e)&_).
      apply match_defectb_spec in e as (w2&w3&->&I1&I2).
      exists w1,w2,w3,a;tauto.
  Qed.

  (** ** Dynamic sequences *)
  (** Dynamic sequences will be our normal forms. A _dynamic sequence_ is a valid word that has no defect. *)
  Definition dynamic_sequence w := valid w /\ ~ match_defect w.

  (** This property is decidable. *)
  Definition test_dyn_seq (w : @word _ _ _ 𝐑) :=
    test_valid w && defect_count w =?= 0.

  Lemma test_dyn_seq_spec w : test_dyn_seq w = true <-> dynamic_sequence w.
  Proof.
    unfold dynamic_sequence,test_dyn_seq.
    rewrite andb_true_iff,test_valid_spec.
    rewrite defect_count_spec,eqX_correct.
    split;(split;[tauto|lia]).
  Qed.
  
  (** Dynamic sequences enjoy the following property: two dyn. seq. [u,v] are alpha-equivalent if and only if they are equal. *)
  Theorem equiv_dynamic_sequence_eq u v :
    dynamic_sequence u -> dynamic_sequence v -> u ≡ v -> u = v.
  Proof.
    rewrite (completeness u v).
    rewrite <- (app_nil_r v) at 1.
    generalize dependent (@nil (@letter _ _ _ 𝐑));intro v2.
    rewrite <- (app_nil_r u) at 1.
    generalize dependent (@nil (@letter _ _ _ 𝐑));intro u2.
    revert u v u2 v2;intros u1;induction u1 as [|lu u1] using rev_induction;
      intros v1' u2 v2 Du Dv (s&P&Acc).
    - inversion P;subst;reflexivity.
    - apply path_letter in P as (v1&lv&s'&->&P&hs).
      rewrite app_ass in Du,Dv.
      assert (IH : prj1 s' = prj2 s' -> u1 = v1)
        by (intro Acc';apply (IHu1 v1 (lu::u2) (lv::v2) Du Dv);exists s';tauto);clear IHu1.
      unfold step in hs;destruct lu as [a|a|x];destruct lv as [b|b|y];try tauto.
      + subst;inversion Acc as [[e1 e2]];subst.
        rewrite IH;tauto.
      + destruct hs as ([(->&I)|(s1&s2&->&I)]&->).
        * rewrite rmfst_absent in Acc by assumption.
          rewrite IH by assumption;reflexivity.
        * rewrite rmfst_present in Acc by assumption.
          pose proof (path_stack_decompose_aux P) as (u1'&u2'&v1'&v2'&->&->&len&_).
          replace a with (⎢u1'⎥?) in *;[replace b with (⎢v1'⎥?) in *|].
          -- rewrite IH,len;[reflexivity|].
             repeat rewrite map_app;simpl.
             repeat rewrite map_app in Acc.
             apply length_app in Acc as (->&->);[ |solve_length].
             rewrite len;reflexivity.
          -- revert Dv;clear.
             rewrite app_ass;simpl; destruct b as [a|k].
             ++ intros (_&F);exfalso;apply F.
                exists v1',v2',v2,a;reflexivity.
             ++ intros (V&_);destruct_eqX k ⎢v1'⎥;[reflexivity|].
                exfalso;apply is_valid_open in V as (->&_);tauto.
          -- revert Du;clear.
             rewrite app_ass;simpl; destruct a as [b|k].
             ++ intros (_&F);exfalso;apply F.
                exists u1',u2',u2,b;reflexivity.
             ++ intros (V&_);destruct_eqX k ⎢u1'⎥;[reflexivity|].
                exfalso;apply is_valid_open in V as (->&_);tauto.
      + destruct hs as (->&(p&->&hp)).
        rewrite IH by assumption.
        f_equal;f_equal;f_equal.
        symmetry;apply action_invariant,map_eq_id.
        intros q Iq.
        rewrite <- paired_Accepting by eauto.
        apply hp;assumption.
  Qed.

  (** * Normalisation *)
  (** ** Rewrite steps *)

  Inductive red_def : relation W :=
  | step u v w a : ~ open (a!) ∈ v -> ~ close (a!) ∈ v ->
                   red_def (u++open (a!)::v++close (a!)::w)
                           (u++open (⎢u⎥?)::([(a!,⎢u⎥?)]∙v)++close(⎢u⎥?)::w).

  Lemma red_def_valid u v : valid u -> red_def u v -> valid v.
  Proof.
    intros V R;inversion R as [w1 w2 w3 a I1 I2];subst;clear R.
    split;[|split];intros u1 u2;[|intro x|];intro n;intro e;levi e;clear e;
      try (inversion E0 as [[e1 e2]];clear E0);subst.
    - simpl_In;tauto.
    - rewrite app_ass in V;simpl in V;apply is_valid_open in V;simpl_In in *.
      rewrite In_act_lists;simpl_In.
      repeat (unfold act;simpl);simpl_eqX;unfold_eqX.
      + exfalso;destruct V as (->&_);inversion E;solve_length.
      + clear N N0;firstorder discriminate.
    - levi e2;inversion E0;subst;clear e2 E0.
      + revert E.
        rewrite <- (act_bij ([(a!,bound⎢w1⎥)]∗)),
        act_pinv_p,act_lists_app,act_lists_cons.
        unfold act at 2;simpl;unfold act at 2;simpl.
        simpl_eqX;unfold_eqX;intros ->.
        * exfalso;apply I1;simpl_In;tauto.
        * destruct V as (V&_).
          destruct (V (w1++open(a!)::[(a!, ⎢ w1 ⎥?)] ∙ w)
                      ([(a!, ⎢ w1 ⎥?)] ∙ w0 ++ close (a!) :: w3) n) as (e&I).
          -- repeat (rewrite app_ass;simpl);reflexivity.
          -- split;[rewrite e;solve_length|].
             revert N N0 I;clear.
             simpl_In;rewrite In_act_lists.
             repeat (unfold act;simpl);simpl_eqX.
             firstorder;discriminate.
      + destruct V as (V&_).
        destruct (V (w1++open(a!)::w2++ close (a!)::w0) u2 n) as (e&I).
        * repeat (rewrite app_ass;simpl);reflexivity.
        * split;[rewrite e;solve_length|assumption].
    - intro In;rewrite app_ass in V;simpl in V;apply (is_valid_var V) in In;simpl_In in *.
      rewrite In_act_lists;simpl_In.
      repeat (unfold act;simpl);simpl_eqX;unfold_eqX.
      clear V I1 I2 N N0;firstorder discriminate.
    - levi e2 ;inversion E0;subst;clear e2 E0.
      + revert E.
        rewrite <- (act_bij ([(a!,bound⎢w1⎥)]∗)),
        act_pinv_p,act_lists_app,act_lists_cons;intros ->.
        destruct_eqX (n?) (⎢w1⎥?);[simpl_In;tauto|].
        intro In.
        pose proof V as (_&h&_).
        destruct (h (w1++open(a!)::[(a!, ⎢ w1 ⎥?)] ∙ w)
                    ([(a!, ⎢ w1 ⎥?)] ∙ w0 ++ close (a!) :: w3)
                    ([(a!, ⎢ w1 ⎥?)] ∙ x) n) as (I1'&I2');clear h.
        * repeat (rewrite app_ass;simpl);reflexivity.
        * unfold support;simpl.
          rewrite support_action,In_act_lists.
          unfold act;simpl;simpl_eqX;assumption.
        * revert I1' I2';simpl_In.
          repeat rewrite In_act_lists.
          repeat (unfold act;simpl);simpl_eqX.
          clear;firstorder discriminate.
      + destruct V as (_&V&_);intro I.
        destruct (V (w1++open(a!)::w2++ close (a!)::w0) u2 x n) as (I1'&I2').
        * repeat (rewrite app_ass;simpl);reflexivity.
        * assumption.
        * revert I1' I2';simpl_In.
          repeat rewrite In_act_lists.
          repeat (unfold act;simpl);simpl_eqX.
          clear;firstorder discriminate.
    - rewrite app_ass in V;simpl in V;pose proof (is_valid_close V) as hyp;simpl_In in *.
      rewrite In_act_lists;simpl_In.
      repeat (unfold act;simpl);simpl_eqX;unfold_eqX.
      + exfalso;destruct hyp as (hyp&_);revert V.
        apply in_split in hyp as (v1&v2&e1);rewrite e1;rewrite app_ass;simpl.
        intros V;apply is_valid_open in V as (e2&_).
        rewrite e1 in e2;solve_length.
      + clear V;split;[tauto|].
        intro I;apply hyp;clear hyp.
        repeat destruct I as [I|I];try discriminate||tauto.
        exfalso;inversion I as [e].
        rewrite e in N0 at 1;apply N0;reflexivity.
    - levi e2 ;inversion E0;subst;clear e2 E0.
      + simpl_In;split;[tauto|].
        repeat rewrite In_act_lists.
        repeat (unfold act;simpl);simpl_eqX.
        cut (⎢w1⎥? # w1 ++ ⟨ (a !) :: w2 ++ (a !) ⟩ :: u2).
        * repeat rewrite support_list_app||rewrite support_list_cons;simpl_In;simpl.
          revert I1 I2;clear.
          intros I1 I2 F [[h|[h|h]]|h].
          -- apply F;left;apply In_support_list;exists (close(⎢w1⎥?));simpl;tauto.
          -- discriminate.
          -- tauto.
          -- apply F;repeat right;apply In_support_list;exists (close(⎢w1⎥?));simpl;tauto.   
        * rewrite (valid_support_open_explicit ⎢w1⎥ V).
          intros (?&?&e1&e2).
          apply length_app in e1 as (_&e1);[discriminate|assumption].
      + revert E.
        rewrite <- (act_bij ([(a!,bound⎢w1⎥)]∗)),
        act_pinv_p,act_lists_app,act_lists_cons.
        unfold act at 2;simpl;unfold act at 2;simpl.
        simpl_eqX;unfold_eqX;intros ->.
        * exfalso;apply I2;simpl_In;tauto.
        * destruct V as (_&_&V).
          destruct (V (w1++open(a!)::[(a!, ⎢ w1 ⎥?)] ∙ w)
                      ([(a!, ⎢ w1 ⎥?)] ∙ w0 ++ close (a!) :: w3) n)
            as (I1'&I2').
          -- repeat (rewrite app_ass;simpl);reflexivity.
          -- revert N N0 I1' I2';clear;intros N1 N2.
             simpl_In;repeat rewrite In_act_lists.
             repeat (unfold act;simpl);simpl_eqX.
             intros I1' I2';split;[clear I2';firstorder discriminate|].
             clear I1';intros I;apply I2';clear I2'.
             repeat destruct I as [I|I];try tauto||discriminate.
             inversion I;subst;tauto.
      + repeat rewrite app_comm_cons in V||rewrite <- app_ass in V.
        destruct (is_valid_close V) as (I1'&I2').
        revert I1' I2';simpl_In.
        repeat rewrite In_act_lists.
        repeat (unfold act;simpl);simpl_eqX;unfold_eqX.
        * exfalso;inversion E;subst;clear E N.
          cut (⎢w1⎥? ∈ ⌊((w1 ++ ⟨ (a !) :: w2) ++ (a !) ⟩ :: w0) ++ close(⎢ w1 ⎥ ?) :: u2⌋).
          -- rewrite valid_support_open_explicit by assumption.
             intros (?&?&e1&e2).
             repeat (rewrite app_ass in e1;simpl in e1).
             apply length_app in e1 as (_&e1);[discriminate|assumption].
          -- apply In_support_list;exists (close (⎢ w1 ⎥?));simpl_In;simpl;tauto.
        * intros I1' I2';split;[clear I2';firstorder discriminate|].
          clear I1';intros I;apply I2';clear I2'.
          repeat destruct I as [I|I];try tauto||discriminate.
          inversion I;subst;tauto.
  Qed.

  Lemma red_def_defect_count u v :
    valid u -> red_def u v ->  defect_count v = defect_count u - 1.
  Proof.
    intros V R;inversion R as [w1 w2 w3 a I1 I2];subst;clear R.
    assert (N: ⎢w1⎥? # w1 ++ ⟨ (a !) :: w2 ++ (a !) ⟩ :: w3)
      by (rewrite valid_support_open_explicit by assumption;intros (?&?&e1&e2);
          apply length_app in e1 as (_&e1);[discriminate|assumption]).
    repeat (rewrite support_list_app in N) || rewrite support_list_cons in N;simpl_In.
    clear V;revert N;remember ⎢w1⎥ as k;clear Heqk.
    intros N;induction w1 as [|l w1].
    - simpl_binding.
      destruct (balanced_open_close I1 I2) as (->&->);simpl.
      rewrite <- Minus.minus_n_O.
      induction w2 as [|l w2];[reflexivity|].
      rewrite act_lists_cons,<-app_comm_cons,<-app_comm_cons.
      rewrite support_list_cons in N;simpl in I1,I2;simpl_In in N.
      destruct (defect_count_disj l (w2++close(a!)::w3)) as [(b&->)|(D&->)].
      + unfold act at 1;simpl.
        unfold act at 1;simpl;simpl_eqX;unfold_eqX.
        replace (d_binding (𝗙 (free b) ([(a!, k?)] ∙ w2 ++ close(k?) :: w3)))
          with  (d_binding (𝗙 (free b) (w2 ++ close(a!) :: w3))).
        * rewrite IHw2;[reflexivity|tauto|tauto|simpl_In;tauto].
        * simpl_binding;rewrite (𝗙_perm _ (free b) w2).
          simpl;unfold act;simpl;simpl_eqX;reflexivity.
      + destruct (defect_count_disj ([(a!, k?)] ∙ l)
                                    ([(a!, k?)] ∙ w2++close(k?)::w3))
          as [(b&F)|(_&->)].
        * exfalso;clear IHw2.
          revert F;destruct l as [[c|n]| |].
          -- intros _;apply (D c);reflexivity.
          -- repeat (unfold act;simpl);simpl_eqX;unfold_eqX.
             ++ intros _;apply N;simpl;tauto.
             ++ discriminate.
          -- repeat (unfold act;simpl);simpl_eqX;discriminate.
          -- repeat (unfold act;simpl);simpl_eqX;discriminate.
        * apply IHw2;simpl_In;tauto.
    - rewrite <-app_comm_cons,<-app_comm_cons.
      rewrite support_list_cons in N;simpl_In in N;simpl in N.
      destruct (defect_count_disj l (w1++open(a!)::w2++close(a!)::w3)) as [(b&->)|(D&->)].
      + simpl.
        replace (d_binding (𝗙 (free b) (w1++open(k?)::[(a!,k?)]∙w2++close(k?)::w3)))
          with  (d_binding (𝗙 (free b) (w1++open(a!)::w2 ++ close(a!) :: w3))).
        * rewrite IHw1.
          -- destruct (d_binding (𝗙 (free b) (w1 ++ open (a!) :: w2 ++ close(a!) :: w3)));
               simpl.
             ++ reflexivity.
             ++ cut (0<defect_count (w1 ++ open(a!) :: w2 ++ close(a!) :: w3));[lia|].
                apply defect_count_spec;exists w1,w2,w3,a;reflexivity.
          -- clear IHw1;simpl_In;simpl;firstorder discriminate.
        * simpl_binding;rewrite (𝗙_perm _ (free b) w2).
          simpl;unfold act;simpl;simpl_eqX;unfold_eqX.
          -- destruct(balanced_open_close I1 I2) as (->&->).
             assert (k? #α w2) as ->;[|simpl;lia].
             apply αfresh_support;simpl_In in N;tauto.
          -- lia.
      + destruct (defect_count_disj l (w1++open(k?)::[(a!,k?)]∙w2++close(k?)::w3))
          as [(b&->)|(_&->)].
        * exfalso;apply (D b);reflexivity.
        * apply IHw1;simpl_In;simpl;firstorder discriminate.
  Qed.

  Lemma red_def_equiv u v :
    valid u -> red_def u v ->  u ≡ v.
  Proof.
    intros V R;inversion R as [w1 w2 w3 a I1 I2];subst;clear R.
    apply αequiv_app_left.
    replace (cons(close(⎢w1⎥?))) with (app[close(bound⎢w1⎥)]) by reflexivity.
    rewrite app_comm_cons,<-app_ass.
    replace (cons(close(a!))) with (app[close(a!)]) by reflexivity.
    rewrite app_comm_cons,<-app_ass.
    apply αequiv_app_right;simpl.
    apply αα.
    - apply αfresh_support.
      assert (I3:~⎢w1⎥?∈ ⌊w1 ++ ⟨ (a !) :: w2 ++ (a !) ⟩ :: w3⌋)
        by (rewrite valid_support_open_explicit by assumption;intros (?&?&e1&e2);
            apply length_app in e1 as (_&e1);[discriminate|assumption]).
      revert I3.
      repeat (rewrite support_list_cons||setoid_rewrite support_list_app;simpl_In;simpl).
      tauto.
    - clear V;split.
      + clear I2;induction w2;simpl_binding.
        * reflexivity.
        * simpl_In in I1;rewrite IHw2 by tauto.
          destruct a0 as [[]| |];simpl;simpl_eqX;unfold_eqX;try reflexivity.
      + clear I1;induction w2;simpl_binding.
        * reflexivity.
        * simpl_In in I2;rewrite IHw2 by tauto.
          destruct a0 as [[]| |];simpl;simpl_eqX;unfold_eqX;try reflexivity.
  Qed.

  (** [hide a n w] goes through the word [w], applying to each letter the transposition [(a!,n?)] until the letter [a!⟩] is found, after which the procedure stops. *)
  Fixpoint hide a n w :=
    match w with
    | [] => []
    | b::w => if close (a!) =?= b
             then ([(a!,n?)]∙b)::w
             else ([(a!,n?)]∙b)::(hide a n w)
    end.

  (** More directly, if [w1++a!⟩::w2] is a decomposition of [w] such that [a!⟩] does not appear in [w1], then [hide a n w] produces the word [((a!,n?)∙w1)++n?⟩::w2]. *)
  Lemma hide_close a n w1 w2 :
    ~ close(a!) ∈ w1 ->
    hide a n (w1++close(a!)::w2) = ([(a!,n?)] ∙w1)++close(n?)::w2.
  Proof.
    induction w1;simpl;
      replace (eq_letter (close (a!))) with (eqX(close(a!)))
      by reflexivity;intros;simpl_beq||simpl_eqX.
    - repeat (unfold act;simpl);simpl_eqX;reflexivity.
    - rewrite IHw1 by tauto.
      reflexivity.
  Qed.
    
  (** This function is meant to remove the first defect of a word. The argument [n] is used to store the length of list visited so far. *)
  Fixpoint remove_defect_aux n w :=
    match w with
    | [] => []
    | open (a!)::w =>
      if match_defectb a w
      then open(n?)::hide a n w
      else open(a!)::remove_defect_aux (S n) w
    | b::w => b::remove_defect_aux (S n) w
    end.

  Definition remove_defect := remove_defect_aux 0.

  (** If the word has no defect, then [remove_defect] leaves it unchanged (whatever the numeric argument). If on the other hand [w] has a first defect, then [remove_defect] will perform a rewrite step. *)
  Lemma case_remove_defect w :
    {~match_defect w /\ remove_defect w = w} + {red_def w (remove_defect w)}.
  Proof.
    destruct (case_defect w) as [M|M];[left|right].
    - split;[assumption|revert M].
      unfold remove_defect;generalize 0;induction w as [|[[a|]| |] w];intro k.
      + reflexivity.
      + intros I;simpl.
        case_eq (match_defectb a w).
        * intro h;exfalso.
          apply match_defectb_spec in h as (w1&w2&->&_).
          apply I;exists [],w1,w2,a;reflexivity.
        * intros _;rewrite IHw;[reflexivity|].
          intros (w1&w2&w3&b&->);apply I;exists (open(a!)::w1),w2,w3,b;reflexivity.
      + simpl;intro I;rewrite IHw;[reflexivity|].
        intros (w1&w2&w3&b&->);apply I;exists (open(n?)::w1),w2,w3,b;reflexivity.
      + simpl;intro I;rewrite IHw;[reflexivity|].
        intros (w1&w2&w3&b&->);apply I;exists (close p::w1),w2,w3,b;reflexivity.
      + simpl;intro I;rewrite IHw;[reflexivity|].
        intros (w1&w2&w3&b&->);apply I;exists (var r::w1),w2,w3,b;reflexivity.
    - destruct M as (w1&w2&w3&a&->&f&I1&I2).
      replace (remove_defect (w1 ++ ⟨ (a !) :: w2 ++ (a !) ⟩ :: w3))
        with (w1 ++ remove_defect_aux ⎢ w1 ⎥ (⟨ (a !) :: w2 ++ (a !) ⟩ :: w3)).
      + simpl;replace (match_defectb _ _) with true.
        * rewrite hide_close by assumption.
          apply step; assumption.
        * symmetry;apply match_defectb_spec.
          exists w2,w3;tauto.
      + remember ⎢w1⎥ as n;assert (len : ⎢w1⎥ <= n) by (rewrite Heqn;reflexivity).
        rewrite Heqn;clear Heqn I1 I2.
        revert f len;generalize (⟨ (a !) :: w2 ++ (a !) ⟩ :: w3);clear;intros w2 f len.
        cut(forall k,remove_defect_aux k (w1++w2) = w1++remove_defect_aux (⎢w1⎥+k) w2);
          [intro h;unfold remove_defect;rewrite (h 0);repeat f_equal;lia|].
        revert n f len;induction w1 as [|l w1];intros n f len k;simpl;[simpl_nat;reflexivity|].
        destruct n;[solve_length|].
        pose proof f as f'.
        simpl in f;apply first_defect_Sn in f.
        assert (len': ⎢w1⎥<=n) by solve_length;clear len.
        pose proof (IHw1 _ f len' (S k)) as IH;clear IHw1.
        destruct l as [[]| |].
        * case_eq (match_defectb a (w1++w2)).
          -- intro F;exfalso.
             cut (S n <= 0);[lia|].
             apply f';exists [],(w1++w2),a;simpl;tauto.
          -- rewrite IH;intros;repeat f_equal;lia.
        * rewrite IH;intros;repeat f_equal;lia.
        * rewrite IH;intros;repeat f_equal;lia.
        * rewrite IH;intros;repeat f_equal;lia.
  Qed.
  
  (** [remove_defect] preserves validity. *)
  Proposition remove_defect_valid w : valid w -> valid (remove_defect w).
  Proof.
    intro V;destruct (case_remove_defect w) as [(_&->)|R];[|eapply red_def_valid,R];assumption.
  Qed.
  
  (** The number of defects of [remove_defect w] is exactly [defect_count w - 1], meaning that if [w] is not a dynamic sequence, [remove_defect] will indeed remove one defect. *)
  Lemma defect_count_remove_defect w :
    valid w -> defect_count (remove_defect w) = defect_count w - 1.
  Proof.
    intro V;destruct (case_remove_defect w) as [(M&->)|R].
    - rewrite defect_count_spec in M;lia.
    - eapply red_def_defect_count,R;assumption.
  Qed.
  
  (** We may also show rather simply that [remove_defect w] is alpha-equivalent to [w], provided [w] was valid. *)
  Lemma remove_defect_equiv w :
    valid w -> remove_defect w ≡ w.
  Proof.
    intro V;destruct (case_remove_defect w) as [(M&->)|R].
    - reflexivity.
    - symmetry;apply red_def_equiv;assumption.
  Qed.
  
  (** ** Normalisation procedure *)
  (** [iter n f x] applies [f] to [x] successively [n] times. [iter n] is in fact the Church numeral [n]. *)
  Fixpoint iter {A} n (f : A -> A) x :=
    match n with
    | 0 => x
    | S n => iter n f (f x)
    end.

  (** To normalise a word [w], we apply to it the [remove_defect] function [defect_count w] times. *)
  Definition normalise w := iter (defect_count w) remove_defect w.
  
  (** If we start with a valid word, [normalise w] will produce a dynamic sequence that is alpha-equivalent to [w]. *)
  Proposition normalise_spec w :
    valid w -> dynamic_sequence (normalise w) /\ w ≡ normalise w.
  Proof.
    unfold normalise.
    remember (defect_count w) as N;revert w HeqN;induction N;intros w En V.
    - simpl;split;[split;[tauto|]|reflexivity].
      rewrite defect_count_spec;lia.
    - simpl;destruct(IHN (remove_defect w)) as (e1&e2).
      + rewrite defect_count_remove_defect,<-En by assumption;lia.
      + apply remove_defect_valid,V.
      + split.
        * assumption.
        * rewrite <- e2;symmetry;apply remove_defect_equiv,V.
  Qed.

  (** Combining what we have established so far, it immediately follows that two words over [X] are alpha-equivalent if and only if their normal form after [⟪_⟫]-translation coincide. *)
  Theorem normal_form :
    forall u v, u ≡ v <-> normalise ⟪u⟫ = normalise ⟪v⟫.
  Proof.
    intros u v;destruct (normalise_spec (@valid_repr_word u)) as (Du&Eu).
    destruct (normalise_spec (@valid_repr_word v)) as (Dv&Ev).
    rewrite repr_word_equiv;split.
    - intros E.
      apply equiv_dynamic_sequence_eq; try assumption.
      rewrite <-Eu,E,<-Ev;reflexivity.
    - intros E;rewrite Eu,E,<-Ev;reflexivity.
  Qed.

  (** * Concatenation of valid words and dynamic sequences *)
  (** Validity and the property of being a dynamic sequence are not stable under concatenation. However, we may define alternative products on words that does preserve these properties while remaining alpha-equivalent to the concatenation. *)
  (** ** Addition as a permutation *)
  (** Obviously the operation [n+_] is not a finitely supported permutation, but if we know of a bound on the argument, we may build a permutation that mimics this operation. *)
  (** [shift n] produces a permutation of pointers that bound numbers smaller that [n] to their successors, [n] to [0] and maps free names and bound numbers greater than [n] to themselves. *)
  Fixpoint shift n : (@perm (@pointer atom) _):=
    match n with
    | 0 => []
    | S n => (shift n)++[(n?,(S n)?)]
    end.

  Lemma shift_free n (a : atom) : shift n ∙ (a!) = a!.
  Proof.
    induction n;simpl.
    - reflexivity.
    - rewrite <- action_compose.
      unfold act at 2;simpl.
      destruct_eqX (a!)(n?);[discriminate|].
      destruct_eqX (a!)((S n)?);[discriminate|].
      apply IHn.
  Qed.

  Lemma shift_bound_n n : shift n ∙ (n?) = 0?.
  Proof.
    induction n;simpl.
    - apply act_nil.
    - rewrite <- action_compose.
      unfold act at 2;simpl.
      destruct_eqX ((S n)?)(n?).
      + inversion E;lia.
      + apply IHn.
  Qed.
  
  Lemma shift_bound_gt n m : n < m -> shift n ∙ (m?) = m?.
  Proof.
    intro I;induction n;simpl.
    - apply act_nil.
    - rewrite <- action_compose.
      unfold act at 2;simpl.
      destruct_eqX (m?)(n?).
      + inversion E;lia.
      + destruct_eqX (m?)((S n)?).
        * inversion E;lia.
        * apply IHn;lia.
  Qed.

  Lemma shift_bound_lt n m : m < n -> shift n ∙ (m?) = (S m)?.
  Proof.
    induction n;simpl.
    - lia.
    - intro h.
      rewrite <- action_compose.
      unfold act at 2;simpl.
      destruct_eqX (m?)(n?).
      + inversion E;subst.
        rewrite shift_bound_gt by lia.
        reflexivity.
      + destruct_eqX (m?)((S n)?).
        * inversion E;subst;lia.
        * apply IHn.
          destruct_eqX m n;[subst;tauto|lia].
  Qed.

  (** By iterating [shift] cleverly, we can mimic addition by [n] for numbers smaller that [m]. This is the meaning of the permutation [Shift n m]. *)
  Fixpoint Shift n m :=
    match n with
    | 0 => []
    | S n => shift (n+m) ++ Shift n m
    end.

  (** The specification of [Shift] is described by the next two lemmas. *)
  Lemma Shift_free (a : atom) n m : Shift n m ∙ (a!) = a!.
  Proof.
    induction n.
    - apply act_nil.
    - simpl;rewrite <- action_compose,IHn,shift_free;reflexivity.
  Qed.

  Lemma Shift_bound_lt n m k : k < m -> Shift n m ∙ (k?) = (n+k)?. 
  Proof.
    intro L;induction n.
    - apply act_nil.
    - simpl;rewrite <- action_compose,IHn.
      apply shift_bound_lt;lia.
  Qed.

  (** Notice that applying [Shift n m] to any bound number yields some bound number. *)
  Remark Shift_bound n m k : exists l, Shift n m ∙ (k?) = l?.
  Proof.
    induction n;simpl.
    - exists k;apply act_nil.
    - simpl;rewrite <- action_compose.
      destruct IHn as (l&->).
      destruct_ltb l (n+m);[destruct_ltb(n+m) l;[replace (n+m) with l in * by lia|]|].
      + exists 0;apply (shift_bound_n l).
      + exists l;apply shift_bound_gt;assumption.
      + exists (S l);apply shift_bound_lt;assumption.
  Qed.
  (* begin hide *)
  Ltac simpl_length :=
  repeat (rewrite app_length in * )
  || (rewrite map_length in * )
  || (rewrite act_lists_length in * )
  || (simpl in * ).
  (* end hide *)

  (** ** Validity preserving concatenation *)
  (** If [u] and [v] are valid, then so is [u++Shift ⎢u⎥⎢v⎥∙v]. *)
  Lemma valid_app u v : valid u -> valid v -> valid (u++Shift ⎢u⎥⎢v⎥∙v).
  Proof.
    assert (inv: forall π (w w' : W), π ∙ w = w' <-> w = π∗ ∙ w')
      by (intros;rewrite <- (act_bij (π∗)),act_pinv_p;reflexivity).
    assert (inv_shift : forall n m k, exists l, Shift n m ∗ ∙ (k?) = l?
                                      /\ Shift n m ∙ (l?) = k?)
      by (intros;case_eq (Shift n m ∗∙(k?));
          [intro a;rewrite <- (act_bij (Shift n m)),act_p_pinv,Shift_free;discriminate
          |intros l e;exists l;split; [|rewrite <- e,act_p_pinv];reflexivity]).
    remember ⎢u⎥ as N.
    remember ⎢v⎥ as K.
    intros V1 V2;split;[|split];intros w1 w2;[|intro x|];intros n E;[|intro I|];
      destruct (inv_shift N K n) as (k&ek&en);revert HeqN HeqK;
        levi E;clear E;try apply inv in E1;subst;
        try (inversion E1;clear E1);subst;intros.
    - rewrite (act_lists_cons _ _ w2) in V2.
      unfold act in V2 at 1;simpl in V2.
      rewrite <- app_nil_l,ek in V2.
      apply is_valid_open in V2 as (->&I).
      revert I;rewrite In_act_lists,inverse_inv;simpl in *.
      unfold act;simpl;rewrite en.
      rewrite Shift_bound_lt in en by solve_length.
      inversion en;simpl_nat;tauto.
    - apply is_valid_open in V1 as (->&I).
      simpl_In;tauto.
    - rewrite (act_lists_cons _ _ (w++_)),act_lists_app,act_lists_cons in V2.
      unfold act at 3 in V2;simpl in V2.
      rewrite ek in V2.
      rewrite app_comm_cons in V2;apply is_valid_open in V2 as (->&I).
      unfold act,act_lists in HeqK.
      revert en I ek HeqK; simpl_length;intros.
      rewrite In_act_lists,inverse_inv in I.
      unfold act in I;simpl in I;rewrite en in I;split;[|tauto].
      rewrite Shift_bound_lt in en by lia.
      inversion en;lia.
    - unfold act,act_lists in HeqK.
      revert en ek HeqK; simpl_length;intros.
      rewrite (act_lists_cons _ _ w2) in V2.
      unfold act in V2 at 1;simpl in V2;rewrite <-app_nil_l in V2.
      cut (k? ∈ ⌊(Shift N K ∗) ∙ x⌋).
      + intro Ik;apply (is_valid_var V2) in Ik as (I1&I2).
        simpl in I1;tauto.
      + rewrite support_action,In_act_lists,inverse_inv,en;assumption.
    - apply (is_valid_var V1) in I as (I1&I2).
      simpl_In;tauto.
    - rewrite (act_lists_cons _ _ (w++_)),act_lists_app,act_lists_cons in V2.
      unfold act at 3 in V2;simpl in V2.
      cut (k? ∈ ⌊(Shift N K ∗) ∙ x⌋).
      + intro Ik;rewrite app_comm_cons in V2;apply (is_valid_var V2) in Ik as (I1&I2).
        unfold act,act_lists in HeqK.
        revert en I ek HeqK; simpl_length;intros.
        rewrite In_act_lists,inverse_inv in I1,I2.
        unfold act in I2;simpl in I2;rewrite en in I2;split;[|tauto].
        unfold act in I1 at 2;simpl in I1;rewrite en in I1;simpl_In.
        destruct I1 as [e|I1];[|tauto].
        rewrite <- (act_bij (Shift N K)),act_p_pinv in e.
        rewrite e;unfold act;simpl;rewrite en;tauto.
      + rewrite support_action,In_act_lists,inverse_inv,en;assumption.
    - rewrite (act_lists_cons _ _ w2) in V2.
      unfold act in V2 at 1;simpl in V2.
      rewrite <- app_nil_l,ek in V2.
      apply is_valid_close in V2 as (I1&I2).
      simpl in I1;tauto.
    - pose proof (is_valid_close V1) as h;simpl_In in *.
      split;[tauto|].
      intros [I|[I|I]];try tauto.
      apply In_act_lists in I;unfold act in I;simpl in I;rewrite ek in I.
      cut (k < K).
      + intro L;rewrite Shift_bound_lt in en by assumption.
        inversion en as [E];rewrite <- E in *.
        cut (N+k< ⎢ w1 ++ close((N + k)?) :: w ⎥);[lia|].
        apply (valid_bound_support_lt V1),In_support_list.
        exists (close ((N+k)?));simpl;simpl_In;tauto.
      + rewrite HeqK;apply (valid_bound_support_lt V2),In_support_list.
        exists (close (k?));simpl;simpl_In;tauto.
    - rewrite (act_lists_cons _ _ (w++_)),act_lists_app,act_lists_cons in V2.
      unfold act at 3 in V2;simpl in V2.
      rewrite ek in V2.
      rewrite app_comm_cons in V2;pose proof (is_valid_close V2) as (I1&I2).
      cut (k < K).
      + intro lk.
        unfold act,act_lists in HeqK.
        revert en I1 I2 ek HeqK; simpl_length;simpl_In;intros en I1 I2 ek HeqK.
        rewrite In_act_lists,inverse_inv in I1,I2.
        rewrite In_act_lists,inverse_inv in I2.
        unfold act at 2 in I1;simpl in I1;rewrite en in I1.
        unfold act at 2 3 in I2;simpl in I2;rewrite en in I2.
        split;[destruct I1 as [I1|I1]|intro I';apply I2;destruct I' as [[I'|[I'|I']]|I']];
          try tauto.
        * rewrite <- (act_bij (Shift N K)),act_p_pinv in I1.
          rewrite I1;unfold act;simpl;rewrite en;tauto.
        * exfalso;cut (n < ⎢u⎥).
          -- intro ln;rewrite Shift_bound_lt in en by assumption.
             inversion en;subst;lia.
          -- apply (valid_bound_support_lt V1),In_support_list.
             eexists;split;[eauto|simpl;tauto].
        * rewrite I';unfold act;simpl;rewrite ek;tauto.
      + replace K with ⎢((Shift N K ∗) ∙ a::(Shift N K ∗) ∙ w)++close(k?) :: (Shift N K ∗)∙w2⎥
          by (rewrite HeqK at 4;unfold act,act_lists; solve_length).
        apply (valid_bound_support_lt V2),In_support_list.
        exists (close(k?));simpl;simpl_In;tauto.
  Qed.

  (** To concatenate dynamic sequences, we need in addition to normalise the result: *)
  Definition app_dyn u v := normalise (u++Shift ⎢u⎥⎢v⎥∙v).
  Infix " +++ " := app_dyn (at level 50).

  (** Indeed, whenever [u] and [v] are valid, [u+++v] is a dynamic sequence. *)
  Lemma app_dyn_dynamic_sequence u v :
    valid u -> valid v -> dynamic_sequence (u +++ v).
  Proof.
    intros h1 h2;unfold app_dyn.
    apply normalise_spec,valid_app;assumption.
  Qed.

  (** Furthermore, [u+++v] is alpha-equivalent to [u++v]. *)
  Lemma app_dyn_equiv_app u v : valid u -> valid v -> u +++ v ≡ u ++ v.
  Proof.
    intros h1 h2;unfold app_dyn.
    transitivity(u ++ Shift ⎢u⎥ ⎢v⎥ ∙ v).
    - symmetry;apply normalise_spec,valid_app;assumption.
    - apply αequiv_app_left.
      symmetry;apply αequiv_αfresh_transpose.
      intros [a|n] I.
      + apply Shift_free.
      + exfalso;apply I,valid_bound_αfresh,h2.
  Qed.

  (** This operation allows us to generalise our [normal_form] theorem as follows: [u] and [v] are alpha-equivalent if and only if for any valid word [w] we have [w +++ ⟪u⟫ = w +++ ⟪v⟫]. *)
  Proposition app_dyn_equiv u v :
    u ≡ v <-> forall w, valid w -> w +++ ⟪u⟫ = w +++ ⟪v⟫.
  Proof.
    split.
    - intros he w hw.
      apply equiv_dynamic_sequence_eq.
      + apply app_dyn_dynamic_sequence;auto using valid_repr_word.
      + apply app_dyn_dynamic_sequence;auto using valid_repr_word.
      + repeat rewrite app_dyn_equiv_app;auto using valid_repr_word.
        apply αequiv_app_left,repr_word_equiv,he.
    - intros h.
      apply normal_form.
      assert (E:valid []).
      + split;[|split];intro;intros;simpl_words.
      + apply h in E;unfold app_dyn in E;simpl in E.
        repeat rewrite act_nil in E.
        assumption.
  Qed.

  (** * Relational interpretation *)
  (** We now build a relational interpretation of words over [X], and prove that this interpretation is fully abstract with respect to alpha-equivalence, in the sense that two words will be alpha-equivalent if and only if they are mapped to the same binary relation by the interpretation. *)
  (** We define the type of dynamic sequences using a sigma-type construction. This will form the base type for our relations. *)
  Definition Dyn :={w : word | test_dyn_seq w = true }.

  Lemma Dyn_eq (o1 o2 : Dyn) : $ o1 = $ o2 <-> o1 = o2.
  Proof.
    destruct o1 as (o1&P1);destruct o2 as (o2&P2);simpl.
    split.
    - intro e.
      apply eq_sig_hprop;simpl;auto.
      clear.
      intro x;destruct (test_dyn_seq x).
      + intros p q;apply UIP.
      + intro p;discriminate.
    - apply eq_sig_fst.
  Qed.
  
  (** Recall that we consider two relations to be equal if they contain the same pairs. *)
  Global Instance relseq : SemEquiv (relation Dyn) := eqRel.

  (** The interpretation [ρ l] of a letter [l] consists of the pairs [(w,w+++⦑l⦒)] for every dynamic sequence [w]. *)
  Definition ρ : letter -> relation Dyn :=
    fun l w1 w2 => $ w2 = ($ w1) +++ [⦑l⦒].

  (** This interpretation lifts to words, in the sense that the relation associated with [u] contains exactly the pairs [(w,w+++⟪u⟫)]. *)
  Lemma ρ_spec u : mapRel ρ u ≃ fun w1 w2 => $ w2 = $ w1 +++ ⟪u⟫.
  Proof.
    induction u using rev_induction;simpl;intros w1 w2;auto.
    - unfold Δ;intuition subst;auto.
      + destruct w2 as (w2&D);simpl.
        apply test_dyn_seq_spec in D.
        unfold app_dyn;simpl;rewrite app_nil_r.
        apply equiv_dynamic_sequence_eq.
        * assumption.
        * apply normalise_spec,D.
        * apply normalise_spec,D.
      + apply Dyn_eq.
        destruct w1 as (w1&D);simpl in *.
        apply test_dyn_seq_spec in D.
        unfold app_dyn in H;rewrite H,app_nil_r.
        apply equiv_dynamic_sequence_eq; try apply normalise_spec;apply D.
    - rewrite (mapRel_add _ _ _ _).
      simpl;unfold product;split.
      + intros ((z&hz)&e1&e2);auto.
        apply IHu in e1 as e;simpl in e.
        apply equiv_dynamic_sequence_eq.
        * destruct w2 as (w2&D);apply test_dyn_seq_spec,D.
        * apply normalise_spec.
          apply valid_app.
          -- destruct w1 as (w1&D);apply test_dyn_seq_spec,D.
          -- apply valid_repr_word.
        * unfold ρ in e2;rewrite e2;simpl.
          destruct w1 as (w1&hw1);simpl in *.
          pose proof hw1 as D;apply test_dyn_seq_spec in D as (V1&D).
          rewrite e;repeat rewrite app_dyn_equiv_app;simpl;auto using valid_repr_word. 
          -- rewrite map_app,app_ass;reflexivity.
          -- apply normalise_spec,valid_app;auto using valid_repr_word.
          -- replace [⦑a⦒] with ⟪[a]⟫ by reflexivity;auto using valid_repr_word.
      + intro e.
        assert (D1:test_dyn_seq (app_dyn ($ w1) ⟪u⟫) = true).
        * apply test_dyn_seq_spec,normalise_spec,valid_app;auto using valid_repr_word.
          destruct w1 as (w1&D);apply test_dyn_seq_spec,D.
        * exists (exist _ (app_dyn ($w1)  ⟪u⟫) D1);split.
          -- rewrite (IHu _ _);simpl;reflexivity.
          -- unfold ρ;rewrite e;simpl.
             apply equiv_dynamic_sequence_eq.
             ++ apply app_dyn_dynamic_sequence.
                ** destruct w1 as (w1&D);apply test_dyn_seq_spec,D.
                ** apply valid_repr_word.
             ++ apply app_dyn_dynamic_sequence.
                ** apply test_dyn_seq_spec,D1.
                ** replace [⦑a⦒] with ⟪[a]⟫ by reflexivity;auto using valid_repr_word.
             ++ clear;destruct w1 as (w1&D);simpl;apply test_dyn_seq_spec in D as (V1&D).
                repeat rewrite app_dyn_equiv_app;auto using valid_repr_word.
                ** rewrite map_app,app_ass;reflexivity.
                ** apply app_dyn_dynamic_sequence;auto using valid_repr_word.
                ** replace [⦑a⦒] with ⟪[a]⟫ by reflexivity;auto using valid_repr_word.
  Qed.

  (** It is then fairly routine to check that this relational interpretation is indeed fully-abstract. *)
  Theorem free_relational_interpretation :
    forall u v, u ≡ v <-> mapRel ρ u ≃ mapRel ρ v.
  Proof.
    intros u v;split.
    - rewrite app_dyn_equiv.
      intros h w1 w2;split;intro E.
      + apply ρ_spec.
        rewrite <- h by (destruct w1 as (w1&D);apply test_dyn_seq_spec,D).
        apply ρ_spec,E.
      + apply ρ_spec.
        rewrite h by (destruct w1 as (w1&D);apply test_dyn_seq_spec,D).
        apply ρ_spec,E.
    - intros h.
      apply normal_form.
      assert (e1 : test_dyn_seq [] = true) by reflexivity.
      assert (e2 : test_dyn_seq (normalise ⟪u⟫) = true)
        by apply test_dyn_seq_spec,normalise_spec,valid_repr_word.
      assert (r1 : mapRel ρ u (exist _ [] e1)(exist _ (normalise⟪u⟫) e2)).
      + apply ρ_spec;simpl.
        unfold app_dyn;simpl;rewrite act_nil;reflexivity.
      + apply h,ρ_spec in r1.
        simpl in r1.
        unfold app_dyn in r1;simpl in r1;rewrite act_nil in r1;assumption.
  Qed. 

End s.