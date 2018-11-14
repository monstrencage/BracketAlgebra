(** * RIS.alternate_eq : equivalent definitions of alpha-equivalence. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export transducer.
Section s.
  Context {atom X: Set}{𝐀 : Atom atom} {𝐗 : Alphabet 𝐀 X}.
  
  (** * Alternative definition of alpha-equivalence *)
  (** ** Main results *)

  (** We introduce a new notion of alpha-equivalence. We just replaced the rule [αα] with the new [αα']. *)
  Reserved Notation " u ≡' v " (at level 80).
  Inductive αequiv' : word -> word -> Prop :=
  | αt' u v w : u ≡' v -> v ≡' w -> u ≡' w
  | αε' : [] ≡' []
  | αr' u v l : u ≡' v -> u++[l] ≡' v++[l]
  | αl' u v l : u ≡' v -> l::u ≡' l::v
  | αα' a b u : b #α u -> a #α u -> u ≡' [(a,b)]∙u
  where " u ≡' v " := (αequiv' u v).
  Hint Constructors αequiv'.

  (** Since we already know that [αα'] is admissible, and since we can prove that [αα] is an instance of [αα'], we get that the new definition of alpha-equivalence defines the same relation as [≡]. *)  
  Theorem equiv_alt u v : u ≡ v <-> u ≡' v.
  Proof.
    split;intro E;induction E;reflexivity||eauto.
    - replace (⟨b :: [(a, b)] ∙ u ++ [b⟩])
        with ([(a, b)] ∙ (⟨a :: u ++ [a⟩])).
      + apply αα'.
        * unfold fresh__α in *.
          rewrite 𝗙_cons,𝗙_add;simpl;rewrite H.
          destruct_eqX b a;simpl;reflexivity.
        * unfold balanced,fresh__α in *.
          rewrite 𝗙_cons,𝗙_add;simpl;simpl_beq.
          destruct (𝗙 a u) as ((m&n)&p);simpl in H0;rewrite d_binding_simpl in H0.
          destruct H0 as (->&->).
          destruct n;reflexivity.
      + rewrite act_lists_cons,act_lists_app.
        f_equal;[|f_equal];repeat (unfold act;simpl;f_equal);simpl_beq;auto.
    - apply αr,IHE.
    - apply αl,IHE.
    - apply αequiv_αfresh_transpose.
      intros c F;unfold act;simpl.
      destruct_eqX c a;[|destruct_eqX c b];subst;tauto.
  Qed.

  (** ** Additional properties *)
  Global Instance αequiv'_equivalence : Equivalence αequiv'.
  Proof.
    split;intro;intros;rewrite <- equiv_alt in *.
    - reflexivity.
    - symmetry;auto.
    - etransitivity;eauto.
  Qed.

  Lemma αequiv'_app_left u v w : u ≡' v -> w++u≡'w++v.
  Proof. intro E;induction w;simpl;auto. Qed.

  Lemma αequiv'_app_right (u v w : word) : u ≡' v -> u++w≡'v++w.
  Proof. 
    intro E;revert w;induction w using rev_induction;simpl;auto.
    + repeat rewrite app_nil_r;auto.
    + repeat rewrite <- app_ass; apply αr';auto.
  Qed.

  Global Instance αequiv'_app :
    Proper (αequiv' ==> αequiv' ==> αequiv') (@app letter).
  Proof.
    intros u1 v1 E1 u2 v2 E2.
    transitivity (u1++v2).
    - apply αequiv'_app_left;auto.
    - apply αequiv'_app_right;auto.
  Qed.

  Lemma αequiv'_binding u v : u ≡' v -> forall a, 𝗙 a u = 𝗙 a v.
  Proof. intros E a;apply αequiv_binding,equiv_alt,E. Qed.

  Lemma αequiv'_perm u v π : u ≡' v -> π ∙ u ≡' π ∙ v.
  Proof. intros E;apply equiv_alt,αequiv_perm,equiv_alt,E. Qed.

  (** * Alpha-equivalence from "Leaving the nest" *)
  (** In earlier work by Gabbay, Ghica and Petrisan an alternative definition of alpha-equivalence was used. We show here that it is equivalent with our definition. *)

  Reserved Notation " u =α= v " (at level 80).
  Inductive αequiv2 : word -> word -> Prop :=
  | αε2 : [] =α= []
  | αm u v l : u =α= v -> u++[l] =α= v++[l]
  | αα2 a b u1 u2 v1 v2 :
      a ⋄ u2 -> b ⋄ v2 ->
      (forall c, c # a -> c # b -> c # u1++u2++v1++v2 ->
            u1++open c::[(a,c)]∙u2 =α= v1++open c::[(b,c)]∙v2)
      -> u1++open a::u2++[close a] =α= v1++open b::v2++[close b]
  where " u =α= v " := (αequiv2 u v).
  Hint Constructors αequiv2.

  Remark αequiv_alternate u1 u2 v1 v2 a b c :
    c #α u2 -> c #α v2 -> a ⋄ u2 -> b ⋄ v2 ->
    u1++open c::[(a,c)]∙u2 ≡ v1++open c::[(b,c)]∙v2 ->
    u1++open a::u2++[close a] ≡ v1++open b::v2++[close b].
  Proof.
    intros f1 f2 b1 b2 E.
    transitivity  (u1 ++ open c :: [(a, c)] ∙ u2 ++ [close c]).
    - apply αequiv_app_left.
      apply αα;auto.
    - transitivity  (v1 ++ open c :: [(b, c)] ∙ v2 ++ [close c]).
      + repeat rewrite app_comm_cons,<- app_ass.
        apply αr,E.
      + apply αequiv_app_left.
        symmetry;apply αα;auto.
  Qed.

  Lemma αequiv2_to_αequiv u v : u =α= v -> u≡v.
  Proof.
    intro E;induction E;auto.
    - reflexivity.
    - apply αr,IHE.
    - destruct (exists_fresh (a :: b :: ⌊ u1 ++ u2 ++ v1 ++ v2 ⌋)) as (c & I).
      repeat rewrite support_list_app in I;simpl_In in I.
      apply αequiv_alternate with (c:=c);auto.
      + apply αfresh_support;tauto.
      + apply αfresh_support;tauto.
      + apply H2.
        * simpl;tauto.
        * simpl;tauto.
        * repeat rewrite support_list_app;simpl_In;tauto.
  Qed.

  Lemma αequiv_to_αequiv2 u v : u≡v -> u =α= v.
  Proof.
    rewrite completeness.
    revert v;induction u as [|l u IHu] using len_rev_induction;intros v' (s&P&A).
    - inversion P;auto.
    - pose proof P as P0;apply path_letter in P as (v&l'&s'&->&P&hs).
      unfold step in hs;destruct l as [a|a|x];destruct l' as [b|b|y];try tauto.
      + subst;apply Accepting_cons in A as (A&E);simpl in E;inversion E;clear E;subst.
        apply αm,IHu;[|exists s'];auto.
      + destruct hs as (hs&->);destruct_eqX a b.
        * subst;apply αm,IHu;[|exists s';split];auto.
          case_in (b,b) s'.
          -- apply decomposition in I as (m1&m2&->&I).
             rewrite rmfst_in in A;repeat rewrite map_app in *;simpl;auto.
             apply length_app in A as (->&->);[|repeat rewrite map_length];reflexivity.
          -- rewrite rmfst_notin in A;auto.
        * destruct (path_stack_decompose P N hs) as (u1&u2&v1&v2&->&->&L&B1&B2).
          repeat rewrite app_ass;apply αα2;auto.
          intros c I1 I2 I3;apply IHu.
          -- rewrite app_length,app_length;simpl;rewrite (act_lists_length _ u2);auto.
          -- pose proof I3 as Ic;repeat rewrite support_list_app in Ic;simpl in Ic;simpl_In in Ic.
             assert (E1:u1 ++ open a :: u2 ++ [close a] ≡ u1 ++ open c :: [(a,c)]∙ u2 ++ [close c] )
               by (apply αequiv_app_left,αα;auto;apply αfresh_support;tauto).
             assert (E2:v1 ++ open b :: v2 ++ [close b] ≡ v1 ++ open c :: [(b,c)]∙v2 ++ [close c] )
               by (apply αequiv_app_left,αα;auto;apply αfresh_support;tauto).
             repeat rewrite app_comm_cons,<-app_ass in *.
             symmetry in E1;apply αequiv_path in E1 as (s1&P1&A1);apply αequiv_path in E2 as (s2&P2&A2).
             assert (E0 : prj2 (@nil (atom*atom)) = prj1(@nil (atom*atom))) by reflexivity.
             assert (E1 : prj2 (@nil (atom*atom)) = prj1([]⋈@nil (atom*atom))) by reflexivity.
             pose proof (path_mix E0 P1 P0) as (E4&P4).
             pose proof (path_mix E1 P4 P2) as (E5&P3).
             unfold mix in P3 at 1;simpl in P3; clear E0 E1.
             apply path_letter in P3 as (?&?&s4&E&P3&P5);simpl_words;subst.
             eexists;split;eauto.
             clear P P0 P1 P2 P3 P4 IHu Ic B1 B2 N hs.
             set (t := prj1 s1).
             replace s1 with (t ⊗ t) in * by (unfold t;rewrite A1 at 2;symmetry;apply combine_split).
             replace (s'⊖(a,b)) with (t ⊗ t) in * 
               by (etransitivity;[|symmetry;apply combine_split];rewrite <-A,<-E4,combine_snd;auto).
             unfold mix in E5,P5;rewrite combine_fst,(@combine_snd _ _ t t) in E5,P5;auto.
             rewrite combine_snd in E5;rewrite combine_fst in P5;auto.
             replace s2 with (t⊗t) in * by (rewrite (@combine_split _ _ s2),<-A2,E5;auto).
             clear A1 A E4 E5 A2;rewrite combine_snd in P5;auto.
             destruct P5 as ([(_&A')|(m1&m2&E&A')]&E').
             ++ rewrite (rmfst_absent A') in E';subst.
                rewrite combine_fst,combine_snd;auto.
             ++ subst;rewrite (rmfst_present _ A') in E'.
                rewrite Accepting_app,Accepting_cons_refl,<-Accepting_app.
                rewrite <- E';apply Accepting_combine.
      + destruct hs as (->&p&->&hs).
        replace (p∙x) with x.
        * apply αm,IHu;[|exists s'];auto.
        * symmetry;apply action_invariant,map_eq_id;intros a I.
          apply hs in I;apply paired_Accepting in I;auto.
  Qed.
End s.