(** * RIS.traces : extracting stacks directly from words. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export transducer.

Section s.
  Context {atom X: Set}{𝐀 : Atom atom} {𝐗 : Alphabet 𝐀 X}.

(** * Simple trace *)
(** We introduce here the notion of trace of a word. Intuitively, the trace of a word [u] is a list of names, corresponding to the unmatched [⟨a] appearing in [u]. They appear in reverse order, for instance the trace of [[⟨a;⟨b]] will be [[b;a]].

 The trace of a word [u] after a trace [l] is computed by the following reverse inductive definition:
    - [Tr l [] = l];
    - [Tr l (u++[⟨a])=a::Tr l u];
    - [Tr l (u++[var x])=Tr l u];
    - [Tr l (u++[a⟩])=(Tr l u) ⊖ a].
     *)
Definition updTr acc l :=
  match l with
  | var _ => acc
  | ⟨a => a::acc
  | a⟩ => acc ⊖ a
  end.
Definition Tr l u := fold_left updTr u l.

(** The following identities hold. *)
Lemma Tr_app l u v : Tr l (u++v) = Tr (Tr l u) v.
Proof. unfold Tr;rewrite fold_left_app;reflexivity. Qed.
Lemma Tr_add l u a : Tr l (u++[a]) = updTr (Tr l u) a.
Proof. unfold Tr;rewrite fold_left_app;reflexivity. Qed.

(** This technical lemma will be used for the next proposition.*)
Lemma updTr_length l u x :
  ⎢updTr (Tr l u) x⎥
  <= ⎢Tr l u⎥ + sum (fun b => c_binding (𝗳 b x) - d_binding (𝗳 b x)) ⌊x⌋.
Proof.
  destruct x as [a|a|x];simpl.
  - simpl_beq;unfold c_binding,d_binding;simpl;lia.
  - simpl_beq;unfold c_binding,d_binding;simpl.
    case_in a (Tr l u).
    + apply decomposition in I as (t1&t2&->&I).
      rewrite (rmfst_in _ I),app_length,app_length;simpl;lia.
    + rewrite (rmfst_notin I);lia.
  - rewrite sum_zero_in;intros;lia.
Qed.

(** The number of occurrences of [a] in [Tr l u] can be obtained from the number of [a]s in [l] by first subtracting [d_binding (𝗙 a u)], and then adding [c_binding (𝗙 a u)]. *)
Proposition Tr_length_binding_atom a l u :
  nb a (Tr l u) = (nb a l - d_binding (𝗙 a u)) + c_binding (𝗙 a u).
Proof.
  induction u using rev_induction.
  - unfold 𝗙,d_binding;simpl;lia.
  - rewrite Tr_add,𝗙_add,d_binding_prod,c_binding_prod.
    destruct a0 as [b|b|x];simpl.
    + unfold_eqX;simpl_binding;lia.
    + unfold_eqX;simpl_binding.
      * symmetry in E;subst;case_in a (Tr l u).
        -- apply decomposition in I as (t1&t2&E&I);rewrite E in *.
           rewrite (rmfst_in _ I); revert IHu.
           repeat (simpl;
                   rewrite filter_app
                   || rewrite app_length
                   || rewrite app_length
                   || simpl_beq);simpl.
           destruct (c_binding (𝗙 a u));lia.
        -- rewrite (rmfst_notin I),IHu.
           rewrite nb_not_In in I;rewrite I in *. 
           destruct (c_binding (𝗙 a u));try lia.
      * rewrite <- plus_n_O,<-Minus.minus_n_O,<- IHu;clear IHu.
        f_equal.
        case_in b (Tr l u).
        -- apply decomposition in I as (t1&t2&E&I);rewrite E in *.
           rewrite (rmfst_in _ I);repeat rewrite filter_app;simpl;simpl_beq;reflexivity.
        -- rewrite (rmfst_notin I);reflexivity.
    + simpl;repeat rewrite d_binding_simpl.
      rewrite <- plus_n_O,<-Minus.minus_n_O;lia.
Qed.

(** The atoms in the trace [Tr l u] all appear either in the support of [u] or in [l]. *)
Lemma Tr_support l u : Tr l u ⊆ ⌊u⌋++l.
Proof.
  induction u using rev_induction;simpl;[reflexivity|].
  rewrite Tr_add,support_list_app.
  setoid_replace ((⌊u⌋++⌊[a]⌋)++l) with  ((⌊[a]⌋++⌊u⌋)++l) by (intro;simpl_In;tauto).
  rewrite app_ass,<-IHu;generalize dependent (Tr l u);intros t _;clear u l.
  unfold support, SupportList;simpl;rewrite app_nil_r,(undup_equivalent ⌊a⌋).
  destruct a as [a|a|x];simpl.
  - reflexivity.
  - rewrite rmfst_decr;intro;simpl_In;tauto.
  - intro;simpl_In;tauto.
Qed.

(** If [a] does not appear in [Tr l u] (for any [l]), then [a] is close-balanced in [u]. *)
Lemma Tr_close_balanced a u l : ~ a ∈ Tr l u -> a ▷ u.
Proof.
  pose proof (Tr_length_binding_atom a l u) as E.
  rewrite nb_not_In;intros I;rewrite I in E;simpl in E.
  unfold open_balanced;lia.
Qed.

(** If [a] is close-balanced in [u], then it cannot appear in [Tr [] u]. Note however that it could appear in [Tr l u] for some [l]: take for instance [l=[a]] and [u=[]]. *)
Lemma In_Tr_not_open_balanced a u : a ▷ u -> ~ a ∈ Tr [] u.
Proof.
  pose proof (Tr_length_binding_atom a [] u) as L;revert L.
  simpl;unfold open_balanced.
  intros L E I;rewrite E in L.
  apply nb_not_In in L;tauto.
Qed.

(** [Tr] commutes with the action of permutations. *)
Lemma Tr_perm p u l : p∙(Tr l u) = Tr (p∙l) (p∙u).
Proof.
  induction u as [|x u] using rev_induction;auto.
  rewrite Tr_add,act_lists_app,act_lists_cons,Tr_add,<-IHu.
  clear IHu;generalize dependent (Tr l u);clear l u;intro l.
  destruct x as [a|a|x];simpl;auto.
  case_in a l.
  - apply decomposition in I as (l1&l2&->&I).
    rewrite rmfst_in;auto.
    rewrite act_lists_app,act_lists_app,act_lists_cons,rmfst_in;auto.
    rewrite In_act_lists,inverse_comp_l;auto.
  - repeat rewrite rmfst_notin;auto.
    rewrite In_act_lists,inverse_comp_l;auto.
Qed.

(** * Indexed traces *)
(** For Theorem [path_αequiv], we will need a stronger notion of traces. Simple traces, as defined in the previous section, list the occurrences of unmatched [⟨a]. In the definition to come we strengthen this by adding a natural number corresponding to the index of the letter in [u] where the unmatched [⟨a] was found. *)
(** ** Technical definition *)
(** We start by defining a variant of [rmfst], intended to work on lists of pairs built out of a number an an atom. Its effect will be made clear by the following lemmas. *)
Fixpoint rmfstn (a : atom) (l : list (nat*atom)) :=
  match l with
  | [] => []
  | (n,b)::l => if a=?=b then l else (n,b)::(rmfstn a l)
  end.

(** Given a name [a] and a list [l], if there is no pair of the shape [(n,a)] in [l] then [rmfstn a l = l]. *)
Lemma rmfstn_notin a l : ~ a ∈ prj2 l -> rmfstn a l = l.
Proof.
  induction l as [|(n,b) l];simpl;auto.
  intros N;simpl.
  destruct_eqX a b.
  - exfalso;apply N;tauto.
  - f_equal;apply IHl;intro;tauto.
Qed.
(** If on the other hand there are such pairs in [l], then [rmfstn a l] will remove from [l] the first of them. *)
Lemma rmfstn_in a n l1 l2 :
  ~ a ∈ prj2 l1 -> rmfstn a (l1 ++ (n,a) :: l2) = l1++l2.
Proof.
  induction l1 as [|(m,b) l1];simpl;auto.
  - simpl_beq;auto.
  - intros N;destruct_eqX a b.
    + exfalso;apply N;tauto.
    + f_equal;apply IHl1;tauto.
Qed.

(** [rmfst] and [rmfstn] are related by the following identity. *)
Lemma rmfstn_rmfst a l : (prj2 l) ⊖ a = prj2 (rmfstn a l).
Proof. induction l as [|(n,b)l];simpl;auto;destruct_eqX a b;simpl;congruence. Qed.

(** [rmfstn a l] is contained in the list [l]. *)
Lemma rmfstn_decr a l : rmfstn a l ⊆ l.
Proof.
  case_in a (prj2 l).
  - apply decomposition in I as (?&?&E&A).
    apply split_snd in E as (?&?&?&->&->&->);auto.
    rewrite rmfstn_in;auto;intro;simpl_In;tauto.
  - rewrite rmfstn_notin;auto;reflexivity.
Qed.

(** ** Main definitions *)
(** We define [Trn] as follows. Its meaning will become clearer with the following lemmas. *)
Definition updTrn (accn : nat * list (nat * atom)) l :=
  let n := fst accn in
  let acc := snd accn in
  match l with
  | var _ => (S n,acc)
  | ⟨a => (S n,(n,a)::acc)
  | a⟩ => (S n,rmfstn a acc)
  end.
Definition Trn_aux l u := fold_left updTrn u l.
Definition Trn u := snd (Trn_aux (0,[]) u).

(* begin hide *)
Lemma Trn_aux_add l u a : Trn_aux l (u++[a]) = updTrn (Trn_aux l u) a.
Proof. unfold Trn_aux;rewrite fold_left_app;reflexivity. Qed.
Lemma Trn_aux_app l u v : Trn_aux l (u++v) = Trn_aux (Trn_aux l u) v.
Proof. unfold Trn_aux;rewrite fold_left_app;reflexivity. Qed.
Lemma Trn_aux_fst l u : fst (Trn_aux l u) = fst l + ⎢u⎥.
Proof.
   destruct l as (n,l);simpl.
   induction u as [|a u] using rev_induction;simpl;[lia|].
   rewrite Trn_aux_add,app_length;simpl.
   destruct a;simpl;rewrite IHu;lia.
Qed.
Lemma Trn_aux_Trn u : Trn_aux (0,[]) u = (⎢u⎥,Trn u).
Proof. rewrite surjective_pairing at 1;rewrite Trn_aux_fst;simpl;reflexivity. Qed.    
Lemma Trn_add u a : Trn (u++[a]) = snd (updTrn (⎢u⎥,Trn u) a).
Proof. rewrite <- Trn_aux_Trn;unfold Trn;rewrite Trn_aux_add;reflexivity. Qed.
(* end hide *)
(** ** Properties of indexed traces *)
(** The second projection of [Trn u] is [Tr [] u]. *)
Remark updTrn_updTr acc l :
  prj2 (snd (updTrn acc l)) = updTr (prj2 (snd acc)) l.
Proof.
  destruct acc as (n,acc);destruct l as [a|a|x];simpl;auto.
  rewrite rmfstn_rmfst;auto.
Qed.

Corollary Trn_Tr u : prj2 (Trn u) = Tr [] u.
Proof.
  unfold Trn;simpl.
  induction u as [|a u] using rev_induction;simpl.
  - reflexivity.
  - rewrite Tr_add,Trn_aux_add,<-IHu,<-updTrn_updTr;reflexivity.
Qed.

(** Any number appearing in the first projection of [Trn u] is strictly smaller than the length of [u]. *)
Lemma Trn_In_length u : forall n, n ∈ prj1 (Trn u) -> n < ⎢u⎥.
Proof.
  intro n;induction u using rev_induction.
  - simpl;tauto.
  - rewrite Trn_add,app_length;simpl.
    destruct a as [a|a|x];simpl in *;auto.
    + intuition lia.
    + case_in a (prj2 (Trn u)).
      * apply decomposition in I as (s1&s2&E&I1).
        destruct (split_snd E I1) as (k&t1&t2&Eu&->&_).
        rewrite Eu in *;rewrite rmfstn_in;auto.
        repeat rewrite map_app in *;simpl_In in *;simpl in *;intuition lia.
      * rewrite rmfstn_notin;auto;intuition lia.
    + intro h;apply IHu in h;lia.
Qed.

(** If the pair [(n,a)] appears in [Trn u], then the letter at index [n] in [u] is [⟨a]. *)
Lemma Trn_open a x u v : (⎢u⎥,a) ∈ Trn (u++x::v) -> x = ⟨a.
Proof.
  induction v as [|l v] using rev_induction;simpl;auto.
  - rewrite Trn_add;destruct x as [b|b|x];simpl.
    + intros [E|I];[inversion E;auto|].
      cut (⎢u⎥ < ⎢u⎥);[lia|].
      apply Trn_In_length,in_map_iff;exists (⎢u⎥,a);split;auto.
    + intro I;apply rmfstn_decr in I.
      cut (⎢u⎥ < ⎢u⎥);[lia|].
      apply Trn_In_length,in_map_iff;exists (⎢u⎥,a);split;auto.
    + intro I.
      cut (⎢u⎥ < ⎢u⎥);[lia|].
      apply Trn_In_length,in_map_iff;exists (⎢u⎥,a);split;auto.
  - rewrite app_comm_cons,<-app_ass,Trn_add;destruct l as [b|b|y];simpl.
    + intros [E|I];[|apply IHv;auto].
      inversion E;rewrite app_length in *;simpl in *;lia.
    + intro I;eapply IHv,rmfstn_decr,I.
    + intro I;eapply IHv,I.
Qed.

(** If the number [n1] appears before [n2] in [Trn u], then [n2<n1]. *)
Lemma Trn_incr u n1 a1 n2 a2 u1 u2 u3 :
  Trn u = u1++(n1,a1)::u2++(n2,a2)::u3 -> n2 < n1.
Proof.
  revert u1 u2 u3 a1 a2 n1 n2;induction u using rev_induction.
  - replace (Trn []) with (@nil (nat*atom)) by reflexivity.
    intros;simpl_words.
  - rewrite Trn_add;intros u1 u2 u3 a1 a2 n1 n2 E.
    destruct a as [a|a|x];simpl in *.
    + destruct u1.
      * simpl in E;inversion E;subst.
        apply Trn_In_length;rewrite H2,map_app;simpl_In;simpl;tauto.
      * simpl in E;inversion E;subst.
        eapply IHu;eauto.
    + case_in a (prj2 (Trn u)).
      * apply decomposition in I as (t1&t2&Et&A).
        apply split_snd in Et as (k&s1&s2&Et&->&->);auto.
        rewrite Et in *;rewrite rmfstn_in in E;auto.
        levi E;clear E;subst.
        -- apply (IHu (u1++[(k,a)]) u2 u3 a1 a2).
           rewrite app_ass;reflexivity.
        -- inversion E1;subst.
           levi H1;clear H1;subst.
           ++ apply (IHu u1 (w++[(k,a)]) u3 a1 a2).
              repeat rewrite app_ass;reflexivity.
           ++ apply (IHu u1 (w++(k,a)::a0::w0) u3 a1 a2).
              repeat rewrite app_ass;reflexivity.
           ++ inversion E0;subst.
              apply (IHu u1 u2 (w0++(k,a)::s2) a1 a2).
              repeat (rewrite app_ass;simpl);reflexivity.
        -- apply (IHu (s1++(k,a)::a0::w) u2 u3 a1 a2).
           repeat (rewrite app_ass;simpl);reflexivity.
      * rewrite rmfstn_notin in E;auto.
        eapply IHu;eauto.
    + eapply IHu;eauto.
Qed.

(** To state results about the binding power, we define the boolean predicate [select n a]. It holds for pairs [(m,b)] where [n<=m] and [a=b]. *)
Definition select n (a : atom) p := Nat.leb n (fst p) && a =?= (snd p).
Lemma select_spec n a m b : select n a (m,b) = true <-> n <= m /\ a = b.
Proof. unfold select;rewrite andb_true_iff,PeanoNat.Nat.leb_le,eqX_correct;tauto. Qed.

(** The number of pairs [(n,a)], such that [n] is smaller than or equal to the length of [u], appearing in [Trn (u++v)] is equal to [c_binding (𝗙 a v)]. *)
Lemma Trn_c_binding a u v :
  ⎢ select ⎢u⎥ a :> Trn (u++v)⎥ = c_binding (𝗙 a v).
Proof.
  induction v as [|x v] using rev_induction.
  - simpl;rewrite app_nil_r,length_zero_iff_nil;apply filter_nil.
    intros (n,b) I;rewrite <- not_true_iff_false;intros E.
    apply select_spec in E as (E&->).
    apply PeanoNat.Nat.le_ngt in E;apply E.
    apply Trn_In_length,in_map_iff;exists (n,b);auto.
  - rewrite 𝗙_add,c_binding_prod,<-app_ass,Trn_add.
    destruct x as [b|b|x];simpl.
    + unfold select at 1;simpl.
      rewrite app_length.
      destruct_leb ⎢u⎥ (⎢u⎥ + ⎢v⎥);try lia;destruct_eqX a b;simpl.
      * rewrite IHv,d_binding_simpl;lia.
      * simpl_binding;lia.
    + case_in b (prj2 (Trn (u++v))).
      * apply decomposition in I as (l1&l2&E&I).
        apply split_snd in E as (n&t1&t2&E&->&->);auto.
        rewrite E in *;rewrite rmfstn_in,filter_app;auto;rewrite filter_app in IHv;revert IHv.
        repeat rewrite app_length;simpl.
        simpl;unfold select at 2;simpl.
        destruct_eqX a b;destruct_leb ⎢u⎥ n;simpl_binding;try lia.
        cut (⎢select ⎢u⎥ b :> t1⎥ + ⎢select ⎢u⎥ b :> t2⎥ = 0);
          [lia|].
        apply PeanoNat.Nat.eq_add_0;split;apply length_zero_iff_nil,filter_nil;
          intros (m,c) Ic;rewrite <-not_true_iff_false;intro Ec;apply select_spec in Ec as (Lc&->).
        -- apply I,in_map_iff;exists (m,c);auto.
        -- apply in_split in Ic as (?&?&->).
           apply Trn_incr in E;lia.
      * rewrite rmfstn_notin;auto.
        rewrite IHv;destruct_eqX a b;simpl_binding;try lia.
        replace (c_binding (𝗙 b v)) with 0 in *;[lia|].
        rewrite <- IHv;symmetry;apply length_zero_iff_nil,filter_nil.
        intros (n,c) Ic;rewrite <-not_true_iff_false;intros Ec;apply select_spec in Ec as (Lc&->).
        apply I,in_map_iff;exists (n,c);auto.
    + rewrite IHv,d_binding_simpl;lia.
Qed.

(** If the pair [(⎢u⎥,a)] appears in [Trn (u++⟨a::v)], then [a] is close-balanced in [v]. *)
Lemma Trn_d_binding a u v : (⎢u⎥,a) ∈ Trn (u++⟨a::v) -> a ◁ v.
Proof.
  induction v using rev_induction.
  - intros _;reflexivity.
  - rewrite app_comm_cons, <- app_ass,Trn_add.
    unfold close_balanced;rewrite 𝗙_add,d_binding_prod.
    destruct a0 as [b|b|x];simpl;try destruct_eqX a b;subst;try rewrite d_binding_simpl.
    + repeat rewrite app_length;simpl.
      intros [F|I];[inversion F;lia|].
      apply IHv in I as ->;auto.
    + repeat rewrite app_length;simpl.
      intros [F|I];[inversion F;lia|].
      apply IHv in I as ->;auto.
    + intro I;pose proof (Trn_c_binding b u (⟨b::v)) as E.
      rewrite 𝗙_cons,c_binding_prod in E;revert E;simpl;simpl_beq;simpl.
      pose proof I as B;apply rmfstn_decr,IHv in B as ->.
      cut (⎢select ⎢u⎥ b :> (Trn (u ++ ⟨b::v))⎥ >= 2);
        [destruct (c_binding (𝗙 b v));lia|].
      case_in b (prj2 (Trn (u ++ ⟨b :: v))).
      * apply decomposition in I0 as (l1&l2&E&I0);revert I.
        apply split_snd in E as (n&t1&t2&E&->&->);auto;rewrite E in *.
        rewrite rmfstn_in;auto.
        intro I;apply in_split in I as (l1&l2&EL);levi EL;subst;clear EL;
          repeat (simpl||rewrite filter_app||rewrite app_length);simpl.
        -- unfold select at 2 3 6;simpl;simpl_beq.
           destruct_leb ⎢u⎥ ⎢u⎥;[|lia];simpl.
           destruct_leb ⎢u⎥ n;simpl;[lia|].
           cut (⎢u⎥ < n);[lia|].
           apply (@Trn_incr (u ++ ⟨b :: v) _ b _ b l1 [] l2).
           rewrite E;simpl;reflexivity.
        -- exfalso;inversion E1;subst;apply I0.
           rewrite map_app;simpl;simpl_In;simpl;tauto.
        -- replace (select ⎢u⎥ b (⎢u⎥, b)) with true
            by (symmetry;apply select_spec;split;reflexivity).
           replace (select ⎢u⎥ b (n, b)) with true;simpl.
           ++ destruct (select ⎢u⎥ b a);simpl;repeat rewrite app_length;simpl;try lia.
           ++ symmetry;apply select_spec;split;auto.
              cut (⎢u⎥ < n);[lia|].
              apply (@Trn_incr (u ++ ⟨b :: v) _ b _ b t1 (a::w) l2).
              rewrite E;simpl;reflexivity.
      * exfalso;apply I0,in_map_iff;exists (⎢u⎥,b);split;auto.
        eapply rmfstn_decr;eauto.
                     + intro I;apply rmfstn_decr,IHv in I as ->;reflexivity.
    + intro I;apply IHv in I as ->;lia.
Qed.

(** * Correspondence with stacks *)
(** If there is a path labelled with [u|v] from [s1] to [s2], then the first component of [s2] is the trace of [u] after the first component of [s1]. *)
Lemma Tr_step a b s1 s2 : s1 ⊣ a | b ↦ s2 -> prj1 s2 = updTr (prj1 s1) a.
Proof.
  destruct a as [a|a|x];destruct b as [b|b|y];unfold step;try tauto.
  - intros ->;simpl;reflexivity.
  - intros ([(->&A)|(t1&t2&->&A)]&->);simpl.
    + rewrite rmfst_absent,rmfst_notin;auto.
      apply A.
    + repeat rewrite map_app;simpl.
      rewrite rmfst_present,map_app,rmfst_in;auto.
      apply A.
  - intuition subst;reflexivity.
Qed.
Corollary Tr_path u v s1 s2 : s1 ⊣ u | v ⤅ s2 -> prj1 s2 = Tr (prj1 s1) u.
Proof.
  intro P;induction P.
  - unfold Tr;simpl;auto.
  - rewrite IHP;simpl.
    apply Tr_step in H as ->;auto.
Qed.
Corollary Trn_path_snd u v s2 : 
  [] ⊣ u | v ⤅ s2 -> prj1 s2 = prj2 (Trn u).
Proof. rewrite Trn_Tr;intro P;rewrite (Tr_path P);reflexivity. Qed.
(** One can also understand that property as stating that if there is a path labelled with [u|v] from the empty stack to [s], then [s] must be the combination of the trace of [u] with the trace of [v]. *)
Corollary path_Tr s u v : [] ⊣ u | v ⤅ s -> s = (Tr [] u) ⊗ (Tr [] v).
Proof.
  intro P;rewrite combine_split.
  rewrite (Tr_path P).
  apply path_sym,Tr_path in P.
  simpl in P;rewrite flip_proj1 in P;rewrite P;reflexivity.
Qed.
Remark Accepting_path_Tr s u v : [] ⊣ u | v ⤅ s -> s ✓ <-> Tr [] u = Tr [] v.
Proof.
  intro P;pose proof (Tr_path P) as E1.
  apply path_sym,Tr_path in P as E2.
  simpl in E2;rewrite flip_proj1 in E2;simpl in *.
  rewrite <- E1,<-E2;tauto.
Qed.

(** If there is a path labelled with [u|v] from the empty stack to [s], then the first projections of the indexed traces of [u] and [v] coincide. *)
Proposition Trn_path_fst u v s :
  [] ⊣ u | v ⤅ s -> prj1 (Trn u) = prj1 (Trn v).
Proof.
  revert v s;induction u as [|a u] using rev_induction;intros v' s3 P.
  - inversion P;auto. 
  - destruct (nil_or_last v') as [->|(b&v&->)];[inversion P;simpl_words|].
    apply path_decompose_app in P as (s2&P&P2).
    inversion P2;inversion H6;subst;clear P2 H6.
    pose proof (IHu _ _ P) as IH;clear IHu.
    pose proof (Trn_path_snd P) as E1.
    pose proof P as E2;apply path_sym,Trn_path_snd in E2;rewrite flip_proj1 in E2.
    repeat rewrite Trn_add.
    destruct a as [a|a|x];destruct b as [b|b|y];try (unfold step in H5;tauto);simpl.
    + repeat rewrite Trn_aux_fst.
      rewrite (path_length_word P);f_equal;auto.
    + destruct H5 as ([(->&(A1&A2))|(t1&t2&->&(A1&A2))]&_).
      * rewrite E1 in A1;rewrite E2 in A2.
        repeat rewrite rmfstn_notin;auto.
      * clear s3 P;rewrite map_app in *;simpl in *.
        revert IH;symmetry in E1,E2;apply split_snd in E1 as (k&l1&l2&->&E11&E12);auto.
        apply split_snd in E2 as (k'&m1&m2&->&E21&E22);auto.
        rewrite E11 in *;rewrite E21 in *;clear E11 E21.
        repeat rewrite map_app;simpl;intro E;apply length_app_tail in E as (E0&E).
        -- repeat rewrite rmfstn_in,map_app;auto. 
           rewrite E0 in *;inversion E;auto.
        -- simpl;f_equal;transitivity ⎢t2⎥.
           ++ rewrite <- (map_length fst),E12,map_length,map_length;auto.
           ++ rewrite <- (map_length snd),E22,map_length,map_length;auto.
    + apply path_length_word in P;repeat rewrite app_length in P;simpl in P;lia.
Qed.

End s.