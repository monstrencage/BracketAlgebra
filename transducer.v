(** * RIS.transducer : definition and properties of the binding transducer. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export stacks words.

Section s.
  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.
  
(** * Transducer *)
(** ** Definition *)
(** The predicate [s ⊣ l1 | l2 ↦ s'] encodes the transition function of the transducer. It holds when there exists a transition in the transducer from state [s] to state [s'] labelled with letters [l1|l2]. *)
Definition step (s : stack) (l1 l2 : letter) (s' : stack) :=
  match (l1,l2) with
  | (⟨a,⟨b) => s' = (a,b)::s
  | (a⟩,b⟩) => (s ⊨ a ↦ b) /\ s' = s ⊖ (a,b)
  | (var x,var y) => s' = s /\ exists p, y = p∙x /\ forall a, a ∈ ⌊x⌋ -> s ⊨ a ↦ p∙a
  | _ => False
  end.
Notation " s ⊣ l1 | l2 ↦ s' " := (step s l1 l2 s') (at level 80).

(** The predicate [s ⊣ u | v ⤅ s'] encodes paths in the transducer. It holds when there exists a path in the transducer from state [s] to state [s'] labelled with the words [u|v]. *)
Reserved Notation " s ⊣ u | v ⤅ s' " (at level 80).
Inductive path : word -> word -> stack -> stack -> Prop :=
| pathϵ s : s ⊣ [] | [] ⤅ s
| pathl s2 u v l1 l2 s1 s3 :
    s1 ⊣ l1 | l2 ↦ s2 -> s2 ⊣ u | v ⤅ s3 -> s1 ⊣ l1::u | l2::v ⤅ s3
where " s ⊣ u | v ⤅ s' " := (path u v s s').
Hint Constructors path.

(** ** The function [δt]: computing a path in the transducer *)

(** [compatible s u v] returns [true] if and only if there exists [s'] such that [s⊣u|v⤅s'].*)
Fixpoint compatible s u v :=
  match (u,v) with
  | ([],[]) => true
  | ([],_) | (_,[]) => false
  | (⟨a::u,⟨b::v)=> compatible ((a,b)::s) u v
  | (a⟩::u,b⟩::v)=>
    if (pairedb s a b)
    then compatible (s⊖(a,b)) u v
    else false
  | (var x::u,var y::v)=>
    match var_perm' ⌊x⌋ s with
    | None => false
    | Some p => (p∙x =?= y)&&(compatible s u v)
    end
  | (_::_,_::_) => false
  end.


(** If [s⊣u|v⤅s'], then [δt s u v] returns [s']. Otherwise, [δt s u v] returns [[]]. This implies that there is at most one path from [s] labelled with [u|v]. *)
Fixpoint δt s u v :=
  match (u,v) with
  | ([],[]) => s
  | ([],_) | (_,[]) => []
  | (⟨a::u,⟨b::v)=> δt ((a,b)::s) u v
  | (a⟩::u,b⟩::v)=>
    if (pairedb s a b)
    then δt (s⊖(a,b)) u v
    else []
  | (var x::u,var y::v)=>
    match var_perm' ⌊x⌋ s with
    | None => []
    | Some p =>
      if (p∙x =?= y)
      then δt s u v
      else []
    end
  | (_::_,_::_) => []
  end.

Ltac case_var s x y :=
  let p := fresh "p" in
  let e := fresh "e" in
  case_eq (var_perm' ⌊x⌋ s);
  [intros p e;destruct_eqX (p∙x) y|intros e].

(** There is a path from [s1] to [s2] labelled with [u|v] if and only if [u,v] is compatible with [s1] and [s2] is [δt s1 u v]. *)
Theorem δt_compatible_spec s1 u v s2 :
  δt s1 u v = s2 /\ compatible s1 u v = true <-> s1 ⊣ u|v ⤅ s2.
Proof.
  revert v s1 s2;induction u as [|[a|a|x] u];intros [|[b|b|y] v] s1 s2;simpl;
    try (now split;intro h;inversion h;auto).
  - split.
    + intros (->&_);auto.
    + intro P;inversion P;split;reflexivity.
  - rewrite IHu;split;intro p.
    + eapply pathl;eauto;reflexivity.
    + inversion p;subst.
      unfold step in H5;subst;auto.
  - case_paired s1 a b. 
    + rewrite IHu;split;intro P.
      * eapply pathl;eauto;split;auto.
      * inversion P;subst.
        destruct H5 as (h&->);auto.
    + split;[intros (_&F);discriminate|].
      intro P;inversion P;subst.
      destruct H5 as (F&_);tauto.
  - case_var s1 x y.
    + subst;simpl.
      rewrite IHu;split;intro P.
      * eapply pathl;eauto.
        split;[reflexivity|].
        exists p;split;auto.
        intros a Ia;apply (var_perm'_Some e Ia).
      * inversion P as [|? ? ? ? ? ? ? hs P'];subst.
         destruct hs as (->&_);tauto.
    + split;[intros (_&F);discriminate|].
      intro P;inversion P as [|? ? ? ? ? ? ? hs P'];subst;exfalso.
      destruct hs as (->&q&->&h).
      apply var_perm'_spec in h as (p'&e'&h).
      rewrite e in e';inversion e';subst;clear e'.
      apply N,support_eq_action_eq;intros a Ia;symmetry;apply h,Ia.
    + split;[intros (_&F);discriminate|].
      intro P;inversion P as [|? ? ? ? ? ? ? hs P'];subst;exfalso.
      destruct hs as (->&q&->&h).
      apply var_perm'_spec in h as (p'&e'&_).
      rewrite e in e';discriminate.
Qed.

Corollary δt_path s u v : compatible s u v = true <-> s ⊣ u|v ⤅ δt s u v.
Proof. rewrite <- δt_compatible_spec;tauto. Qed.

(** When [u,v] is not compatible with [s], we set [δt s u v] to be the empty list. This choice of a default value is arbitrary. *)
Lemma compatible_false s u v : compatible s u v = false -> δt s u v = [].
Proof.
  revert s v;induction u as [|[a|a|x] u];intros s [|[b|b|y] v];simpl;discriminate || auto.
  - destruct (pairedb s a b);auto.
  - case_var s x y;auto.
Qed.

(** ** Elementary properties *)
(** It is straightforward that a path of length one is exactly a step. *)
Remark path_single_letter s1 l1 l2 s2 :
  s1 ⊣ [l1] | [l2] ⤅ s2 <-> s1 ⊣ l1 | l2 ↦ s2.
Proof.
  split;intro P;[inversion P as [|? ? ? ? ? ? ? h1 h2];inversion h2;subst;apply h1
                |apply (pathl P),pathϵ].
Qed.

(** The transition predicate commutes with permutation actions. *)
Fact nom_step p s1 s2 l1 l2 :
  s1 ⊣ l1 | l2 ↦ s2 -> p ∙ s1 ⊣ p∙l1 | p∙l2 ↦ p∙s2.
Proof.
  destruct l1 as [a|a|x];destruct l2 as [b|b|y];unfold step;simpl;auto.
  - intros ->;reflexivity.
  - replace (p∙a,p∙b) with (p∙(a,b)) by reflexivity.
    intros (P&->);setoid_rewrite rmfst_perm.
    rewrite act_pinv_p;split;auto.
    apply paired_perm;setoid_rewrite act_pinv_p;auto.
  - intros (->&q&->&P);split;auto.
    exists (p++q++p∗);split.
    + repeat rewrite action_compose.
      rewrite app_ass,app_ass,perm_pinv_p_eq_nil,app_nil_r;auto.
    + intro a;rewrite support_action,In_act_lists.
      intro I;apply P in I;clear P.
      apply paired_perm.
      rewrite action_compose,<-app_ass,perm_pinv_p_eq_nil;simpl;rewrite <- action_compose;auto.
Qed.

Corollary nom_path p s1 s2 u v :
  s1 ⊣ u | v ⤅ s2 -> p ∙ s1 ⊣ p∙u | p∙v ⤅ p∙s2.
Proof.
  intro P;induction P;simpl;auto.
  apply nom_step with (p:=p) in H.
  pose proof (pathl H IHP) as IH;apply IH.
Qed.

Corollary nom_compatible p s u v :
  compatible s u v = compatible (p∙s) (p∙u) (p∙v).
Proof.
  apply eq_iff_eq_true.
  cut (forall p s u v, compatible s u v = true -> compatible (p ∙ s) (p ∙ u) (p ∙ v) = true).
  - intros h;split;auto.
    intro E;apply (h (p∗)) in E.
    repeat rewrite act_pinv_p in E;auto.
  - clear;intros p s u v E.
    apply δt_path in E;apply nom_path with (p:=p) in E.
    apply δt_compatible_spec in E;tauto.
Qed.

Corollary nom_δt p s u v :
  p∙(δt s u v) = δt (p∙s) (p∙u) (p∙v).
Proof.
  case_eq (compatible s u v).
  - rewrite δt_path;intro P.
    apply nom_path with (p:=p) in P.
    apply δt_compatible_spec in P as (P&_);auto.
  - intro h;rewrite (compatible_false h).
    rewrite nom_compatible with (p:=p) in h;rewrite (compatible_false h).
    reflexivity.
Qed.
    
(** If [s] is accepting, then for any word [u] there is an accepting stack [s'] such that [s ⊣ u | u ⤅ s']. *)
Lemma path_id_Accepting u : forall s, s ✓ -> (δt s u u) ✓.
Proof.
  induction u as [|[a|a|x]u];intros s A;simpl;auto.
  - apply IHu;simpl;rewrite A;auto.
  - destruct (pairedb s a a);auto.
    apply IHu,Accepting_rmfst,A.
  - case_var s x x;auto.
Qed.

Lemma path_id_compatible u : forall s, s ✓ -> compatible s u u = true.
Proof.
  induction u as [|[a|a|x]u];intros s A;simpl;auto.
  - apply IHu;simpl;rewrite A;reflexivity.
  - assert (E:a=a) by reflexivity.
    rewrite <-(paired_Accepting _ _ A),pairedb_spec in E;rewrite E.
    apply IHu,Accepting_rmfst,A.
  - case_var s x x.
    + apply IHu;auto.
    + exfalso.
      apply N,action_invariant,map_eq_id.
      cut (forall a, a ∈ ⌊x⌋ -> s ⊨ a ↦ [] ∙ a).
      * rewrite var_perm'_spec;intros (q&e'&h).
        rewrite e' in e;inversion e;subst;clear e.
        setoid_rewrite act_nil in h.
        intros a Ia;symmetry;apply h,Ia.
      * setoid_rewrite act_nil.
        intros a _;apply paired_Accepting;tauto.
    + exfalso;apply var_perm'_None in e as (a&Ia&F);apply (F a),paired_Accepting;tauto.
Qed.

Corollary path_id s u : s ✓ -> exists s', s'✓ /\ s ⊣ u | u ⤅ s'.
Proof.
  setoid_rewrite <- δt_compatible_spec;intro A;rewrite (path_id_compatible u A).
  exists (δt s u u);split;auto;apply path_id_Accepting,A.
Qed.
                                                                            
(** If there is a path from labelled with [u|v], then [u] and [v] have the same length. *)
Lemma path_length_word u v s1 s2 : s1 ⊣ u | v ⤅ s2 -> ⎢u⎥ = ⎢v⎥.
Proof. intro P;induction P;solve_length. Qed.

(** If [u1] and [v1] have the same length, then [u1++u2,v1++v2] is compatible with [s] if and only if [u1,v1] is compatible with [s] and [u2,v2] is compatible with [δt s u1 v1]. *)
Proposition compatible_app u1 u2 v1 v2 s :
  ⎢u1⎥ = ⎢v1⎥ ->
  compatible s (u1++u2) (v1++v2) = (compatible s u1 v1)
                                     && compatible (δt s u1 v1) u2 v2.
Proof.
  revert v1 s;induction u1 as [|[a|a|x] u1];intros [|[b|b|y]v1] s1 L;simpl in *;lia||auto.
  - case_paired s1 a b;simpl;auto.
  - case_var s1 x y;simpl;auto.
Qed.

(** If [u1,v1] is compatible with [s] then [δt s (u1++u2) (v1++v2)] may be computed as [δt (δt s u1 v1) u2 v2]. *)
Proposition δt_app u1 u2 v1 v2 s :
  compatible s u1 v1 = true -> δt s (u1++u2) (v1++v2) = δt (δt s u1 v1) u2 v2.
Proof.
  revert v1 s;induction u1 as [|[a|a|x] u1];intros [|[b|b|y]v1] s1 L;simpl in *;discriminate||auto.
  - revert L;case_paired s1 a b;simpl;discriminate||auto.
  - revert L;case_var s1 x y;simpl;discriminate||auto.
Qed.

(** If there is a path labelled with [u1++u2|v1++v2], and if [u1] and [v1] have the same length, then it can be factored as a path labelled with [u1|v1] followed by one with label [u2|v2]. *)
Corollary path_decompose_app u1 u2 v1 v2 s1 s2 :
  (s1 ⊣ u1++u2 | v1++v2 ⤅ s2) -> ⎢u1⎥ = ⎢v1⎥ ->
  exists s3, s1 ⊣ u1 | v1  ⤅ s3 /\ s3 ⊣ u2 | v2  ⤅ s2.
Proof.
  setoid_rewrite <- δt_compatible_spec.
  intros (<-&C) L;rewrite compatible_app,andb_true_iff in C;auto.
  exists (δt s1 u1 v1);rewrite δt_app;tauto.
Qed.

Corollary path_letter u l v s1 s2 :
  (s1 ⊣ u++[l] | v ⤅ s2) ->
  exists v' l' s3, v = v' ++ [l'] /\ s1 ⊣ u | v' ⤅ s3 /\ s3 ⊣ l | l' ↦ s2.
Proof.
  intro P;destruct (nil_or_last v) as [->|(l'&v'&->)].
  + inversion P;simpl_words.
  + apply path_decompose_app in P as (s3&P1&P2);[|apply path_length_word in P;solve_length].
    exists v',l',s3;simpl;repeat split;auto.
    inversion P2;inversion H6;subst;auto.
Qed.

(** If we know [s2] to be accepting, we may simplify [image (s1++s2) a], [var_perm x (s1++s2)], [pairedb (s1++s2) a b], [compatible (s1++s2) u v]. Also, [δt (s1++s2) u v] is accepting if and only if [δt s1 u v] is. *)
Proposition image_app_Accepting s1 s2 :
  s2 ✓ -> forall a, image (s1++s2) a = image s1 a.
Proof.
  induction s1 as [|(a,b)s1];intros Acc c;simpl;auto.
  - apply image_spec,paired_Accepting;auto.
  - destruct_eqX c a;auto.
Qed.

Corollary var_perm_app_Accepting s1 s2 x :
  s2 ✓ -> var_perm x (s1++s2) = var_perm x s1 .
Proof. unfold var_perm; intro Acc;rewrite (map_ext _ _ (image_app_Accepting _ Acc));auto. Qed.

Lemma pairedb_app_Accepting s1 s2 :
  s2 ✓ -> forall a b, pairedb (s1++s2) a b = pairedb s1 a b.
Proof.
  intros Acc a b;case_paired s1 a b;case_paired (s1++s2) a b;auto.
  - exfalso;apply hp0,paired_app.
    rewrite (paired_Accepting _ _ Acc).
    pose proof hp as [(->&A)|(?&?&->&_)];simpl_In;auto.
  - exfalso;apply hp;apply paired_app in hp0 as [(E&_)|(A&hp0)];auto.
    apply (paired_Accepting _ _ Acc) in hp0 as ->.
    left;split;auto.
Qed.

Proposition compatible_app_Accepting s1 s2 u v :
  s2 ✓ -> compatible (s1++s2) u v = compatible s1 u v.
Proof.
  revert v s1 s2;induction u as [|[a|a|x] u];intros [|[b|b|y]v] s1 s2 Acc;simpl in *;auto.
  - repeat rewrite app_comm_cons;apply IHu,Acc.
  - rewrite pairedb_app_Accepting;auto;case_paired s1 a b;auto.
    pose proof hp as hp';
      rewrite pairedb_spec,<-(pairedb_app_Accepting _ Acc),<-pairedb_spec in hp'.
    destruct (rmfst_app_dec_stacks hp') as [(t1&t2&->&h&->)|[(t1&t2&->&h&->)|(->&h&->)]].
    + rewrite rmfst_present,<-app_ass;auto.
    + apply absent_app in h as (h1&h2);rewrite (rmfst_absent h1);apply IHu.
      repeat rewrite map_app in *;simpl in *.
      apply length_app in Acc as (->&h);[|solve_length].
      inversion h;auto.
    + apply absent_app in h as (h1&h2);rewrite (rmfst_absent h1);apply IHu;auto.
  - rewrite IHu by tauto.
    case_var s1 x y;case_var (s1++s2) x y;try reflexivity;simpl;exfalso.
    + apply N;rewrite <- E;apply support_eq_action_eq.
      intros a Ia.
      pose proof (var_perm'_Some e Ia) as p1.
      pose proof (var_perm'_Some e0 Ia) as p2.
      rewrite pairedb_spec,(pairedb_app_Accepting _ Acc),<-pairedb_spec in p2.
      apply (paired_inj p2 p1);reflexivity.
    + apply var_perm'_None in e0 as (a&Ia&h).
      pose proof (var_perm'_Some e Ia) as p1.
      apply (h (p∙a)).
      rewrite pairedb_spec,(pairedb_app_Accepting _ Acc),<-pairedb_spec;tauto.
    + apply N;rewrite <- E;apply support_eq_action_eq.
      intros a Ia.
      pose proof (var_perm'_Some e Ia) as p1.
      pose proof (var_perm'_Some e0 Ia) as p2.
      rewrite pairedb_spec,(pairedb_app_Accepting _ Acc),<-pairedb_spec in p2.
      apply (paired_inj p1 p2);reflexivity.
    + apply var_perm'_None in e as (a&Ia&h).
      pose proof (var_perm'_Some e0 Ia) as p1.
      apply (h (p∙a)).
      rewrite pairedb_spec,<-(pairedb_app_Accepting _ Acc),<-pairedb_spec;tauto.
Qed.

Proposition δt_app_Accepting s1 s2 u v :
  s2 ✓ -> δt (s1++s2) u v ✓ <-> δt s1 u v ✓.
Proof.
  revert v s1 s2;induction u as [|[a|a|x] u];intros [|[b|b|y]v] s1 s2 Acc;simpl in *;try tauto.
  - rewrite Accepting_app,Acc;tauto.
  - repeat rewrite app_comm_cons;rewrite IHu;auto;tauto.
  - rewrite pairedb_app_Accepting;auto.
    case_paired s1 a b;simpl;[|tauto].
    pose proof hp as hp';rewrite pairedb_spec,<-(pairedb_app_Accepting _ Acc),<-pairedb_spec in hp'.
    destruct (rmfst_app_dec_stacks hp') as [(t1&t2&->&h&->)|[(t1&t2&->&h&->)|(->&h&->)]].
    + rewrite rmfst_present,<-app_ass;auto.
    + apply absent_app in h as (h1&h2);rewrite (rmfst_absent h1);apply IHu.
      repeat rewrite map_app in *;simpl in *.
      apply length_app in Acc as (->&h);[|solve_length].
      inversion h;auto.
    + apply absent_app in h as (h1&h2);rewrite (rmfst_absent h1);apply IHu;auto.
  - pose proof (compatible_app_Accepting s1 [var x] [var y] Acc) as e.
    revert e;simpl.
    case_var s1 x y;case_var (s1++s2) x y;try discriminate||reflexivity;simpl.
    intros _;apply IHu,Acc.
Qed.

Corollary path_app_Accepting s1 s2 u v s3 :
  s2 ✓ -> s1 ⊣ u | v ⤅ s3 -> exists s4, s1++s2 ⊣ u | v ⤅ s4 /\ (s3 ✓ -> s4 ✓).
Proof.
  setoid_rewrite <- δt_compatible_spec.
  intros A (<-&C);exists (δt (s1++s2) u v);split;[split|];auto.
  - rewrite compatible_app_Accepting,C;auto.
  - rewrite δt_app_Accepting;auto.
Qed.
           
(** We can flip a path with label [u|v] into a path with label [v|u]. *)
Lemma step_sym a b s1 s2 : s1 ⊣ a | b ↦ s2 -> s1` ⊣ b | a ↦ s2`.
Proof.
  intro h;destruct a as [a|a|x];destruct b as [b|b|y];unfold step in *;try tauto.
  + rewrite h;simpl;auto.
  + rewrite <- paired_flip,rmfst_flip.
    destruct h as (P&->);auto.
  + destruct h as (->&p&->&E).
    split;auto;exists (p∗);split.
    * rewrite action_compose,perm_pinv_p_eq_nil,act_nil;auto.
    * intros a I;rewrite <- paired_flip,<-(act_p_pinv p).
      apply E,In_act_lists,support_action,I.
Qed.

Corollary path_sym s u v s' : s ⊣ u | v ⤅ s' <-> (s`) ⊣ v | u ⤅ (s'`).
Proof.
  revert u v s s';cut (forall u s v s', s ⊣ u | v ⤅ s' -> (s`) ⊣ v | u ⤅ (s'`));
    [intros h u v s s';split;[apply h|intro p;apply h in p;repeat rewrite flip_involutive in p;auto]
    |intros u s v s' P].
  induction P;simpl;eauto.
  apply step_sym in H;eauto.
Qed.

Corollary compatible_flip s u v : compatible (s`) u v = compatible s v u.
Proof.
  case_eq (compatible s v u).
  - rewrite δt_path;intro P;apply path_sym,δt_compatible_spec in P;tauto.
  - intro h;case_eq (compatible (s`) u v);auto.
    rewrite δt_path;intro P;apply path_sym,δt_compatible_spec in P as (_&C).
    rewrite flip_involutive in C;rewrite C in h;discriminate.
Qed.

Corollary δt_flip s u v : δt (s`) u v = (δt s v u)`.
Proof.
  case_eq (compatible s v u).
  - rewrite δt_path;intro P;apply path_sym,δt_compatible_spec in P;tauto.
  - intro C;rewrite (compatible_false C);rewrite <- compatible_flip in C;rewrite (compatible_false C).
    reflexivity.
Qed.
  
(** We can compose a path with label [u|v] with a path with label [v|w] to get a path with label [u|w], if their starting points are compatible. *)
Lemma step_mix l1 l2 l3 s1 s2 s3 s4 :
  prj2 s1 = prj1 s3 -> s1 ⊣ l1 | l2 ↦ s2 -> s3 ⊣ l2 | l3 ↦ s4 ->
  (s1 ⋈ s3) ⊣ l1 | l3 ↦ (s2 ⋈ s4) /\ prj2 s2 = prj1 s4.
Proof.
  destruct l1 as [a|a|x];destruct l2 as [b|b|y];destruct l3 as [c|c|z];unfold step;try tauto.
  - intros E -> -> ;simpl;split;auto;f_equal;auto.
  - intros E1 (P1&E2) (P2&E3);pose proof (paired_mix E1 P1 P2) as (h1&h2&h3);subst;auto.
  - intros len (->&p&->&hp) (->&q&->&hq);repeat split;auto.
    exists (q++p);rewrite action_compose.
    split;auto;intros a I1.
    eapply paired_mix;auto.
    rewrite <- action_compose;apply hq.
    rewrite support_action,In_act_lists,inverse_comp_l;auto.
Qed.

Corollary path_mix u v w s1 s2 s3 s4 :
  prj2 s1 = prj1 s3 -> (s1 ⊣ u | v ⤅ s2) -> (s3 ⊣ v | w ⤅ s4) ->
  prj2 s2 = prj1 s4 /\ (s1 ⋈ s3) ⊣ u | w ⤅ (s2 ⋈ s4).
Proof.
  intros E P;revert w s3 s4 E;induction P;intros w' s1' s3' E1 P'.
  - inversion P';subst;auto.
  - inversion P';subst;auto;clear P'.
    pose proof (step_mix E1 H H2) as (S'&E2).
    pose proof (IHP _ _ _ E2 H6) as (->&P');eauto.    
Qed.

(** Notice that paths are deterministic, in the sense that given a starting point [s] and a label [u|v], there is at most one stack [s'] such that [s⊣ u | v ⤅s']. *)
Remark step_det a b s s1 s2 : s ⊣ a | b ↦ s1 -> s ⊣ a | b ↦ s2 -> s1 = s2.
Proof. destruct a;destruct b;unfold step;try tauto|| intuition congruence. Qed.

Remark path_det u v s s1 s2 : s ⊣ u | v ⤅ s1 -> s ⊣ u | v ⤅ s2 -> s1 = s2.
Proof.
  intro P;revert s2;induction P;intros s' P';inversion P';subst;clear P';auto.
  apply (step_det H) in H6;subst;eauto.
Qed.

(** We can compose a path from [s1] to [s2] and one from [s2] to [s3] to get a path from [s1] to [s3]. *)
Lemma path_app u1 u2 v1 v2 s1 s2 s3 :
  s1 ⊣ u1 | v1 ⤅ s2 -> s2 ⊣ u2 | v2 ⤅ s3 -> s1 ⊣ u1++u2 | v1++v2 ⤅ s3.
Proof. intros P1 P2;induction P1;auto;apply IHP1 in P2;simpl;eauto. Qed.

(** ** Binding power *)
(** If [s ⊣ u | v ⤅ s'], we can relate the number of occurrences of atoms in [s] and [s'] with the binding power of [u] and [v] with respect to [a]. *)
Proposition stack_binding a u s s' :
  (s ⊣ u | u ⤅ s') ->
  nb a (prj1 s') = (nb a (prj1 s) - d_binding (𝗙 a u)) + c_binding (𝗙 a u).
Proof.
  intro P;assert (exists v, v = u /\ s ⊣ u | v ⤅ s') as (v&E0&P') by (exists u;split;auto).
  clear P;induction P';simpl in *;auto.
  - unfold 𝗙;simpl_binding; lia.
  - inversion E0 as [[E1 E]];apply IHP' in E as -> ;subst;clear E0 IHP';simpl_binding.
    generalize (𝗙 a u);clear u v P' s3;intros ((n,m),p);simpl_binding.
    destruct l1 as [b|b|x];unfold step in H;simpl.
    + subst;unfold_eqX;simpl;simpl_beq;simpl.
      * destruct n;lia.
      * lia.
    + destruct H as ([(_&A)|(t1&t2&->&A)]&->); [rewrite rmfst_absent|rewrite rmfst_present];auto;
        destruct A as (A&_);apply nb_not_In in A;unfold_eqX;simpl_binding;
          repeat rewrite map_app,filter_app,app_length;simpl;simpl_eqX;simpl;lia.
    + destruct H as (->&_);lia.
Qed.

Corollary stack_binding_both u v s s' :
  (s ⊣ u | v ⤅ s') ->
  forall a,
    nb a (prj1 s') = (nb a (prj1 s) - d_binding (𝗙 a u)) + c_binding (𝗙 a u)
    /\
    nb a (prj2 s') = (nb a (prj2 s) - d_binding (𝗙 a v)) + c_binding (𝗙 a v).
Proof.
  intros P a;pose proof P as P';apply path_sym in P';split.
  - apply (path_mix (eq_sym (@flip_proj1 _ _ s)) P) in P' as (E&P').
    apply stack_binding with (a:=a) in P'.
    rewrite mix_fst,mix_fst in P';auto.
    + unfold flip;rewrite map_length;auto.
    + unfold flip;rewrite map_length;auto.
  - apply (path_mix (@flip_proj2 _ _ s) P') in P as (E&P).
    apply stack_binding with (a:=a) in P.
    rewrite mix_fst,flip_proj1,mix_fst,flip_proj1 in P;auto.
    + unfold flip;rewrite map_length;auto.
    + unfold flip;rewrite map_length;auto.
Qed.

(** Using these, we can compute the size of the target stack from the c-binding power of [u]. *)
Lemma size_stack u v s :
  [] ⊣ u | v ⤅ s -> ⎢s⎥ = sum (fun a => c_binding (𝗙 a u)) {{⌊u⌋}}.
Proof.
  intro P.
  transitivity (sum (fun a => nb a [] - d_binding (𝗙 a u) + c_binding (𝗙 a u)) {{⌊ u ⌋}}).
  - transitivity (sum (fun a => nb a (prj1 s)) {{⌊u⌋}}).
    + rewrite <- length_sum_filter;auto.
      * symmetry;apply map_length.
      * revert v s P;induction u as [|l u] using rev_induction;simpl;intros v s P.
        -- inversion P;reflexivity.
        -- apply path_letter in P as (v'&l'&s'&->&P&hs).
           apply IHu in P;rewrite undup_equivalent,(support_list_app u [l]),
                          <-(undup_equivalent ⌊u⌋),<-P.
           unfold support,SupportList,support;simpl;rewrite app_nil_r,undup_equivalent.
           clear P IHu u;destruct l as [a|a|x];destruct l' as [b|b|y];unfold step in hs;simpl;
             try tauto.
           ++ subst;simpl;intro c;simpl_In;simpl;tauto.
           ++ destruct hs as ([(->&A)|(s1&s2&->&A)]&->).
              ** rewrite rmfst_absent;auto;intro;simpl_In;tauto.
              ** rewrite (rmfst_present _ A);repeat rewrite map_app;intro;simpl_In;simpl; tauto.
           ++ destruct hs as (->&_);intro;simpl_In;tauto.
      * apply NoDup_undup.
    + apply sum_ext;intro.
      apply (stack_binding_both P x).
  - apply sum_ext;simpl;auto.
Qed.

(** ** Applying permutations on one component *)
(** We introduce a new operation. [p ⧓ s] is the stack obtained by replacing every pair [(a,b)] in [s] with [(a,p∙b)]. *)
Definition mixp p s : stack:= (prj1 s) ⊗ (p∙prj2 s).
Infix "⧓" := mixp (at level 50).

Remark mixp_fst p l : prj1 (p ⧓ l) = prj1 l.
Proof. unfold mixp;induction l;simpl;auto;f_equal;auto. Qed.

Remark mixp_snd p l : prj2 (p ⧓ l) = prj2 (p∙l).
Proof. unfold mixp,act,act_lists;induction l;simpl;auto;f_equal;auto. Qed.

Remark mixp_snd_bis p l : prj2 (p ⧓ l) = p∙prj2 l.
Proof. unfold mixp,act,act_lists;induction l;simpl;auto;f_equal;auto. Qed.

Remark mixp_cons p a b l : p ⧓ ((a,b)::l) = (a,p∙b)::p ⧓ l.
Proof. reflexivity. Qed.

Remark mixp_app p l m : p ⧓ (l++m) = p ⧓ l ++ p ⧓ m.
Proof.
  unfold mixp;induction l as [|a l];simpl;auto.
  f_equal;auto.
Qed.

Remark mixp_absent p l a b : absent (p⧓l) a b <-> absent l a (p∗∙b).
Proof.
  unfold absent;rewrite mixp_fst,mixp_snd.
  replace (prj2 (p∙l)) with (p ∙ prj2 l)
    by (etransitivity;[|etransitivity];[apply map_map| |symmetry;apply map_map];simpl;auto).
  rewrite In_act_lists;tauto.
Qed.

(** [min_occ a u] is equal to [d_binding (𝗙 a u)] if the boolean component of [𝗙 a u] is [false], and [d_binding (𝗙 a u)+1] otherwise. *)
Definition min_occ a v :=
  match 𝗙 a v with (m,true,_) => S m | (m,_,_) => m end.

Remark min_occ_app a u v : min_occ a u <= min_occ a (u++v).
Proof.
  unfold min_occ;rewrite 𝗙_app.
  destruct (𝗙 a u) as ((n1&b1)&m1); destruct (𝗙 a v) as ((n2&b2)&m2).
  unfold prod_binding;destruct_ltb m1 n2;[destruct_ltb n2 m1|];destruct b1;destruct b2;simpl;lia.
Qed.

(** This is the technical lemma needed to prove that the law [αα] holds for stacks. More precisely, we want to show that if [b #α u] and [a #α u] then there is a path from the empty stack to some accepting stack labelled with [u | [(a,b)]∙u]. We generalise the statement by changing [a,b #α u] with a permutation [p] such that [forall a, ~ a #α u -> p ∙ a = a]. 

Intuitively, one might think that the following holds: [s ⊣ u | v ⤅ s' -> p ⧓ s ⊣ u | p∙v ⤅ p⧓s']. Unfortunately, this is not true in general, consider for instance [[] ⊣ a⟩ | a⟩ ⤅ []]. 

For this reason we need to require that [forall a, ~ a #α v -> p ∙ a = a]. However, while the statement becomes true in this case, it is not suitable for induction. Thus we assume the stronger condition 
[forall a, p ∙ a <> a -> min_occ a v <= nb a (prj2 s)].
*)
Lemma perm_path_mixp p u v s s' :
  (forall a, p ∙ a <> a -> min_occ a v <= nb a (prj2 s)) -> (s ⊣ u | v ⤅ s') ->
  p ⧓ s ⊣ u | p∙v ⤅ p⧓s'.
Proof.
  revert v s';induction u as [|l u] using rev_induction;intros v' s' B P.
  - inversion P;subst;auto.
  - apply path_letter in P as (v&l'&s''&->&P&hs).
    setoid_rewrite act_lists_app;eapply path_app.
    + apply IHu;[|eauto];intros b N;etransitivity;[|apply B;auto];apply min_occ_app.
    + eapply pathl;auto using pathϵ;pose proof (stack_binding_both P) as B'.
      destruct l as [a|a|x];destruct l' as [b|b|y];unfold step in hs;try tauto.
      * subst;reflexivity.
      * destruct hs as ([(->&A)|(t1&t2&->&A)]&->);
          [rewrite (rmfst_absent A)|rewrite (rmfst_present _ A)].
        -- cut (p∙a=a).
           ++ intro Ea; split;[left;split;auto|rewrite Ea;rewrite rmfst_absent;auto];
                rewrite mixp_absent;rewrite <- Ea at 2;rewrite inverse_comp_l;auto.
           ++ destruct_eqX (p∙a) a;auto.
              exfalso;apply B in N.
              pose proof (B' a) as (_&E').
              destruct A as (_&A);rewrite nb_not_In in A.
              revert N;unfold min_occ;rewrite 𝗙_add;simpl;simpl_beq.
              destruct (𝗙 a v) as ((?,?),[|[]]);simpl in *;rewrite d_binding_simpl in E';
                destruct n;simpl in *;lia.
        -- repeat rewrite mixp_app;rewrite mixp_cons.
           split;[right;exists (p⧓t1),(p⧓t2); split|rewrite rmfst_present];auto;
           apply mixp_absent;rewrite inverse_comp_l;auto.
      * destruct hs as (->&q&->&S);split;auto.
        exists (p++q);rewrite action_compose;split;auto.
        intros a I;pose proof I as Ia.
        apply S in I as [(Ea&A)|(t1&t2&->&A)].
        -- left;cut (p∙a=a).
           ++ rewrite <-action_compose,Ea;intro Ea'; split;auto.
              rewrite mixp_absent;rewrite <- Ea' at 2;rewrite inverse_comp_l;auto.
           ++ destruct_eqX (p∙a) a;auto.
              exfalso;apply B in N.
              pose proof (B' a) as (_&E').
              destruct A as (_&A);rewrite nb_not_In in A.
              revert N;unfold min_occ;rewrite 𝗙_add;simpl.
              rewrite <- perm_bij with (p0:=q∗),inverse_comp_l in Ea.
              rewrite Ea, <-In_act_lists, <-support_action, <-inb_spec in Ia;rewrite Ia.
              destruct (𝗙 a v) as ((?,?),[]);simpl in *;rewrite d_binding_simpl in E';
                destruct n;destruct b;simpl;lia.
        -- right;exists (p⧓t1),(p⧓t2).
           rewrite mixp_app,mixp_cons,action_compose;split;auto.
           rewrite mixp_absent,action_compose, <-app_ass,perm_pinv_p_eq_nil;simpl;auto.
Qed.

Corollary αfresh_perm_path p u v s s' :
  (forall a, ~ a #α v -> p ∙ a = a) -> s ⊣ u | v ⤅ s' -> p ⧓ s ⊣ u | p∙v ⤅ p ⧓ s'.
Proof.
  intros h P;apply perm_path_mixp;auto.
  intros a h';cut (a#α v).
  - intro E; unfold min_occ;rewrite E in *;lia.
  - unfold fresh__α;destruct_eqX (𝗙 a v) ε;auto.
    apply h in N;tauto.
Qed.  

Corollary αfresh_perm_path_nil p u :
  (forall a, ~ a #α u -> p ∙ a = a) -> exists s, [] ⊣ u | p∙u ⤅ s /\ s ✓.
Proof.
  intros h;pose proof (path_id u Accepting_nil) as (l&A&E).
  pose proof (αfresh_perm_path h E) as P;exists (p⧓l);split;auto.
  rewrite combine_split in *.
  rewrite mixp_fst,combine_fst;
    [|unfold mixp;repeat rewrite map_length||rewrite combine_length;solve_length].
  rewrite mixp_snd_bis,combine_snd,A;[|solve_length].
  symmetry;apply action_invariant,map_eq_id.
  intros a I;apply h.
  rewrite support_list_atoms, nb_In in I.
  apply (stack_binding a) in E;simpl in E.
  rewrite <- A,E in I.
  intros E';rewrite E' in I;simpl in I;lia.
Qed.

(** * Main result *)
(** ** Completeness *)
(** It is now fairly routine to check that whenever [u] and [v] are alpha-equivalent, there is a path labelled with [u|v] from the empty stack to some accepting stack. *)
Theorem αequiv_path u v : u ≡ v -> exists s, [] ⊣ u | v ⤅ s /\ s ✓.
Proof.
  intro E;induction E as [u v w E1 (s1&P1&A1) E2 (s2&P2&A2)
                         | | u v l E (s&P&A) | u v l E (s&P&A) | a b u F B ].
  - exists (s1 ⋈ s2); assert (E:prj2 (@nil (atom*atom)) = prj1 (@nil (atom*atom))) by reflexivity.
    pose proof (path_mix E P1 P2) as (E'&P);split;auto.
    rewrite mix_snd,mix_fst;auto using proj_length;congruence.
  - exists [];split;auto using pathϵ.
  - cut (exists s', s⊣l|l↦s' /\ s' ✓);
      [intros (s'&hs&A');exists s';split;auto;eapply (path_app P);eauto|clear P u v E].
    destruct (path_id [l] A) as (s'&Acc&P).
    inversion P as [|s1 ? ? ? ? s2 s3 h P'];subst;inversion P' as [|];subst;clear P P';eauto.
  - destruct l as [a|a|x].
    + revert P;setoid_rewrite <- δt_compatible_spec.
      intros (<-&C);eexists;split;[split;[eauto|]|];simpl.
      * rewrite <- compatible_app_Accepting with (s2:=[(a,a)]) in C;simpl;auto.
      * rewrite <- (app_nil_l [(a,a)]),δt_app_Accepting;auto.
    + exists s;split;auto.
      eapply pathl;[|apply P].
      split;[left|];repeat split;auto.
    + exists s;split;[eapply pathl;[|apply P]|tauto].
      apply path_single_letter.
      replace [] with (δt [] [var x] [var x]) at 2;[apply δt_path|];simpl;[rewrite andb_true_r|];
      rewrite act_nil; simpl_beq;reflexivity.
  - assert (E: forall c, ~ c #α (⟨a :: u ++ [a⟩]) -> [(a, b)] ∙ c = c).
    + intros c I;apply elements_inv_act_atom;simpl.
      intros [<-|[<-|?]];try tauto;apply I;clear I.
      * unfold fresh__α,balanced in *.
        rewrite 𝗙_cons,𝗙_add;simpl;simpl_beq.
        destruct (𝗙 a u) as (([],?),[]);simpl in *;rewrite d_binding_simpl in *;try lia.
        reflexivity.
      * unfold fresh__α;rewrite 𝗙_cons,𝗙_add,F;simpl.
        destruct_eqX b a;reflexivity.
    + assert (a#α (⟨a :: u ++ [a⟩]) /\ b #α (⟨a :: u ++ [a⟩])) as (Fa&Fb).
      * unfold fresh__α;destruct_eqX b a;simpl_binding;rewrite F;repeat split;simpl;
          try reflexivity.
        unfold balanced in B;destruct (𝗙 a u) as ((x&y)&z);simpl_binding in *.
        destruct B as (->&->);reflexivity.
      * pose proof (αfresh_perm_path_nil E) as (s&P&A);exists s;split;auto.
        setoid_rewrite (act_lists_cons _ ( ⟨a ) ) in P.
        rewrite act_lists_app in P.
        unfold act at 1 3 in P;simpl in P.
        unfold act at 3 in P;simpl in P.
        replace ([(a, b)] ∙ a) with b in P by (unfold act;simpl;destruct_eqX b a;auto).
        apply P.
Qed.

(** ** Soundness *)
(** To prove completeness, we will proceed by induction on the length of the path, focusing on the last step:
    - if [[]⊣[]|[]⤅[]], then [[]≡[]];
    - if [[] ⊣ u|v ⤅ s ⊣ l|l' ↦ s'] and [s'] is accepting, then the letters [l,l'] can be:
      - [⟨a,⟨b], but because [s'] is accepting we deduce that [a=b] and [s'] is accepting;
      - [var x,var y], with [s=s'], and because [s'] is accepting we deduce that [var x=var y];
      - [a⟩,b⟩].
      In the first two case, we have [l=l'] and by induction [u≡v], thus we deduce [u++l≡v++l'].
      
   The last case is more subtle: we need to show that if [a<>b] and if there is path for the empty stack to [s] labelled with [u++[a⟩] | v++[b⟩]], then we can decompose [u] and [v] as follows:
    - [u=u1++⟨a::u2] and [v=v1++⟨b::v2], where [u1] and [v1] have the same length;
    - [a ⋄ u2] and [b ⋄ v2].
    However, the statements [a ⋄ u2] and [b ⋄ v2] are not stable by prefixes, meaning that this statement is too weak to be provable by a direct induction. Therefore we start by proving the following technical lemma.
*)
Lemma path_stack_decompose_aux u v a b t1 t2 :
  ([] ⊣ u | v ⤅ t1++(a,b)::t2) ->
  exists u1 u2 v1 v2, u=u1++⟨a::u2
                 /\ v=v1++⟨b::v2
                 /\ ⎢u1⎥ = ⎢v1⎥
                 /\ nb a (prj1 t1) = c_binding (𝗙 a u2)
                 /\ nb b (prj2 t1) = c_binding (𝗙 b v2)
                 /\ nb a (prj1 t2) = c_binding (𝗙 a u1)
                 /\ nb b (prj2 t2) = c_binding (𝗙 b v1).
Proof.
  revert a b v t1 t2;induction u as [|l u] using rev_induction;intros a b v' t1 t2 P;
    [inversion P;simpl_words|].
  apply path_letter in P as (v&l'&s'&->&P&hs).
  destruct l as [c|c|x];destruct l' as [d|d|y];unfold step in hs;try tauto.
  - destruct t1;simpl in *;inversion hs;subst;clear hs. 
    + exists u,[],v,[];simpl;repeat split;auto.
      * apply (path_length_word P).
      * apply (stack_binding_both P c).
      * apply (stack_binding_both P d).
    + apply IHu in P as (u1&u2&v1&v2&->&->&L&E1&E2&->&->).
      exists u1,(u2++[open c]),v1,(v2++[open d]);repeat rewrite app_ass;simpl;repeat split;auto.
      * destruct_eqX a c;simpl_binding; lia.
      * destruct_eqX b d;simpl_binding;lia.
  - destruct hs as ([(->&(A1&A2))|(m1&m2&->&(A1&A2))]&E).
    + setoid_rewrite rmfst_absent in E;[|split;auto];subst.
      rewrite map_app in *;simpl in *;simpl_In in *;simpl in *.
      apply IHu in P as (u1&u2&v1&v2&->&->&L&E1&E2&->&->).
      exists u1,(u2++[c⟩]),v1,(v2++[c⟩]);repeat rewrite app_ass.
      simpl_binding;repeat split;auto.
      * destruct_eqX a c;[tauto|simpl_binding;lia].
      * destruct_eqX b c;[tauto|simpl_binding;lia].
    + rewrite rmfst_present in E by (split;auto).
      apply Levi in E as (s&[(->&->)|(->&E)]);
        [|destruct s as [|x s];[rewrite app_nil_r in *;simpl in *;subst
                               |inversion E;subst;clear E]].
      * rewrite app_comm_cons,<- app_ass in P.
        apply IHu in P as (u1&u2&v1&v2&->&->&L&E).
        exists u1,(u2++[c⟩]),v1,(v2++[d⟩]);simpl_binding;repeat rewrite app_ass.
        destruct E as (<-&<-&<-&<-);repeat rewrite map_app,filter_app,app_length;simpl.
        repeat split;auto.
        -- destruct_eqX a c;simpl_binding;lia.
        -- destruct_eqX b d;simpl_binding;lia.
      * replace ((c,d)::(a,b)::t2) with ([(c,d)]++(a,b)::t2) in P by reflexivity.
        rewrite <- app_ass in P.
        apply IHu in P as (u1&u2&v1&v2&->&->&L&E).
        exists u1,(u2++[c⟩]),v1,(v2++[d⟩]);simpl_binding;repeat rewrite app_ass.
        destruct E as (<-&<-&<-&<-);repeat rewrite map_app,filter_app,app_length;simpl.
        repeat split;auto.
        -- destruct_eqX a c;simpl_binding;lia.
        -- destruct_eqX b d;simpl_binding;lia.
      * rewrite app_ass in P;simpl in P.        
        apply IHu in P as (u1&u2&v1&v2&->&->&L&E).
        exists u1,(u2++[c⟩]),v1,(v2++[d⟩]);simpl_binding;repeat rewrite app_ass.
        destruct E as (<-&<-&<-&<-);repeat rewrite map_app,filter_app,app_length;simpl.
        assert (a<>c /\ b<>d) as (n1&n2)
            by (rewrite map_app in *;simpl in *;simpl_In in *;simpl in *;tauto).
        repeat simpl_beq;simpl_binding;repeat split;tauto||lia.
  - destruct hs as (<-&_).
    apply IHu in P as (u1&u2&v1&v2&->&->&L&->&->&->&->).
    repeat rewrite app_ass;simpl;exists u1,(u2++[var x]),v1,(v2++[var y]);simpl_binding;
      repeat split;auto;lia.
Qed.

Corollary path_stack_decompose u v a b s :
  ([] ⊣ u | v ⤅ s) ->
  a<>b ->
  (s ⊨ a ↦ b) ->
  exists u1 u2 v1 v2, u=u1++⟨a::u2
                 /\ v=v1++⟨b::v2
                 /\ ⎢u1⎥ = ⎢v1⎥
                 /\ a ⋄ u2
                 /\ b ⋄ v2.
Proof.
  intros P N [(->&_)|(t1&t2&->&A1&A2)];[tauto|].
  destruct (path_stack_decompose_aux P) as (u1&u2&v1&v2&->&->&L&E1&E2&L1&L2).
  exists u1,u2,v1,v2;split;[|split;[|split]];auto.
  apply nb_not_In in A1;apply nb_not_In in A2.
  pose proof (stack_binding_both P a) as (Ba&_).
  pose proof (stack_binding_both P b) as (_&Bb).
  revert Ba Bb;repeat rewrite map_app,filter_app,app_length;simpl.
  rewrite A1 in *;rewrite A2 in *;repeat simpl_beq;simpl.
  unfold balanced;simpl_binding;rewrite <- E1,<- E2;simpl_binding.
  destruct (d_binding (𝗙 a u2));[destruct (d_binding (𝗙 b v2));[auto|]|];simpl;lia.
Qed.

(** We may now prove the second direction of our main theorem: whenever we have an accepting path labelled with [u|v], [u] and [v] are alpha-equivalent. 

Note that this proof relies on the fact that [Atom] is infinite. This is in fact the only place in the proof where we use this fact. Indeed, to prove that [⟨a;⟨b;a⟩;b⟩] is equivalent to [⟨b;⟨a;b⟩;a⟩], the transducer only uses names [a] and [b], but the derivation of [≡] will need to use a α-fresh name. *)
Theorem path_αequiv u v s : s ✓ -> [] ⊣ u | v ⤅ s -> u ≡ v.
Proof.
  intros A P;revert v s A P;induction u as [|l u IH]using len_rev_induction;intros v0 s0 A P.
  - inversion P;subst;reflexivity.
  - pose proof P as P0;apply path_letter in P as (v&l'&s'&->&P&hs).
    destruct l as [a|a|x];destruct l' as [b|b|y];unfold step in hs;try tauto.
    + subst; replace b with a in * by (rewrite Accepting_refl in A;apply A;now left).
      apply IH in P;auto;apply Accepting_cons_refl in A;auto.
      apply αr,P.
    + destruct_eqX a b.
      * symmetry in E;subst.
        eapply αr,IH;try apply P||lia.
        destruct hs as ([(_&A')|(s1&s2&->&A')]&->);[setoid_rewrite (rmfst_absent A') in A
                                                   |rewrite (rmfst_present _ A') in A];auto. 
        rewrite Accepting_app in *;rewrite Accepting_cons_refl ;tauto.
      * destruct hs as (hs&->).
        destruct (path_stack_decompose P N hs) as (u1&u2&v1&v2&->&->&B1&B2&L).
        assert (exists c, ~ c ∈( ⌊u2⌋++⌊v2⌋)) as (c&Ic)
            by (apply exists_fresh).
        assert (E1:u1 ++ ⟨a :: u2 ++ [a⟩] ≡ u1 ++ ⟨c :: [(a,c)]∙ u2 ++ [c⟩] )
          by (apply αequiv_app_left,αα;auto;apply αfresh_support;simpl_In in Ic;tauto).
        assert (E2:v1 ++ ⟨b :: v2 ++ [b⟩] ≡ v1 ++ ⟨c :: [(b,c)]∙v2 ++ [c⟩] )
          by (apply αequiv_app_left,αα;auto;apply αfresh_support;simpl_In in Ic;tauto).
        repeat rewrite app_comm_cons,<-app_ass in *.
        repeat rewrite app_ass.
        symmetry in E1;apply αequiv_path in E1 as (s1&P1&A1);apply αequiv_path in E2 as (s2&P2&A2).
        assert (E0 : prj2 (@nil (atom*atom)) = prj1(@nil (atom*atom))) by reflexivity.
        assert (E1 : prj2 (@nil (atom*atom)) = prj1([]⋈@nil (atom*atom))) by reflexivity.
        pose proof (path_mix E0 P1 P0) as (E4&P4).
        pose proof (path_mix E1 P4 P2) as (E5&P3).
        unfold mix in P3 at 1;simpl in P3; clear E0 E1.
        apply path_letter in P3 as (?&?&s4&E&P3&P5);simpl_words;subst.
        simpl in *;simpl_In in *. 
        transitivity  (u1 ++ ⟨c :: [(a, c)] ∙ u2 ++ [c⟩]);
          [|transitivity  (v1 ++ ⟨c :: [(b, c)] ∙ v2 ++ [c⟩])].
        -- apply αequiv_app_left.
           apply αα;auto.
           apply αfresh_support;tauto.
        -- repeat rewrite app_comm_cons,<- app_ass.
           apply αr;eapply IH;try apply P3.
           ++ repeat rewrite app_length;simpl.
              rewrite (act_lists_length [(a,c)] u2);lia.
           ++ revert A A1 A2 E4 E5 P5;clear.
              intros A0 A1 A2 E1;rewrite mix_snd;auto using proj_length;intro E2.
              cut (s1 = s'⊖(a,b) /\ s2 = s'⊖(a,b));[intros (->&->);clear A1 A2 E1 E2|].
              ** pose proof A0 as E;unfold mix;rewrite <- E.
                 rewrite combine_fst;auto.
                 intros ([(_&A)|(t1&t2&->&A)]&E3).
                 --- rewrite (rmfst_absent A) in E3;subst;apply Accepting_combine.
                 --- rewrite E in E3 at 2;rewrite <-combine_split,(rmfst_present _ A) in E3;
                       rewrite E3 in A0.
                     rewrite Accepting_app in *;rewrite Accepting_cons;simpl;tauto.
              ** rewrite (@combine_split _ _ s1),(@combine_split _ _ (s'⊖(a,b))),
                 (@combine_split _ _ s2).
                 split.
                 --- rewrite A1,E1,A0;auto.
                 --- rewrite A0,E2,A2;auto.
        -- apply αequiv_app_left.
           symmetry;apply αα;auto.
           apply αfresh_support;tauto.
    + destruct hs as (->&p&->&E).
      rewrite action_invariant.
      * eapply αr,IH,P;auto.
      * apply map_eq_id.
        intros a I;apply E in I.
        rewrite paired_Accepting in I;auto.
Qed.

Theorem completeness u v : u ≡ v <-> (exists s, [] ⊣ u | v ⤅ s /\ s ✓).
Proof.
  split.
  - apply αequiv_path.
  - intros (s&P&A);apply (path_αequiv A P).
Qed.

(** Using the equivalence between paths and alpha-equivalence, and lemma [αfresh_perm_path_nil], we can prove that the following rule is admissible. *)
Proposition αequiv_αfresh_transpose p u : (forall a, ~ a #α u -> p∙a = a) -> u ≡ p∙u.
Proof. rewrite completeness;apply αfresh_perm_path_nil. Qed.

End s.



(* begin hide *)
Ltac case_var s x y :=
  let p := fresh "p" in
  let e := fresh "e" in
  case_eq (var_perm' ⌊x⌋ s);
  [intros p e;destruct_eqX (p∙x) y|intros e].
Hint Constructors path.
Notation " s ⊣ l1 | l2 ↦ s' " := (step s l1 l2 s') (at level 80).
Notation " s ⊣ u | v ⤅ s' " := (path u v s s') (at level 80).
(* end hide *)                          