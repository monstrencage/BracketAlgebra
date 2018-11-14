Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp.
Require Import aeq_facts alpha_regexp closed_languages binding_finite alphaKA systems.
Require Import factors filters.

Opaque filter_binding.

Section s.

  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.
  Ltac non_zero e :=
    let T:=fresh "T" in
    case_eq (test0 e);intro T;
    [etransitivity;[|apply zero_minimal];
     try apply KA_αKA_inf;
     apply ax_eq_inf,test0_spec;
     repeat (simpl;rewrite T||rewrite test0_act||rewrite orb_true_r);
     try reflexivity|].
  
  Lemma commute_perm_transpose (p : perm) (a b : atom) : (p++[(a,b)] : perm) ≃ [(p∙a,p∙b)]++p.
  Proof.
    intro c;repeat rewrite <- action_compose.
    unfold act at 2 3;simpl.
    destruct_eqX c a;[reflexivity|].
    rewrite <- (act_bij p) in N;simpl_eqX.
    destruct_eqX c b;[reflexivity|].
    rewrite <- (act_bij p) in N0;simpl_eqX.
    reflexivity.
  Qed.

  Lemma 𝗙_perm p (a:atom) (u:list letter) : 𝗙 a (p∙u) = 𝗙 (p∗∙a) u.
  Proof. apply 𝗙_perm. Qed.

  Notation Regexp := (@regexp letter).

  Notation "  N  ▶ " := ((N,false,0):𝖡) (at level 30).
  
  Lemma destr_bind_prod α β N : α⋅β = N ▶ -> β = fst(fst β) ▶.
  Proof.
    unfold prod_binding;destruct α as ((d,f),c),β as ((d',f'),c');unfold d_binding;simpl.
    destruct_ltb c d';[destruct_ltb d' c;[replace d' with c in * by lia|]|];
      intros heq;inversion heq;clear heq;subst.
    - apply orb_false_iff in H1 as (->&->);reflexivity.
    - lia.
    - reflexivity.
  Qed.

  Lemma destr_bind_prod_full α β N :
    α⋅β = N ▶ <->
    β = (d_binding β)▶
    /\ ((c_binding α < d_binding β /\ d_binding α + d_binding β - c_binding α= N)
       \/ (α = (N,false,d_binding β))).
  Proof.
    unfold prod_binding;destruct α as ((d,f),c),β as ((d',f'),c');unfold d_binding;simpl.
    destruct_ltb c d';[destruct_ltb d' c;[replace d' with c in * by lia|]|];split.
    - intros heq;inversion heq;clear heq;subst.
      apply orb_false_iff in H1 as (->&->).
      split;[|right];reflexivity.
    - intros (h1&[F|h2]);[lia|].
      inversion h1;subst.
      inversion h2;subst.
      reflexivity.
    - intro h;inversion h;lia.
    - intros (h1&[F|h2]);[lia|].
      inversion h2;subst.
      lia.
    - intro h;inversion h;subst.
      split;[reflexivity|].
      left;tauto.
    - intros (h1&[(_&<-)|h2]).
      + inversion h1;subst.
        reflexivity.
      + inversion h1;subst.
        inversion h2;subst.
        lia.
  Qed.

  Lemma lower_squares_prod_destr_false β N :
    β ∈ lower_squares (N,false,N) -> β⋅N ▶ = N ▶.
  Proof.
    intros I.
    transitivity ((N,false,N)⋅N ▶).
    - apply lower_squares_spec in I as (_&<-);[|reflexivity].
      rewrite<- prod_assoc;f_equal.
      unfold prod_binding;destruct_ltb N N;[reflexivity|lia].
    - unfold prod_binding;destruct_ltb N N;[reflexivity|lia].
  Qed.

  Lemma lower_squares_prod_destr_true β N :
    β ∈ lower_squares (N,true,N) -> β⋅S N ▶ = S N ▶.
  Proof.
    intros I.
    transitivity ((N,true,N)⋅S N ▶).
    - apply lower_squares_spec in I as (_&<-);[|reflexivity].
      rewrite<- prod_assoc;f_equal.
      unfold prod_binding;destruct_ltb N (S N);[lia|simpl_nat;reflexivity].
    - unfold prod_binding;destruct_ltb N (S N);[lia|simpl_nat;reflexivity].
  Qed.

  Definition SplitRange N k : list (𝖡 * nat) :=
    flat_map
      (fun B =>
         match B with
         | (β,(S n,false,0)) => if Nat.ltb (d_binding β) (S N)
                               then [(β,n)]
                               else []
         | _ => []
         end)
    (factors (S N▶) k).

  Lemma SplitRange_result N k β n :
    (β,n) ∈ SplitRange N k -> β ⋅ S n ▶ = S N ▶ /\ forall α, S N ▶ ⋅ α <>  β.
  Proof.
    unfold SplitRange;rewrite in_flat_map;intros ((β',(([|n']&[])&[]))&I1&I2);
      try (simpl in I2;tauto).
    destruct_ltb (d_binding β') (S N);[simpl in I2;tauto|].
    simpl in I2;destruct I2 as [E|F];[|tauto].
    symmetry in E;inversion E;clear E;subst.
    apply factors_prod in I1;split;[assumption|].
    apply destr_bind_prod_full in I1 as (_&hyp).
    destruct β' as ((d,f),c);unfold d_binding in *;simpl in *.
    intros ((d',f'),c').
    unfold prod_binding.
    destruct d';simpl.
    - clear hyp;intro hyp;inversion hyp;clear hyp;subst.
      lia.
    - intro hyp';inversion hyp';subst;clear hyp'.
      lia.
  Qed.
  
  Lemma SplitRange_In' N k β n :
    size β <= k -> β ⋅ S n ▶ = S N ▶ -> (forall α, S N ▶ ⋅ α <> β) -> (β,n) ∈ SplitRange N k.
  Proof.
    intros Sz Eβ Min.
    unfold SplitRange.
    apply in_flat_map.
    exists (β,S n ▶);simpl.
    split;[apply factors_In;tauto|].
    apply destr_bind_prod_full in Eβ as (_&Eβ).
    destruct_ltb (d_binding β) (S N);simpl;[|tauto].
    destruct Eβ as [(Eβ&E)|Eβ].
    - replace (d_binding (S n,false,0)) with (S n) in * by reflexivity.
      lia.
    - apply (Min (0,false,S n));rewrite Eβ.
      unfold d_binding,prod_binding;reflexivity.
  Qed.

  Lemma exists_prefix_destr_binding u a N :
    d_binding (𝗙 a u) >= N -> exists w1 w2 : list letter, u = w1 ++ w2 /\ 𝗙 a w1 = N ▶.
  Proof.
    induction u as [|l u]using rev_induction;simpl.
    - intro L;replace (d_binding (𝗙 a [])) with 0 in L by reflexivity.
      replace N with 0 in * by lia.
      exists [],[];split;reflexivity.
    - destruct_ltb (d_binding (𝗙 a u)) N.
      + intros;destruct IHu as (w1&w2&->&IH);[lia|].
        exists w1,(w2++[l]);rewrite app_ass;tauto.
      + clear IHu;destruct l as [b|b|x];simpl_binding.
        * destruct_eqX a b;unfold d_binding in *;simpl;intro;exfalso;lia.
        * destruct_eqX a b;[|unfold d_binding in *;simpl;intro;exfalso;lia].
          destruct_eqX (c_binding (𝗙 b u)) 0.
          -- simpl;intros L'.
             assert (E' : d_binding (𝗙 b u) + 1 = N) by lia.
             exists (u++[close b]),[];split;[rewrite app_nil_r;reflexivity|].
             simpl_binding.
             destruct (𝗙 b u) as ((d,f),c).
             unfold d_binding in *;simpl in *;subst.
             unfold prod_binding;simpl;simpl_nat.
             reflexivity.
          -- simpl.
             destruct (c_binding (𝗙 b u));[exfalso;apply N0;reflexivity|lia].
        * unfold d_binding at 2;simpl;simpl_nat;intro;exfalso;lia.
  Qed.

  Lemma SplitRange_In N k u v a :
    v <> [] -> size(𝗙 a u) <= k -> 
    𝗙 a (u++v) = S N ▶ -> (forall w1 w2, u++v = w1++w2  -> ⎢w1⎥ < ⎢u++v⎥ -> 𝗙 a w1 <> S N ▶) ->
    (𝗙 a u,d_binding (𝗙 a v)-1) ∈ SplitRange N k.
  Proof.
    simpl_binding;intros P Len E h.
    pose proof E as E'.
    apply destr_bind_prod_full in E' as (Ev&hyp).
    rewrite Ev in E.
    remember (d_binding (𝗙 a v)) as N';clear HeqN'.
    unfold SplitRange;apply in_flat_map;exists (𝗙 a u,(N',false,0));split.
    - apply factors_In;tauto.
    - remember (𝗙 a u) as α.
      destruct α as ((d,f),c).
      unfold d_binding in *; simpl in *;clear Len.
      destruct N'.
      + simpl;rewrite prod_unit_r in E.
        rewrite E in *.
        apply (h u v).
        * reflexivity.
        * rewrite app_length.
          rewrite <- length_zero_iff_nil in P;lia.
        * rewrite Heqα;reflexivity.
      + replace (S N' - 1) with N' by lia.
        destruct_ltb d (S N);simpl;[|tauto].
        destruct hyp as [(L'&EN)|hyp];[lia|].
        inversion hyp;clear hyp;subst.
        cut (exists w1 w2, u = w1 ++ w2 /\ 𝗙 a w1 = S N ▶).
        * intros (w1&w2&->&E1);apply (h w1 (w2++v)).
          -- rewrite app_ass;reflexivity.
          -- repeat rewrite app_length.
             rewrite <- length_zero_iff_nil in P;lia.
          -- assumption.
        * cut (d_binding (𝗙 a u) = S N);[|rewrite <- Heqα;reflexivity].
          intros;apply exists_prefix_destr_binding;lia.
  Qed.

  Lemma lower_squares_true N : lower_squares (N,true,N) ≈ (N,true,N)::lower_squares (N,false,N).
  Proof.
    intro β;simpl_In.
    repeat rewrite lower_squares_alt by reflexivity.
    destruct β as ((k,ff),k');unfold square,d_binding;simpl.
    rewrite orb_true_r,orb_false_r,negb_true_iff.
    split.
    - intros (->&[L|(->&_)]).
      + tauto.
      + destruct ff;tauto.
    - intros [E|(->&[L|(->&->)])].
      + inversion E;subst;tauto.
      + tauto.
      + tauto.
  Qed.

  Lemma lower_squares_false N :
    lower_squares (S N,false,S N) ≈ (S N,false,S N)::lower_squares (N,true,N).
  Proof.
    intro β;simpl_In.
    repeat rewrite lower_squares_alt by reflexivity.
    destruct β as ((k,ff),k');unfold square,d_binding;simpl.
    rewrite orb_true_r,orb_false_r,negb_true_iff.
    split.
    - intros (->&[L|(->&->)]).
      + destruct_eqX k N.
        * tauto.
        * cut (k<N);[tauto|lia].
      + tauto.
    - intros [E|(->&[L|(->&_)])].
      + inversion E;subst;tauto.
      + cut (k<S N);[tauto|lia].
      + cut (N<S N);[tauto|lia].
  Qed.

  Definition LowerExpr a N f e := Σ (map (fun b => filter_binding a b e) (lower_squares (N,f,N))).

  Lemma LowerExpr_support a N f e : ⌊LowerExpr a N f e⌋ ⊆ ⌊e⌋.
  Proof.
    unfold LowerExpr.
    rewrite <- Σ_support.
    intros b Ib.
    apply In_support_list in Ib as (g&Ig&Ib).
    apply in_map_iff in Ig as ((?&?)&<-&_).
    apply filter_binding_support in Ib;tauto.
  Qed.
       
  Lemma LowerExpr_inf a N f e :
    is_binding_finite e -> LowerExpr a N f e <=KA e.
  Proof.
    intros Be;apply Σ_bounded;intros g Ig.
    apply in_map_iff in Ig as (β&<-&Iβ).
    apply filter_binding_inf,Be.
  Qed.
    
  Lemma LowerExpr_is_binding_finite a N f e :
    is_binding_finite e -> is_binding_finite (LowerExpr a N f e).
  Proof.
    intros Be;eapply is_binding_finite_ax_inf,KA_αKA_inf,LowerExpr_inf;assumption.
  Qed.

  Lemma LowerExpr_star_is_binding_finite a N f e :
    is_binding_finite (e⋆) -> is_binding_finite (LowerExpr a N f e ⋆).
  Proof.
    intros Be;eapply is_binding_finite_ax_inf,KA_αKA_inf,proper_star_inf,LowerExpr_inf.
    - assumption.
    - rewrite <- binding_finite_spec in *;apply andb_true_iff in Be;tauto.
  Qed.

  Lemma LowerExpr_ϵ a N f e : is_binding_finite e -> ϵ (LowerExpr a N f e) = ϵ e.
  Proof.
    unfold LowerExpr;intro Be.
    destruct (ϵ_zero_or_un e) as [E|E];rewrite E.
    - apply ϵ_Σ_un.
      exists (filter_binding a (0 ▶) e);split.
      + apply in_map_iff;exists (0 ▶);split;[reflexivity|].
        apply lower_squares_alt;[reflexivity|].
        split;[reflexivity|].
        simpl;destruct N;[tauto|left;lia].
      + apply ϵ_spec,filter_binding_lang;[assumption|];split;[|reflexivity].
        apply ϵ_spec,E.
    - apply ϵ_Σ_zero.
      intros g Ig.
      apply in_map_iff in Ig as (β&<-&Iβ);simpl in *.
      apply filter_binding_ϵ,E.
  Qed.

  Lemma LowerExpr_test0 a N f e : test0 e = true -> test0 (LowerExpr a N f e) = true.
  Proof.
    intro T.
    unfold LowerExpr.
    rewrite test0_Σ.
    apply forallb_forall;intros g Ig.
    apply in_map_iff in Ig as (β&<-&Iβ);simpl in *.
    apply filter_binding_test0,T.
  Qed.

  Lemma LowerExpr_act p a N f e : p∙ (LowerExpr a N f e) = LowerExpr (p∙a) N f (p∙e).
  Proof.
    unfold LowerExpr.
    rewrite Σ_act.
    unfold act at 1,act_lists.
    rewrite map_map;f_equal.
    apply map_ext.
    intros b;apply filter_binding_act.
  Qed.
  
  Lemma star_join_bis_left (E F G : Regexp) : E =KA F ∪ G -> E ⋆ =KA F ⋆ ∪ (F ⋆ · G) · E ⋆.
  Proof.
    intro hyp.
    apply ax_inf_PartialOrder;unfold Basics.flip;split.
    + etransitivity;[rewrite hyp;apply ax_eq_inf,proper_star,semiring_comm|].
      etransitivity;[apply ax_eq_inf,star_join|].
      apply inf_join_inf.
      * etransitivity;[apply ax_eq_inf,ka_star_unfold_eq|].
        apply inf_join_inf;[etransitivity;[|apply inf_cup_left];apply one_inf_star|].
        transitivity ((un·G)·E⋆).
        -- apply proper_prod_inf.
           ++ apply ax_eq_inf;symmetry;apply left_unit.
           ++ apply proper_star_inf;rewrite hyp;apply inf_cup_right.
        -- etransitivity;[|apply inf_cup_right].
           apply proper_prod_inf;[|reflexivity].
           apply proper_prod_inf;[|reflexivity].
           apply one_inf_star.
      * etransitivity;[apply proper_prod_inf;[reflexivity|apply ax_eq_inf,ka_star_unfold_eq]|].
        etransitivity;[apply ax_eq_inf,semiring_left_distr|].
        apply inf_join_inf.
        -- etransitivity;[|apply inf_cup_left].
           apply ax_eq_inf,right_unit.
        -- etransitivity;[|apply inf_cup_right].
           etransitivity;[|apply ax_eq_inf,mon_assoc].
           apply proper_prod_inf;[reflexivity|].
           etransitivity;[apply ax_eq_inf;symmetry;apply mon_assoc|].
           apply proper_prod_inf;[reflexivity|].
           etransitivity;[|apply ax_eq_inf,ka_star_dup].
           apply proper_prod_inf;[apply proper_star_inf;rewrite hyp;apply inf_cup_left|].
           etransitivity;[|apply ax_eq_inf;symmetry;apply ka_star_star].
           apply proper_star_inf;rewrite hyp.
           etransitivity;[|apply ax_eq_inf,ka_star_dup].
           apply proper_prod_inf;[|apply proper_star_inf,inf_cup_left].
           etransitivity;[|apply star_incr].
           apply inf_cup_right.
    + apply inf_join_inf.
      * rewrite hyp;apply proper_star_inf,inf_cup_left.
      * etransitivity;[|apply ax_eq_inf,ka_star_dup].
        apply proper_prod_inf;[|reflexivity].
        rewrite hyp.
        etransitivity;[|apply ax_eq_inf,ka_star_dup].
        apply proper_prod_inf;[apply proper_star_inf,inf_cup_left|].
        etransitivity;[|apply star_incr].
        apply inf_cup_right.
  Qed.
  Lemma star_join_bis_right (E F G : Regexp) : E =KA F ∪ G -> E ⋆ =KA F ⋆ ∪ (E ⋆ · G) · F ⋆.
  Proof.
    intro hyp.
    apply ax_inf_PartialOrder;unfold Basics.flip;split.
    + etransitivity;[rewrite hyp;apply ax_eq_inf,proper_star,semiring_comm|].
      etransitivity;[apply ax_eq_inf,star_join|].
      apply inf_join_inf.
      * etransitivity;[apply ax_eq_inf,ka_star_unfold_eq|].
        apply inf_join_inf;[etransitivity;[|apply inf_cup_left];apply one_inf_star|].
        etransitivity;[apply ax_eq_inf;symmetry;apply star_switch_side|].
        transitivity ((E⋆·G)·un).
        -- etransitivity;[|apply ax_eq_inf;symmetry;apply right_unit].
           apply proper_prod_inf;[|reflexivity].
           apply proper_star_inf;rewrite hyp;apply inf_cup_right.
        -- etransitivity;[|apply inf_cup_right].
           apply proper_prod_inf;[reflexivity|].
           apply one_inf_star.
      * etransitivity;[apply proper_prod_inf;[reflexivity|apply ax_eq_inf,ka_star_unfold_eq]|].
        etransitivity;[apply ax_eq_inf,semiring_left_distr|].
        apply inf_join_inf.
        -- etransitivity;[|apply inf_cup_left].
           apply ax_eq_inf,right_unit.
        -- etransitivity;[apply proper_prod_inf;[reflexivity
                                                |apply ax_eq_inf;symmetry;apply star_switch_side]|].
           etransitivity;[|apply inf_cup_right].
           etransitivity;[apply ax_eq_inf,mon_assoc|].
           etransitivity;[|apply ax_eq_inf,mon_assoc].
           apply proper_prod_inf;[|reflexivity].
           etransitivity;[|apply ax_eq_inf,ka_star_dup].
           apply proper_prod_inf;[apply proper_star_inf;rewrite hyp;apply inf_cup_left|].
           etransitivity;[|apply ax_eq_inf;symmetry;apply ka_star_star].
           apply proper_star_inf;rewrite hyp.
           etransitivity;[|apply ax_eq_inf,ka_star_dup].
           apply proper_prod_inf;[|apply proper_star_inf,inf_cup_left].
           etransitivity;[|apply star_incr].
           apply inf_cup_right.
    + apply inf_join_inf.
      * rewrite hyp;apply proper_star_inf,inf_cup_left.
      * etransitivity;[|apply ax_eq_inf,ka_star_dup].
        apply proper_prod_inf.
        -- etransitivity;[|apply ax_eq_inf,ka_star_dup].
           apply proper_prod_inf;[reflexivity|].
           etransitivity;[|apply star_incr]. 
           rewrite hyp.
           apply inf_cup_right.
        -- rewrite hyp;apply proper_star_inf,inf_cup_left.
  Qed.
  
  Lemma LowerExpr_star_true_left a N e :
    LowerExpr a N true e ⋆
    =KA LowerExpr a N false e ⋆
        ∪ LowerExpr a N false e ⋆ · filter_binding a (N,true,N) e · LowerExpr a N true e ⋆.
  Proof.
    assert (h: LowerExpr a N true e =KA LowerExpr a N false e ∪ filter_binding a (N,true,N) e).
    - unfold LowerExpr.
      etransitivity;[|apply semiring_comm].
      etransitivity;[apply algebra.Σ_equivalent;rewrite lower_squares_true;reflexivity|].
      simpl;reflexivity.
    - apply star_join_bis_left,h.
  Qed.
  Lemma LowerExpr_star_false_left a N e :
    LowerExpr a (S N) false e ⋆
    =KA LowerExpr a N true e ⋆
        ∪ LowerExpr a N true e ⋆ · filter_binding a (S N,false,S N) e · LowerExpr a (S N) false e ⋆.
  Proof.
    assert (h: LowerExpr a (S N) false e =KA LowerExpr a N true e
                                             ∪ filter_binding a (S N,false,S N) e).
    - unfold LowerExpr.
      etransitivity;[|apply semiring_comm].
      etransitivity;[apply algebra.Σ_equivalent;rewrite lower_squares_false;reflexivity|].
      simpl;reflexivity.
    - apply star_join_bis_left,h.
  Qed.
  
  Lemma LowerExpr_star_true_right a N e :
    LowerExpr a N true e ⋆
    =KA LowerExpr a N false e ⋆
        ∪ LowerExpr a N true e ⋆ · filter_binding a (N,true,N) e · LowerExpr a N false e ⋆.
  Proof.
    assert (h: LowerExpr a N true e =KA LowerExpr a N false e ∪ filter_binding a (N,true,N) e).
    - unfold LowerExpr.
      etransitivity;[|apply semiring_comm].
      etransitivity;[apply algebra.Σ_equivalent;rewrite lower_squares_true;reflexivity|].
      simpl;reflexivity.
    - apply star_join_bis_right,h.
  Qed.
  
  Lemma LowerExpr_star_false_right a N e :
    LowerExpr a (S N) false e ⋆
    =KA LowerExpr a N true e ⋆
        ∪ LowerExpr a (S N) false e ⋆ · filter_binding a (S N,false,S N) e · LowerExpr a N true e ⋆.
  Proof.
    assert (h: LowerExpr a (S N) false e =KA LowerExpr a N true e
                                             ∪ filter_binding a (S N,false,S N) e).
    - unfold LowerExpr.
      etransitivity;[|apply semiring_comm].
      etransitivity;[apply algebra.Σ_equivalent;rewrite lower_squares_false;reflexivity|].
      simpl;reflexivity.
    - apply star_join_bis_right,h.
  Qed.

  Lemma LowerExpr_lang a N f e :
    is_binding_finite e -> ⟦LowerExpr a N f e⟧ ≃ (fun u => ⟦e⟧ u /\ 𝗙 a u ∈ (lower_squares (N,f,N))).
  Proof.
    unfold LowerExpr; intros Be u;split;intros Iu.
    - apply Σ_lang in Iu as (g&Ig&Iu).
      apply in_map_iff in Ig as (β&<-&Iβ).
      apply filter_binding_lang in Iu as (Iu&->);tauto.
    - destruct Iu as (Iu&Eu).
      apply Σ_lang;exists (filter_binding a (𝗙 a u) e);split.
      + apply in_map_iff;exists (𝗙 a u);tauto.
      + apply filter_binding_lang;tauto.
  Qed.
  
  Lemma LowerExpr_star_lang a N f e :
    is_binding_finite (e⋆) -> ⟦LowerExpr a N f e⋆⟧ ≃ (fun u => ⟦e⋆⟧ u /\ 𝗙 a u ∈ (lower_squares (N,f,N))).
  Proof.
    intros Bs.
    assert (Sq : sqExpr e)
      by (eapply sqExpr_inf;[apply binding_finite_sqExpr_star,Bs|simpl;apply star_incr]). 
    unfold LowerExpr; intros u;split;intros Iu.
    - assert (h : ⟦LowerExpr a N f e⋆⟧≲⟦e⋆⟧)
        by (apply ax_inf_lang_incl,proper_star_inf,LowerExpr_inf,Sq).    
      split;[apply h,Iu|].
      apply binding_prod_lower_squares in Iu;[|assumption]. 
      destruct Iu as [<-|Iu];[|apply Iu].
      apply lower_squares_alt;[reflexivity|split;[reflexivity|]].
      destruct N;simpl;[right;tauto|left;lia].
    - destruct Iu as ((n&Iu)&Iβ);exists n.
      revert u Iu Iβ;induction n;intros u.
      + intros -> _;reflexivity.
      + intros (u1&u2&->&Iu1&Iu2).
        simpl_binding.
        intros IL.
        apply lower_squares_prod in IL as (h1&h2).
        * exists u1,u2;split;[reflexivity|].
             split;[|apply IHn;tauto].
             apply Σ_lang;exists (filter_binding a (𝗙 a u1) e);split.
          -- apply in_map_iff;exists (𝗙 a u1);tauto.
          -- apply filter_binding_lang;[apply Sq|tauto].
        * eapply is_binding_finite_bindings in Iu1;[|apply Sq].
          apply Sq in Iu1;apply Iu1.
        * apply binding_finite_sqExpr_star in Bs as (Bs&Sq').
          apply (Sq' a).
          apply is_binding_finite_bindings;[apply Bs|exists n;assumption].
        * reflexivity.
  Qed.

  Lemma LowerExpr_αKA a N ff e f :
    is_binding_finite f -> e =α f -> LowerExpr a N ff e =α LowerExpr a N ff f .
  Proof.
    intros Bf E.
    pose proof Bf as Be;apply (is_binding_finite_ax_eq E) in Be.
    apply Σ_map_equiv_α.
    intros β _.
    apply filter_binding_αKA;tauto.
  Qed.

  Lemma LowerExpr_αKA_inf a N ff e f :
    is_binding_finite f -> e <=α f -> LowerExpr a N ff e <=α LowerExpr a N ff f .
  Proof.
    intros Bf E.
    pose proof Bf as Be;apply (is_binding_finite_ax_eq E) in Be.
    apply Σ_bounded;intros g Ig.
    apply in_map_iff in Ig as (β&<-&Iβ).
    etransitivity;[|apply Σ_bigger,in_map_iff;exists β;split;[reflexivity|assumption]].
    apply filter_binding_αKA_inf;tauto.
  Qed.
  
  Opaque lower_squares LowerExpr.
      
  Fixpoint splitActStrict c a N e :=
    match e with
    | e_zero => zero
    | e_un => zero
    | ⟪x⟫ => if S N ▶=?= 𝗳 a x then [(a,c)]∙⟪x⟫ else zero
    | e_add e f => splitActStrict c a N e ∪ splitActStrict c a N f
    | e_prod e f =>
      if (test0 (e·f))
      then zero
      else (splitActStrict c a N e · f)
             ∪ (Σ (map (fun B => [(a,c)]∙ filter_binding a (fst B) e·(splitActStrict c a (snd B) f))
                       (SplitRange N (sizeExpr e))))
    | e_star e =>
      [(a,c)]∙ LowerExpr a N true e ⋆ · splitActStrict c a N e · e⋆
    end.

  Lemma splitActStrict_support c a N e :
    ⌊splitActStrict c a N e⌋ ⊆ c::a::⌊e⌋.
  Proof.
    revert N;induction e;intro N;simpl.
    - apply incl_nil.
    - apply incl_nil.
    - replace (e_add e1) with (join e1) by reflexivity.
      repeat rewrite support_join.
      apply incl_app;[rewrite IHe1|rewrite IHe2];intro;simpl;simpl_In;tauto.
    - destruct (test0 e1 || test0 e2);[apply incl_nil|].
      replace (e_prod e1) with (prod e1) by reflexivity.
      repeat rewrite support_join||rewrite support_prod.
      repeat apply incl_app.
      + rewrite IHe1;intro;simpl;simpl_In;tauto.
      + intro;simpl;simpl_In;tauto.
      + rewrite <- Σ_support.
        intros k Ik.
        apply In_support_list in Ik as (f&If&Ik).
        apply in_map_iff in If as ((?&?)&<-&_).
        rewrite support_prod,support_action in Ik;simpl_In in Ik.
        rewrite In_act_lists in Ik.
        rewrite filter_binding_support in Ik;simpl in *;simpl_In.
        destruct Ik as [Ik|Ik].
        * revert Ik;unfold act;simpl;unfold_eqX;tauto.
        * apply IHe2 in Ik;simpl in Ik; tauto.
    - replace (e_star e) with (star e) by reflexivity.
      repeat rewrite support_action||rewrite support_star||rewrite support_prod.
      repeat apply incl_app.
      + Transparent LowerExpr.
        unfold LowerExpr.
        Opaque LowerExpr.
        rewrite <- Σ_support.
        intros b Ib.
        apply In_act_lists,In_support_list in Ib as (f&If&Ib).
        apply in_map_iff in If as ((?&?)&<-&_).
        apply filter_binding_support in Ib.
        revert Ib;unfold act;simpl;unfold_eqX;tauto.
      + apply IHe.
      + intro;simpl;tauto.
    - destruct (_=?=_).
      + rewrite support_action.
        intros b Ib;apply In_act_lists in Ib.
        revert Ib;unfold act;simpl;unfold_eqX;tauto.
      + apply incl_nil.
  Qed.

  
  Lemma splitActStrict_test0 c a N e:
    test0 e = true -> test0 (splitActStrict c a N e) = true.
  Proof.
    induction e;simpl;try reflexivity||discriminate.
    - rewrite andb_true_iff; intros (eq1,eq2);rewrite IHe1,IHe2;tauto.
    - intros ->;reflexivity.
  Qed.
      
  Lemma splitActStrict_ϵ c a N e : ϵ (splitActStrict c a N e) = zero.
  Proof.
    revert N ;induction e;intros N;simpl;simpl_In;try tauto.
    - rewrite IHe1,IHe2;reflexivity.
    - destruct (test0 e1||test0 e2);[simpl;tauto|].
      simpl.
      rewrite IHe1;simpl.
      rewrite ϵ_Σ_zero;[reflexivity|].
      intros g Ig;apply in_map_iff in Ig as ((β'&N')&<-&Ig).
      simpl.
      rewrite ϵ_act,IHe2;simpl.
      destruct (ϵ _);reflexivity.
    - destruct N;simpl;rewrite IHe;reflexivity.
    - destruct (_=?=_);reflexivity.
  Qed.

  Lemma splitActStrict_act p c a N e : p∙splitActStrict c a N e = splitActStrict (p ∙ c) (p ∙ a) N (p ∙ e).
  Proof.
    revert N;induction e;intros N;simpl;try reflexivity.
    - rewrite act_join;replace actReg with act by reflexivity.
      rewrite IHe1,IHe2;reflexivity.
    - replace actReg with act by reflexivity.
      repeat rewrite test0_act;destruct (test0 e1||test0 e2);[reflexivity|].
      rewrite (act_join p (splitActStrict c a N e1·e2)),act_prod,IHe1.
      f_equal.
      rewrite Σ_act.
      unfold act at 1,act_lists;rewrite map_map.
      f_equal.
      repeat rewrite sizeExpr_act.
      apply map_ext.
      intros (β&N');simpl.
      rewrite <- IHe2,act_prod;f_equal.
      rewrite <- filter_binding_act.
      repeat rewrite action_compose.
      rewrite commute_perm_transpose.
      reflexivity.
    - replace actReg with act by reflexivity.
      rewrite <- IHe.
      rewrite (act_prod p ([(a, c)] ∙ LowerExpr a N true e ⋆ · splitActStrict c a N e)),act_prod .
      f_equal.
      f_equal.
      rewrite <- LowerExpr_act.
      repeat rewrite act_star.
      f_equal.
      repeat rewrite action_compose.
      rewrite commute_perm_transpose.
      reflexivity.
    - rewrite 𝗳_perm,act_pinv_p.
      destruct (_=?=_);try reflexivity.
      replace ⟪p∙x⟫ with (p∙⟪x⟫) by reflexivity.
      repeat rewrite action_compose.
      rewrite commute_perm_transpose.
      reflexivity.
  Qed.
  
  Lemma splitActStrict_lang c a N e :
    is_binding_finite e ->
    ⟦splitActStrict c a N e⟧ ≃ (fun u => exists u1 u2, u = [(a,c)]∙u1++u2
                                         /\ ⟦e⟧ (u1++u2)
                                         /\ 𝗙 a u1 = S N ▶
                                         /\ forall v w, u1 = v++w -> ⎢v⎥ < ⎢u1⎥ -> 𝗙 a v <> S N ▶).
  Proof.
    intros Be ;revert N.
    induction_bin_fin e Be;intros N u.
    - simpl;split;[intro FF;exfalso;apply FF|].
      intros (?&?&_&FF&_);apply FF.
    - simpl;split;[intro FF;exfalso;apply FF|].
      intros (?&?&->&E&FF&_);simpl.
      apply app_eq_nil in E as (->&->).
      discriminate.
    - simpl;destruct_eqX ((S N,false,0) : 𝖡) (𝗳 a x);simpl.
      + split.
        * intros ->;exists [x],[];repeat split.
          -- simpl_binding;reflexivity.
          -- intros [] ?;simpl;[|lia].
             intros <- _;simpl_binding.
             rewrite <- E;discriminate.
        * intros (u1&u2&->&Ex&B&Min).
          rewrite <- E in B;destruct u1;[discriminate|].
          inversion Ex as [[e1 e2]];apply app_eq_nil in e2 as (?&?);subst.
          reflexivity.
      + split;[intro FF;exfalso;apply FF|].
        intros ([]&u2&->&Ex&B&Min);[discriminate|].
        inversion Ex as [[e1 e2]];apply app_eq_nil in e2 as (?&?);subst.
        apply N0;rewrite <- B;simpl_binding;reflexivity.
    - simpl;unfold join,joinLang;rewrite (IHe1 N u),(IHe2 N u).
      split;[intros [I|I]|intro I];destruct I as (u1&u2&h1&h2&h3);
        [| |destruct h2 as [h2|h2];[left|right]];exists u1,u2;repeat split;tauto.
    - simpl;rewrite T;simpl;split.
      + intros [I|I].
        * destruct I as (u'&u3&->&Iu'&Iu3).
          apply IHe1 in Iu' as (u1&u2&->&Iu&hB&Min).
          exists u1,(u2++u3).
          rewrite app_ass;split;[reflexivity|].
          rewrite <- app_ass;split;[exists (u1++u2),u3;tauto|].
          tauto.
        * apply Σ_lang in I as (g&Ig&Iu).
          apply in_map_iff in Ig as ((β&N')&<-&Ig).
          destruct Iu as (u1&u'&->&Iu1&Iu).
          apply act_lang,filter_binding_lang in Iu1 as (Iu1&Eu1);[|assumption].
          simpl in *.
          apply IHe2 in Iu as (u2&u3&->&Iu&B&Min).
          exists ([(a,c)]∗∙u1++u2),u3.
          split;[rewrite act_lists_app,act_p_pinv,app_ass;reflexivity|].
          split;[rewrite app_ass;exists ([(a,c)]∙u1),(u2++u3);tauto|].
          apply SplitRange_result in Ig as (E1&E2).
          split.
          -- simpl_binding;rewrite Eu1,B,E1;reflexivity.
          -- intros w1 w2 Ew L h.
             apply Levi in Ew as (w&[(Ew&->)|(->&->)]).
             ++ apply (act_bij [(a,c)]) in Ew;rewrite act_p_pinv in Ew.
                replace [(a,c)] with ([(a,c)]∗) in Ew by reflexivity.
                rewrite Ew in *.
                rewrite act_p_pinv in Iu1,Eu1, L.
                rewrite 𝗙_app,h in Eu1;subst.
                apply (E2 (𝗙 a w));reflexivity.
             ++ clear IHe1 IHe2 Iu1 Iu T e1 e2 B1 B2.
                assert (Len : ⎢w⎥ < ⎢w++w2⎥) by solve_length;clear L.
                rewrite 𝗙_app in h,B;simpl in *.
                rewrite Eu1 in *.
                pose proof h as h'.
                apply destr_bind_prod_full in h' as (E'&h').
                remember (d_binding (𝗙 a w)) as K;clear HeqK;rewrite E' in *.
                pose proof B as B'.
                apply destr_bind_prod_full in B' as (E''&h'').
                remember (d_binding (𝗙 a w2)) as K';clear HeqK';rewrite E'' in *.
                simpl in *.
                replace (d_binding (K,false,0)) with K in * by reflexivity.
                destruct h' as [h'| ->];[|apply (E2 (0,false,K));reflexivity].
                destruct h'' as [h''|h''].
                ** destruct β as ((D,f),C).
                   unfold d_binding in h';simpl in *.
                   destruct h' as (L1&E);rewrite <- E in *;clear E N.
                   destruct h'' as (L2&E);rewrite <- E in *;clear E N'.
                   revert E1;simpl_nat;unfold prod_binding.
                   destruct_ltb C (K+K');[lia|].
                   destruct_ltb (K+K') C;[|lia].
                   intros E;inversion E as [[EE]];lia.
                ** inversion h'' as [[h1 h2]];rewrite h1 in *;rewrite <- h2 in *;clear h1 h2 K K'.
                   apply (Min w w2);tauto. 
      + intros (u1&u2&->&(v1&v2&EE&Iv1&Iv2)&B&Min).
        apply Levi in EE as (w&[(->&->)|(->&->)]).
        * destruct_eqX w (@nil letter);simpl in *.
          -- rewrite app_nil_r in *.
             left;exists ([(a,c)]∙v1),u2;split;[reflexivity|split;[|assumption]].
             apply IHe1.
             exists v1,[];repeat rewrite app_nil_r;tauto.
          -- right.
             apply Σ_lang.
             exists ([(a, c)] ∙ filter_binding a (𝗙 a v1) e1 · splitActStrict c a (d_binding(𝗙 a w)-1) e2).
             split.
             ++ apply in_map_iff;exists (𝗙 a v1,d_binding(𝗙 a w)-1);split;[reflexivity|].
                apply SplitRange_In;try tauto.
                apply binding_finite_bound_size;tauto.
             ++ rewrite act_lists_app,app_ass.
                exists ([(a,c)]∙v1),([(a,c)]∙w++u2);split;[reflexivity|split].
                ** apply act_lang;rewrite act_pinv_p.
                   apply filter_binding_lang;tauto.
                ** apply IHe2;exists w,u2;split;[reflexivity|].
                   split;[assumption|].
                   replace (S (d_binding (𝗙 a w) - 1)) with (d_binding (𝗙 a w));[split|].
                   --- simpl_binding in B;eapply destr_bind_prod;eassumption.
                   --- intros w1 w2 -> Len Ew1.
                       apply (Min (v1++w1) w2);[rewrite app_ass;reflexivity|solve_length|].
                       simpl_binding.
                       rewrite Ew1.
                       rewrite 𝗙_app in B.
                       pose proof (destr_bind_prod B) as E;rewrite E in B;apply B.
                   --- simpl_binding in B;apply destr_bind_prod_full in B as (E1&E2).
                       remember (𝗙 a w) as K. 
                       destruct K as ((?&?)&?);unfold d_binding in *;simpl in *.
                       cut (0<>n);[lia|].
                       remember (𝗙 a v1) as K'. 
                       destruct K' as ((?&?)&?);unfold d_binding in *;simpl in *.
                       destruct E2 as [(E2&_)|E2];[lia|].
                       inversion E2;subst.
                       intros <-.
                       apply (Min v1 w);[reflexivity|rewrite <-length_zero_iff_nil in N0;solve_length|].
                       rewrite <- HeqK';reflexivity.
        * left.
          exists ([(a,c)]∙u1++w),v2;split;[rewrite app_ass;reflexivity|].
          split;[|assumption].
          apply IHe1;exists u1,w;tauto.
    - simpl;rewrite T;split;[intro FF;exfalso;apply FF|].
      intros (u1&u2&_&Iu&_).
      assert (T' : test0 (e1·e2) = true) by apply T.
      apply test0_spec,soundness in T'.
      cut (⟦ e1 · e2 ⟧(u1++u2));[|apply Iu].
      rewrite (T' _);intro FF;apply FF.
    - simpl;split.
      + intros (?&u4&->&(u1&u'&->&Iu1'&Iu')&Iu4).
        assert (Iu1: ⟦LowerExpr a N true e⋆⟧ ([(a,c)]∗∙u1))
          by (rewrite<- act_lang,act_star;apply Iu1');clear Iu1'.
        apply IHe in Iu' as (u2&u3&->&Iu'&B&Min);clear IHe.
        exists ((([(a, c)] ∗) ∙ u1)++u2),(u3++u4);repeat split.
        * rewrite act_lists_app,act_p_pinv;repeat rewrite app_ass;reflexivity.
        * cut (⟦ e ⟧⋆·⟦e⟧·⟦e⟧⋆ ≲ ⟦e⟧⋆);[|apply ka_star_mid_split].
          intros h;apply h;clear h.
          rewrite <- app_ass.
          exists ((([(a, c)] ∗) ∙ u1 ++ u2) ++ u3),u4;split;[reflexivity|].
          split;[|assumption].
          exists (([(a, c)] ∗) ∙ u1), (u2 ++ u3);split;[rewrite app_ass;reflexivity|].
          split;[|assumption].
          cut (⟦ LowerExpr a N true e ⋆ ⟧ ≲ ⟦e⋆⟧);[intros h;apply h,Iu1|].
          apply ax_inf_lang_incl,proper_star_inf,LowerExpr_inf,Sq.
        * simpl_binding.
          rewrite B.
          apply LowerExpr_star_lang in Iu1 as (_&Iu1);[|apply sqExpr_bindings_finite_star,Sq].
          transitivity ((N,true,N)⋅(S N,false,0)).
          -- apply lower_squares_spec in Iu1 as (_&E);[|reflexivity].
             rewrite <- E,<-prod_assoc.
             f_equal.
             unfold prod_binding;destruct_ltb N (S N);[lia|].
             repeat f_equal;lia.
          -- unfold prod_binding;destruct_ltb N (S N);[lia|].
             repeat f_equal;lia.
        * intros w1 w2 Ew Lw Ew1.
          apply Levi in Ew as (w&[(Ew&->)|(->&->)]).
          -- rewrite <- (act_bij [(a,c)]),act_p_pinv in Ew;rewrite Ew in *;clear Ew u1.
             rewrite act_pinv_p in Lw,Iu1.
             apply LowerExpr_star_lang in Iu1 as (_&Iu1);[|apply sqExpr_bindings_finite_star,Sq].
             apply lower_squares_alt in Iu1 as (h&h');[|reflexivity].
             revert h h';unfold square;simpl.
             rewrite orb_true_r.
             simpl_binding.
             rewrite Ew1;simpl;simpl_nat;lia.
          -- apply LowerExpr_star_lang in Iu1 as (_&Iu1);[|apply sqExpr_bindings_finite_star,Sq].
             apply (Min w w2);[reflexivity|solve_length|].
             simpl_binding in Ew1.
             apply destr_bind_prod_full in Ew1 as (Ew&hyp).
             remember (d_binding (𝗙 a w)) as K;clear HeqK.
             rewrite Ew in *.
             f_equal;f_equal.
             apply lower_squares_alt in Iu1 as (h&h');[|reflexivity].
             simpl in *.
             rewrite orb_true_r in h'.
             destruct hyp as [hyp|hyp];[|exfalso].
             ++ simpl_binding in B;apply destr_bind_prod_full in B as (Ew2&hyp').
                remember (d_binding (𝗙 a w2)) as K';clear HeqK'.
                rewrite Ew in *;simpl in *.
                unfold d_binding in hyp';simpl in hyp'.
                destruct hyp' as [(hK'&hyp')|hyp'];[|inversion hyp';reflexivity].
                exfalso.
                rewrite <- h in hyp.
                remember (c_binding (𝗙 a ([(a, c)] ∙ u1))) as M.
                destruct h' as [h'|(h'&_)];lia.
             ++ rewrite hyp in *.
                unfold square,d_binding in h;simpl in *;subst.
                destruct h' as [FF|(FF&_)];lia.
      + intros (u1&u2&->&Iu'&B&Min).
        assert (Iu : ⟦e⋆⟧ (u1++u2)) by apply Iu';clear Iu'.
        apply split_star in Iu as [(->&->)|(w1&w2&w3&w4&->&->&Iw1&Iw&Iw4)];[discriminate|].
        exists ([(a, c)] ∙ (w1 ++ w2) ++ w3),w4;split;[rewrite app_ass;reflexivity|].
        split;[|assumption].
        rewrite act_lists_app,app_ass.
        exists ([(a,c)]∙w1),([(a,c)]∙w2++w3);split;[reflexivity|].
        cut (𝗙 a w1 ∈ lower_squares (N, true, N)).
        * intros Iβ.
          split.
          -- cut (⟦ [(a, c)] ∙ (LowerExpr a N true e⋆) ⟧ ([(a, c)] ∙ w1));
               [rewrite act_star;simpl;tauto|].
             apply act_lang;rewrite act_pinv_p.
             apply LowerExpr_star_lang;[apply sqExpr_bindings_finite_star,Sq|tauto].
          -- apply IHe.
             exists w2,w3;split;[reflexivity|].
             split;[assumption|].
             split.
             ++ simpl_binding in B.
                apply destr_bind_prod_full in B as (h1&h2);rewrite h1.
                remember (d_binding (𝗙 a w2)) as K;clear HeqK.
                f_equal;f_equal.
                apply lower_squares_alt in Iβ as (Sqw1&h);[|reflexivity].
                simpl in h.
                destruct h2 as [(h2&h2')|h2].
                ** rewrite <- Sqw1 in h2'.
                   destruct h as [h|(h&_)];lia.
                ** rewrite h2 in Sqw1.
                   apply Sqw1.
             ++ intros v1 v2 -> Len Ev1.
                apply (Min (w1++v1) v2);[rewrite app_ass;reflexivity|solve_length|].
                simpl_binding.
                transitivity ((N,true,N)⋅(S N,false,0)).
                ** apply lower_squares_spec in Iβ as (_&Iβ);[|reflexivity].
                   rewrite <- Iβ,<-prod_assoc.
                   f_equal.
                   rewrite Ev1;unfold prod_binding;destruct_ltb N (S N);[lia|].
                   destruct_ltb (S N) N;[|lia].
                   f_equal;f_equal;lia.
                ** unfold prod_binding;destruct_ltb N (S N);[lia|].
                   destruct_ltb (S N) N;[|lia].
                   f_equal;f_equal;lia.
        * clear IHe.
          apply lower_squares_alt;[reflexivity|].
          cut (square (𝗙 a w1)).
          -- intros Sw1;split;[tauto|].
             simpl_binding in B;apply destr_bind_prod_full in B as (Ew2&B).
             simpl;rewrite orb_true_r.
             remember (d_binding (𝗙 a w2)) as K;clear HeqK.
             rewrite <- Sw1 in B.
             destruct B as [(B1&B2)|B].
             ++ replace K with (S N) in * by lia.
                destruct_eqX (c_binding (𝗙 a w1)) N;[right;tauto|left;lia].
             ++ rewrite B in *;simpl.
                unfold square,d_binding in Sw1;simpl in Sw1;subst.
                exfalso.
                cut (exists v1 v2, w1 = v1++v2 /\ 𝗙 a v1 = S N ▶).
                ** intros (v1&v2&->&Ev1).
                   apply (Min v1 (v2++w2));[rewrite app_ass;reflexivity| |assumption].
                   repeat rewrite app_length.
                   destruct w2;[discriminate|simpl;lia].
                ** cut (d_binding (𝗙 a w1) = S N);[|rewrite B;reflexivity].
                   clear;induction w1 as [|l w1] using rev_induction;[discriminate|].
                   destruct_eqX (d_binding (𝗙 a w1)) (S N).
                   --- destruct IHw1 as (v1&v2&->&Ev1);[reflexivity|].
                       intros _;exists v1,(v2++[l]);split;[rewrite app_ass;reflexivity|assumption].
                   --- simpl_binding.
                       destruct l as [b|b|x];simpl;unfold_eqX;simpl;simpl_nat;try tauto.
                       subst.
                       case_eq (c_binding (𝗙 b w1));[|intros ? ?;simpl_nat;tauto].
                       intros E1 E2.
                       exists (w1++[close b]),[];split;[rewrite app_nil_r;reflexivity|].
                       simpl_binding.
                       apply destr_bind_prod_full;split;[reflexivity|].
                       left;split;simpl.
                       +++ rewrite E1;unfold d_binding;simpl;lia.
                       +++ unfold d_binding at 2;simpl.
                           rewrite E1;simpl_nat;assumption.
          -- apply sqExpr_star in Sq as (Bs&Sq).
             apply (Sq a),(is_binding_finite_bindings);tauto.
  Qed.
  
  Lemma is_binding_finite_splitActStrict c a N e :
    is_binding_finite e -> is_binding_finite (splitActStrict c a N e).
  Proof.
    intro Be;apply binding_finite_spec.
    revert N;induction_bin_fin e Be;intro N.
    - reflexivity.
    - reflexivity.
    - simpl;destruct (_=?=_);reflexivity.
    - simpl;rewrite IHe1,IHe2;reflexivity.
    - simpl;rewrite T;simpl.
      apply andb_true_iff;split.
      + apply orb_true_iff;right.
        rewrite IHe1.
        apply binding_finite_spec,B2.
      + rewrite binding_finite_Σ,forallb_forall.
        intros g Ig.
        apply in_map_iff in Ig as ((β&n)&<-&I).
        simpl;apply orb_true_iff;right.
        rewrite IHe2,andb_true_r.
        apply binding_finite_spec,is_binding_finite_act,is_binding_finite_filter_binding,B1.
    - assert (E: test0(e1·e2) = true) by apply T.
      eapply splitActStrict_test0,test0_spec,KA_αKA in E.
      eapply binding_finite_spec,is_binding_finite_ax_eq;
        [apply E|apply binding_finite_spec;reflexivity].
    - simpl.
      rewrite orb_false_r.
      assert (E1 : is_binding_finite (e⋆)) by (apply sqExpr_bindings_finite_star,Sq).
      apply binding_finite_spec in E1;simpl in E1;rewrite E1,andb_true_r.
      rewrite IHe,andb_true_r.
      apply orb_true_iff;right.
      apply orb_true_iff;right.
      apply andb_true_iff;split.
      + apply binding_finite_spec,is_binding_finite_act,LowerExpr_is_binding_finite,Sq.
      + apply forallb_forall;intros b _.
        apply forallb_forall;intros β Iβ;unfold is_square.
        destruct Sq as (Be&Sq).
        rewrite eqX_correct.
        apply bindings_witness in Iβ as (u&Iu&<-).
        apply act_lang,LowerExpr_lang in Iu as (Iu&_);[|apply Be].
        eapply (is_binding_finite_bindings Be ([(a,c)]∗∙b)) in Iu. 
        rewrite 𝗙_perm,act_pinv_p in Iu.
        apply Sq in Iu;apply Iu.
  Qed.
        
      
    
  Lemma splitActStrict_KA c a N e f : is_binding_finite f -> e =KA f -> splitActStrict c a N e =KA splitActStrict c a N f.
  Proof.
    intros Bf E;apply CompletenessKA.
    rewrite (splitActStrict_lang _ _ _ Bf).
    pose proof Bf as Be;apply (is_binding_finite_ax_eq (KA_αKA E)) in Be.
    rewrite (splitActStrict_lang _ _ _ Be).
    intro u;setoid_rewrite (soundness E _);tauto.
  Qed.

  Lemma splitActStrict_KA_inf c a N e f :
    is_binding_finite f -> e <=KA f -> splitActStrict c a N e <=KA splitActStrict c a N f.
  Proof.
    unfold ax_inf;intros Bf Ef;rewrite <- (splitActStrict_KA c a N Bf Ef) at 2.
    reflexivity.
  Qed.

  Lemma splitActStrict_fresh c a N e : is_binding_finite e -> a # e -> splitActStrict c a N e =KA zero.
  Proof.
    intros Be Fe;apply test0_spec,not_false_is_true.
    intros Iu;apply test0_false in Iu as (u&Iu).
    apply splitActStrict_lang in Iu as (u1&u2&_&Iu&B&_);[|assumption].
    apply support_lang in Iu;rewrite <- Iu in Fe.
    assert (Fu1 : a # u1) by (rewrite support_list_app in Fe;simpl_In in Fe;tauto).
    apply αfresh_support in Fu1;rewrite Fu1 in B;discriminate.
  Qed.

  Lemma splitActStrict_αfresh c a N e : is_binding_finite e -> freshExpr a e -> splitActStrict c a N e =KA zero.
  Proof.
    intros Be Fe;apply test0_spec,not_false_is_true.
    intros Iu;apply test0_false in Iu as (u&Iu).
    apply splitActStrict_lang in Iu as (u1&u2&_&Iu&B&_);[|assumption].
    unfold freshExpr in Fe.
    eapply is_binding_finite_bindings,Fe in Iu as [B'|FF];simpl in *;try tauto.
    symmetry in B';revert B';simpl_binding;rewrite B.
    unfold ε;rewrite destr_bind_prod_full;simpl.
    intros (_&[(h1&h2)|h1]);discriminate.
  Qed.

  Lemma witness_binding a N : exists u, 𝗙 a u = N ▶.
  Proof.
    exists (map (fun _ => close a) (seq 0 N)).
    remember 0 as k;rewrite Heqk at 2. 
    clear Heqk;revert k;induction N;intro k.
    - reflexivity.
    - simpl;simpl_binding.
      rewrite IHN.
      unfold prod_binding;destruct N;simpl;reflexivity.
  Qed.
      
  Lemma splitActStrict_αKA c a N e f :
    is_binding_finite f -> c # e -> c # f -> e =α f -> splitActStrict c a N e =α splitActStrict c a N f.
  Proof.
    intros B2 Fe Ff eq.
    pose proof B2 as B1.
    apply (is_binding_finite_ax_eq eq) in B1.
    revert c N Fe Ff;induction eq;intros c N F1 F2.
    - reflexivity.
    - symmetry;apply IHeq;tauto.
    - destruct (exists_fresh (⌊e⌋++⌊f⌋++⌊g⌋)) as (d&Id).
      assert (d # e /\ d # f /\ d # g) as (Fe&Ff&Fg) by (simpl_In in Id;tauto);clear Id.
      rewrite <- (act_pinv_p [(c,d)] _).
      rewrite <- (act_pinv_p [(c,d)] (splitActStrict c a N e)).
      apply αKA_act.
      repeat rewrite splitActStrict_act.
      unfold act at 1 2 4 5;simpl;simpl_eqX.
      rewrite action_invariant,action_invariant.
      + unfold_eqX.
        * apply KA_αKA;transitivity zero;[|symmetry];apply splitActStrict_fresh;tauto.
        * apply KA_αKA;transitivity zero;[|symmetry];apply splitActStrict_fresh;tauto.
        * etransitivity;[apply IHeq1|apply IHeq2];try tauto.
          -- apply (is_binding_finite_ax_eq eq1);tauto.
          -- apply (is_binding_finite_ax_eq eq1);tauto.
      + apply map_eq_id;intros b Ib.
        apply elements_inv_act_atom;simpl;intros [<-|[<-|F]];tauto.
      + apply map_eq_id;intros b Ib.
        apply elements_inv_act_atom;simpl;intros [<-|[<-|F]];tauto.
    - simpl.
      assert (eqT : test0 (e·e') = test0 (f·f'))
        by (apply test0_αKA;rewrite eq1,eq2;reflexivity).
      case_eq (test0 (e·e'));intro Te;pose proof Te as Tf;rewrite eqT in Tf;
        [simpl in *;rewrite Te,Tf;reflexivity|].
      simpl in *;revert B1 B2;repeat rewrite <- binding_finite_spec;simpl;rewrite Te,Tf;simpl;
        repeat rewrite andb_true_iff||rewrite binding_finite_spec;intros (Be&Be')(Bf&Bf').
      apply ax_eq_add.
      + apply ax_eq_prod;[|assumption].
        rewrite support_prod in F1,F2.
        apply IHeq1;simpl_In in *;tauto.
      + apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros g Ig;
          apply in_map_iff in Ig as ((β&N')&<-&Ig);simpl in *.
        * transitivity ([(a, c)] ∙ filter_binding a β f · splitActStrict c a N' f' ).
          -- apply proper_prod_inf;[apply αKA_inf_act,filter_binding_αKA_inf,ax_eq_inf
                                   |apply ax_eq_inf,IHeq2];try tauto.
             ++ rewrite support_prod in F1;simpl_In in *;tauto.
             ++ rewrite support_prod in F2;simpl_In in *;tauto.
          -- non_zero (filter_binding a β f).
             apply Σ_bigger, in_map_iff.
             exists (β,N');split;[reflexivity|].
             apply SplitRange_result in Ig as (Eg&Min).
             apply test0_false in T as (u&Iu).
             apply filter_binding_lang in Iu as (Iu&Eu);[|assumption].
             apply SplitRange_In'.
             ++ rewrite <- Eu;apply binding_finite_bound_size;try tauto.
             ++ assumption.
             ++ assumption.
        * transitivity ([(a, c)] ∙ filter_binding a β e · splitActStrict c a N' e' ).
          -- apply proper_prod_inf;[apply αKA_inf_act,filter_binding_αKA_inf,ax_eq_inf
                                   |apply ax_eq_inf;symmetry;apply IHeq2];try tauto.
             ++ rewrite eq1;reflexivity.
             ++ rewrite support_prod in F1;simpl_In in *;tauto.
             ++ rewrite support_prod in F2;simpl_In in *;tauto.
          -- non_zero (filter_binding a β e).
             apply Σ_bigger, in_map_iff.
             exists (β,N');split;[reflexivity|].
             apply SplitRange_result in Ig as (Eg&Min).
             apply test0_false in T as (u&Iu).
             apply filter_binding_lang in Iu as (Iu&Eu);[|assumption].
             apply SplitRange_In'.
             ++ rewrite <- Eu;apply binding_finite_bound_size;try tauto.
             ++ assumption.
             ++ assumption.
    - rewrite <- binding_finite_spec in B1,B2;simpl in B1,B2;
        repeat rewrite andb_true_iff in B1,B2||rewrite binding_finite_spec in B1,B2.
      rewrite support_join in F1,F2.
      simpl;apply ax_eq_add;[apply IHeq1|apply IHeq2];simpl_In in *;tauto.
    - simpl.
      rewrite eq at 3.
      pose proof B1 as Be.
      pose proof B2 as Bf.
      rewrite <- binding_finite_spec in Be,Bf;simpl in Be,Bf;
        repeat rewrite andb_true_iff in Be,Bf||rewrite binding_finite_spec in Be,Bf.
      rewrite IHeq;try tauto.
      repeat (apply proper_prod;[|reflexivity]).
      apply ax_eq_star,αKA_act.
      apply LowerExpr_αKA;tauto.
    - destruct H as [a1 a2 e h|e f h].
      + destruct_eqX a1 a2;[rewrite perm_a_a_eq_nil,act_nil;reflexivity|].
        destruct_eqX a a1;[|destruct_eqX a a2].
        * transitivity zero;[|symmetry];apply KA_αKA,splitActStrict_αfresh.
          -- assumption.
          -- intros b Ib;left;symmetry.
             apply bindings_witness in Ib as (u&Iu&<-).
             apply (h _ Iu).
          -- apply is_binding_finite_act;tauto.
          -- intros b Ib;left;symmetry.
             rewrite bindings_act in Ib.
             revert Ib; unfold act;simpl;simpl_eqX;intro Ib.
             apply bindings_witness in Ib as (u&Iu&<-).
             apply (h _ Iu).
        * transitivity zero;[|symmetry];apply KA_αKA,splitActStrict_αfresh.
          -- assumption.
          -- intros b Ib;left;symmetry.
             apply bindings_witness in Ib as (u&Iu&<-).
             apply (h _ Iu).
          -- apply is_binding_finite_act;tauto.
          -- intros b Ib;left;symmetry.
             rewrite bindings_act in Ib.
             revert Ib; unfold act;simpl;simpl_eqX;intro Ib.
             apply bindings_witness in Ib as (u&Iu&<-).
             apply (h _ Iu).
        * revert F2;rewrite support_action,In_act_lists.
          unfold act at 1;simpl;unfold_eqX;intros F2.
          -- rewrite action_invariant;[reflexivity|].
             apply elements_inv_act;intros b Ib.
             rewrite support_list_atoms in Ib.
             simpl;intros [<-|[<-|FF]];tauto.
          -- rewrite action_invariant;[reflexivity|].
             apply elements_inv_act;intros b Ib.
             rewrite support_list_atoms in Ib.
             simpl;intros [<-|[<-|FF]];tauto.
          -- rewrite <- (act_p_pinv [(a1,a2)] c) at 2.
             rewrite <- (act_p_pinv [(a1,a2)] a) at 2.
             rewrite <- splitActStrict_act.
             unfold act at 2 3;simpl;simpl_eqX.
             apply ax_eq_ax,αKA_αα.
             intros u Iu.
             apply splitActStrict_lang in Iu as (u1&u2&->&Iu&_);[|assumption].
             destruct (h _ Iu) as (e1&e2);revert e1 e2.
             unfold fresh__α;simpl_binding.
             repeat rewrite 𝗙_perm.
             unfold act;simpl;simpl_eqX;tauto.
      + apply KA_αKA,splitActStrict_KA,ax_eq_ax,h;tauto.
    - destruct H as [e f|e f].
      + pose proof eq as eq';clear eq.
        assert (eq : e · f <=α f) by (apply eq');clear eq'.
        case_eq (test0 f);intro Tf;[transitivity zero;apply KA_αKA;[|symmetry];
                                    apply test0_spec;simpl;try rewrite splitActStrict_test0;
                                    try rewrite Tf;reflexivity|].
        assert (Bs: is_binding_finite (e⋆))
          by (revert Tf B1 ;repeat rewrite <- binding_finite_spec;simpl;intros ->;simpl;
              repeat rewrite andb_true_iff;tauto).
        assert (Be: is_binding_finite e)
          by (revert Bs ;repeat rewrite <- binding_finite_spec;simpl;
              repeat rewrite andb_true_iff;tauto).
        pose proof B2 as Bf;clear B1 B2.
        assert (Fe : c # e) by (rewrite support_join,support_prod,support_star in F1;
                                simpl_In in F1;tauto).
        pose proof F2 as Ff;clear F1 F2.
        assert (IH : forall (c : atom) (N : nat), c # e -> c # f -> splitActStrict c a N (e · f) <=α splitActStrict c a N f)
          by (intros d N' F1 F2;apply IHeq;try tauto;
              [revert Tf Bf Bs ;repeat rewrite <- binding_finite_spec;simpl;
               repeat rewrite andb_true_iff;intros -> -> (->&_);simpl;split;
               [apply orb_true_r|reflexivity]
              |rewrite support_join,support_prod;simpl_In;tauto]);clear IHeq.
        cut (splitActStrict c a N (e ⋆ · f) <=α splitActStrict c a N f);[intro h;apply h|].
        simpl;rewrite Tf.
        apply inf_join_inf.
        * rewrite <- (mon_assoc _ _ _).
          etransitivity;[apply proper_prod_inf;[reflexivity|apply ka_star_left_ind,eq]|].
          rewrite <- (mon_assoc _ _ _).
          etransitivity;[apply proper_prod_inf;[reflexivity|etransitivity;[|apply (IH c N);tauto]]|].
          -- simpl;rewrite Tf.
             case_eq (test0 e);simpl;intros Te;
               [apply ax_eq_inf,KA_αKA,test0_spec;simpl;apply orb_true_iff;left;
                apply splitActStrict_test0,Te|].
             apply inf_cup_left.
          -- apply ka_star_left_ind.
             etransitivity;[|apply (IH c N);tauto].
             simpl;rewrite Tf.
             case_eq (test0 e);simpl;intros Te;
               [apply ax_eq_inf,KA_αKA,test0_spec;simpl;apply orb_true_iff;left;
                rewrite test0_act,LowerExpr_test0;tauto|].
             etransitivity;[|apply inf_cup_right].
             Transparent LowerExpr.
             unfold LowerExpr.
             rewrite Σ_act.
             unfold act at 1,act_lists;simpl.
             rewrite Σ_distr_r.
             repeat rewrite map_map.
             apply Σ_bounded;intros g Ig.
             apply in_map_iff in Ig as (β&<-&Iβ).
             non_zero (filter_binding a β e).
             apply Σ_bigger,in_map_iff.
             exists (β,N);split;[reflexivity|].
             apply SplitRange_In'.
             ++ apply test0_false in T as (u&Iu).
                apply filter_binding_lang in Iu as (Iu&<-);[|assumption].
                apply binding_finite_bound_size;tauto.
             ++ apply lower_squares_alt in Iβ;[|reflexivity].
                apply destr_bind_prod_full;split;[reflexivity|].
                unfold d_binding at 1 3;simpl.
                left.
                destruct Iβ as (<-&[L|(E&_)]);simpl in *;split;try lia.
             ++ intros α Eα.
                rewrite <- Eα in Iβ.
                apply lower_squares_spec in Iβ as (_&Eu1);[|reflexivity].
                revert Eu1.
                destruct α as ((D,ff),C);unfold prod_binding;simpl.
                destruct D;simpl;destruct_ltb C N.
                --- destruct_ltb N C;intros E;inversion E;lia.
                --- destruct C;intros E;inversion E;lia.
                --- destruct_ltb N C;intros E;inversion E;lia.
                --- destruct C;intros E;inversion E;lia.
        * apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((β,N')&<-&Ig);simpl.
          non_zero (filter_binding a β (e⋆)).
          assert (size β<= sizeExpr e /\ exists N' ff, β = (N',ff,N')) as (Sz&K&ff&->)
              by (apply test0_false in T as (u&Iu);
                  apply filter_binding_lang in Iu as (Iu&Eu);[|assumption];
                  split;[rewrite<- Eu;transitivity (sizeExpr (e⋆));
                         [apply binding_finite_bound_size;tauto|reflexivity]|];
                  exists (d_binding β),(snd(fst β));cut (square β);
                  [intros E;destruct β as ((C,F),D);unfold square,d_binding in *;
                   simpl in *;subst;reflexivity
                  |pose proof (binding_finite_sqExpr_star Bs) as (_&h);
                   rewrite <- Eu;apply (h a),is_binding_finite_bindings,Iu;assumption]).
          replace N' with N in *.
          -- transitivity ([(a,c)]∙LowerExpr a K ff e ⋆· splitActStrict c a N f).
             ++ apply proper_prod_inf;[|reflexivity].
                rewrite <- act_star;apply αKA_inf_act.
                apply KA_αKA_inf,CompletenessKA_inf;intros u Iu.
                apply filter_binding_lang in Iu as (Iu&Eu);[|assumption].
                apply LowerExpr_star_lang;[assumption|].
                split;[assumption|].
                apply lower_squares_spec;[reflexivity|].
                rewrite Eu;split.
                ** reflexivity.
                ** unfold prod_binding;destruct_ltb K K;[rewrite orb_diag;reflexivity|lia].
             ++ apply ka_star_left_ind.
                etransitivity;[|apply (IH c N);tauto].
                simpl;rewrite Tf.
                case_eq (test0 e);simpl;intros Te;
                  [apply ax_eq_inf,KA_αKA,test0_spec;simpl;apply orb_true_iff;left;
                   rewrite test0_act,LowerExpr_test0;tauto|].
                etransitivity;[|apply inf_cup_right].
                Transparent LowerExpr.
                unfold LowerExpr.
                rewrite Σ_act.
                unfold act at 1,act_lists;simpl.
                rewrite Σ_distr_r.
                repeat rewrite map_map.
                apply Σ_bounded;intros g Ig'.
                apply in_map_iff in Ig' as (β'&<-&Iβ).
                apply Σ_bigger,in_map_iff.
                exists (β',N);split;[reflexivity|].
                apply SplitRange_In'.
                ** rewrite <- Sz.
                   apply lower_squares_size;[reflexivity|assumption].
                ** apply lower_squares_spec in Iβ as (_&e1);[|reflexivity].
                   apply SplitRange_result in Ig as (e2&_).
                   rewrite <- e2 at 2.
                   rewrite <- e1,<-prod_assoc,e2;reflexivity.
                ** intros α Eα.
                   apply SplitRange_result in Ig as (e2&Min).
                   apply (Min (α⋅(K,ff,K))).
                   rewrite prod_assoc,Eα.
                   apply lower_squares_spec in Iβ as (_&->);reflexivity.
          -- apply SplitRange_result in Ig as (e2&Min).
             apply destr_bind_prod_full in e2 as (_&e2).
             unfold d_binding in e2;simpl in e2.
             destruct e2 as [(h1&h2)|h].
             ++ lia.
             ++ inversion h;clear h;lia.
      + pose proof eq as eq';clear eq.
        assert (eq : e · f <=α e) by (apply eq');clear eq'.
        case_eq (test0 e);intro Te;[transitivity zero;apply KA_αKA;[|symmetry];
                                    apply test0_spec;simpl;try rewrite splitActStrict_test0;
                                    try rewrite Te;reflexivity|].
        assert (Bs: is_binding_finite (f⋆))
          by (revert Te B1 ;repeat rewrite <- binding_finite_spec;simpl;intros ->;simpl;
              repeat rewrite andb_true_iff;tauto).
        assert (Bf: is_binding_finite f)
          by (revert Bs ;repeat rewrite <- binding_finite_spec;simpl;
              repeat rewrite andb_true_iff;tauto).
        pose proof B2 as Be;clear B1 B2.
        assert (Ff : c # f) by (rewrite support_join,support_prod,support_star in F1;
                                simpl_In in F1;tauto).
        pose proof F2 as Fe;clear F1 F2.
        assert (IH : forall (c : atom) (N : nat), c # e -> c # f -> splitActStrict c a N (e · f) <=α splitActStrict c a N e)
          by (intros d N' F1 F2;apply IHeq;try tauto;
              [revert Te Be Bs ;repeat rewrite <- binding_finite_spec;simpl;
               repeat rewrite andb_true_iff;intros -> -> (->&_);simpl;split;
               [apply orb_true_r|reflexivity]
              |rewrite support_join,support_prod;simpl_In;tauto]);clear IHeq.
        cut (splitActStrict c a N (e · f ⋆) <=α splitActStrict c a N e);[intro h;apply h|].
        simpl;rewrite Te;simpl.
        apply inf_join_inf.
        * apply ka_star_right_ind.
          etransitivity;[|apply (IH c N);tauto].
          non_zero f.
          simpl;rewrite Te,T;simpl;apply inf_cup_left.
        * apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((β,N')&<-&Ig);simpl.
          transitivity (splitActStrict c a N e · f⋆).
          -- repeat rewrite (mon_assoc _ _ _).
             apply proper_prod_inf;[|reflexivity].
             set (L := map fst ((fun B => snd B=?=N'):>SplitRange N (sizeExpr e))).
             transitivity ([(a,c)]∙Σ (map (fun b => filter_binding a b e) L)·splitActStrict c a N' f).
             ++ apply proper_prod_inf;[|reflexivity].
                transitivity ([(a,c)]∙Σ (map (fun b => filter_binding a b e) L)
                                     ·[(a, c)] ∙ LowerExpr a N' true f ⋆).
                ** apply proper_prod_inf;[|reflexivity].
                   apply αKA_inf_act.
                   apply Σ_bigger,in_map_iff;exists β;split;[reflexivity|].
                   apply in_map_iff;exists (β,N');split;[reflexivity|].
                   simpl_In;split;[assumption|].
                   rewrite eqX_correct;reflexivity.
                ** clear β Ig;rewrite <-act_star,<- act_prod.
                   apply αKA_inf_act.
                   apply ka_star_right_ind.
                   rewrite Σ_distr_r,map_map.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as (β&<-&Iβ).
                   unfold LowerExpr.
                   rewrite Σ_distr_l,map_map.
                   apply Σ_bounded;intros g Ig.
                   apply in_map_iff in Ig as (α&<-&Iα).
                   transitivity (filter_binding a (β⋅α) e).
                   --- etransitivity;[|apply filter_binding_αKA_inf,eq;assumption].
                       apply KA_αKA_inf,CompletenessKA_inf.
                       intros u (u1&u2&->&Iu1&Iu2).
                       apply filter_binding_lang in Iu1 as (Iu1&<-);[|assumption].
                       apply filter_binding_lang in Iu2 as (Iu2&<-);[|assumption].
                       apply filter_binding_lang.
                       +++ revert Be Bf.
                           repeat rewrite <- binding_finite_spec;simpl;
                             intros -> ->;apply orb_true_r.
                       +++ split;[|simpl_binding;reflexivity].
                           exists u1,u2;tauto.
                   --- non_zero (filter_binding a (β⋅α) e).
                       clear IH;apply Σ_bigger,in_map_iff;exists (β⋅α);split;[reflexivity|].
                       apply lower_squares_alt in Iα as (Eα&hyp1);[|reflexivity].
                       destruct α as ((K&ff)&?).
                       unfold square in Eα;unfold d_binding in *;simpl in hyp1,Eα;subst.
                       assert (L1 : K <= N') by (destruct hyp1 as [h|(h&_)];lia);clear hyp1.
                       revert Iβ;unfold L.
                       repeat rewrite in_map_iff.
                       intros ((?&?)&E&h);simpl in E;subst.
                       simpl_In in h;destruct h as (Iβ&E).
                       rewrite eqX_correct in E;simpl in E;subst.
                       exists (β⋅(K,ff,K),N');split;[reflexivity|].
                       simpl_In;split;[|apply eqX_correct;reflexivity].
                       apply SplitRange_result in Iβ as (E&Min).
                       apply SplitRange_In'.
                       +++ apply test0_false in T as (u&Iu).
                           apply filter_binding_lang in Iu as (Iu&<-);[|assumption].
                           apply binding_finite_bound_size;tauto.
                       +++ rewrite <-E,<- prod_assoc.
                           unfold prod_binding at 2.
                           destruct_ltb K (S N');[lia|].
                           destruct_ltb (S N') K;[|lia].
                           f_equal;f_equal;f_equal;lia.
                       +++ intros A EA.
                           apply destr_bind_prod_full in E as (_&E).
                           destruct A as ((D,FF)&C),β as ((D',ff'),C').
                           unfold d_binding in *;simpl in *.
                           destruct E as [(L2&E)|E].
                           *** revert EA;destruct D;unfold prod_binding at 1;simpl;
                                 unfold prod_binding;(destruct_ltb C' K;[destruct_ltb K C'|]);
                                      intro EA;inversion EA;subst;lia.
                           *** inversion E;subst.
                               apply (Min (0,false,S N')).
                               unfold prod_binding;simpl;reflexivity.
             ++ clear β Ig;rewrite Σ_act;unfold act at 1,act_lists;rewrite Σ_distr_r.
                repeat rewrite map_map.
                apply Σ_bounded;intros g Ig.
                apply in_map_iff in Ig as (β&<-&Iβ).
                etransitivity;[|apply (IH c N);tauto].
                simpl;rewrite Te.
                case_eq (test0 f);simpl;intro T.
                ** apply ax_eq_inf,KA_αKA,test0_spec;simpl;apply orb_true_iff;right.
                   apply splitActStrict_test0,T.
                ** etransitivity;[|apply inf_cup_right].
                   apply Σ_bigger,in_map_iff;exists (β,N');split;[reflexivity|].
                   unfold L in Iβ.
                   apply in_map_iff in Iβ as ((?&?)&E&Iβ).
                   simpl_In in Iβ;destruct Iβ as (Iβ&E').
                   rewrite eqX_correct in E';simpl in E,E';subst;assumption.
          -- apply ka_star_right_ind.
             etransitivity;[|apply (IH c N);tauto].
             non_zero f.
             simpl;rewrite Te,T;simpl;apply inf_cup_left.
  Qed.
        
  Lemma splitActStrict_αKA_inf c a N e f :
    is_binding_finite f -> c # e -> c # f -> e <=α f -> splitActStrict c a N e <=α splitActStrict c a N f.
  Proof.
    intros Bf F1 F2 E.
    apply (@splitActStrict_αKA c a N) in E;[apply E|assumption| |assumption].
    rewrite support_join;simpl_In;tauto.
  Qed.


  Fixpoint splitStrict_list a N e :=
    match e with
    | e_zero => []
    | e_un => []
    | ⟪x⟫ => if S N ▶=?= 𝗳 a x then [(⟪x⟫,un)] else []
    | e_add e f => splitStrict_list a N e ++ splitStrict_list a N f
    | e_prod e f =>
      if (test0 (e·f))
      then []
      else (map (fun P => (fst P,snd P·f)) (splitStrict_list a N e))
             ++ (flat_map (fun B => map (fun P => (filter_binding a (fst B) e·fst P,snd P))
                                     (splitStrict_list a (snd B) f))
                          (SplitRange N (sizeExpr e)))
    | e_star e =>
      map (fun P => (LowerExpr a N true e ⋆ · fst P,snd P·e⋆)) 
          (splitStrict_list a N e)
    end.

  Lemma splitActStrict_splitStrict_list c a N e :
    splitActStrict c a N e =KA Σ (map (fun P => [(a,c)]∙fst P · snd P) (splitStrict_list a N e)).
  Proof.
    revert N;induction e;intros N;simpl.
    - reflexivity.
    - reflexivity.
    - rewrite map_app,IHe1,IHe2.
      apply algebra.Σ_app.
    - destruct (test0 e1||test0 e2);[reflexivity|].
      rewrite map_app,map_map.
      etransitivity;[|apply algebra.Σ_app].
      apply proper_join.
      + rewrite IHe1.
        etransitivity;[apply Σ_distr_r|].
        rewrite map_map.
        apply Σ_map_equiv.
        intros (f1,f2) _;simpl.
        symmetry;apply mon_assoc.
      + apply ax_inf_PartialOrder;unfold Basics.flip;simpl;split;apply Σ_bounded;intros g Ig.
        * apply in_map_iff in Ig as ((b,n)&<-&I).
          simpl.
          rewrite IHe2.
          etransitivity;[apply ax_eq_inf,Σ_distr_l|].
          rewrite map_map.
          apply Σ_bounded;intros g Ig.
          apply in_map_iff in Ig as ((f1&f2)&<-&If).
          simpl.
          transitivity ([(a, c)] ∙ (filter_binding a b e1 · f1) · f2).
          -- rewrite act_prod;apply ax_eq_inf,mon_assoc.
          -- apply Σ_bigger,in_map_iff;exists (filter_binding a b e1 · f1, f2).
             split;[reflexivity|].
             apply in_flat_map;exists (b,n);split;[assumption|].
             apply in_map_iff;exists (f1,f2);tauto.
        * apply in_map_iff in Ig as ((f1,f2)&<-&If).
          apply in_flat_map in If as ((b,n)&Ib&If).
          apply in_map_iff in If as ((g1&g2)&heq&Ig).
          symmetry in heq;inversion heq;clear heq;subst.
          transitivity  ([(a, c)] ∙ filter_binding a b e1 · splitActStrict c a n e2).
          -- rewrite IHe2.
             simpl;rewrite act_prod.
             etransitivity;[apply ax_eq_inf;symmetry;apply mon_assoc|].
             apply proper_prod_inf;[reflexivity|].
             apply Σ_bigger,in_map_iff;exists (g1,g2);tauto.
          -- apply Σ_bigger,in_map_iff;exists (b,n);tauto.
    - rewrite IHe;clear IHe;rewrite map_map.
      apply ax_inf_PartialOrder;unfold Basics.flip;simpl;split.
      + etransitivity;[apply ax_eq_inf,proper_prod;[apply Σ_distr_l|reflexivity]|].
        rewrite map_map.
        etransitivity;[apply ax_eq_inf,Σ_distr_r|]. 
        rewrite map_map.
        apply Σ_bounded;intros g Ig.
        apply in_map_iff in Ig as ((f1,f2)&<-&If).
        simpl.
        transitivity ([(a, c)] ∙ (LowerExpr a N true e ⋆ · f1) · (f2 · e ⋆)).
        * rewrite act_prod;apply ax_eq_inf.
          etransitivity;[|symmetry;apply mon_assoc].
          apply proper_prod;[|reflexivity].
          etransitivity;[apply mon_assoc|].
          reflexivity.
        * apply Σ_bigger,in_map_iff;exists (f1,f2);tauto.
      + apply Σ_bounded;intros g Ig.
        apply in_map_iff in Ig as ((f1,f2)&<-&If).
        simpl.
        transitivity (([(a, c)] ∙ LowerExpr a N true e ⋆ · ([(a, c)] ∙ f1 · f2)) · e ⋆).
        * rewrite act_prod;apply ax_eq_inf.
          etransitivity;[apply mon_assoc|].
          apply proper_prod;[|reflexivity].
          etransitivity;[|symmetry;apply mon_assoc].
          reflexivity.
        * apply proper_prod_inf;[|reflexivity].
          apply proper_prod_inf;[reflexivity|].
          apply Σ_bigger,in_map_iff;exists (f1,f2);tauto.
    - destruct (_=?=_);[|reflexivity].
      simpl.
      etransitivity;[|symmetry;apply right_unit].
      etransitivity;[|symmetry;apply right_unit].
      reflexivity.
  Qed.
          
  Lemma splitStrict_list_binding a N e f1 f2 u :
    is_binding_finite e -> (f1,f2) ∈ (splitStrict_list a N e) -> ⟦f1⟧ u ->
    𝗙 a u = S N ▶
    /\ (forall v w : list letter, u = v ++ w -> ⎢ v ⎥ < ⎢ u ⎥ -> 𝗙 a v <> (S N, false, 0)).
  Proof.
    intro Be;revert N f1 f2 u;induction_bin_fin e Be;intros N f1 f2 u;simpl.
    - tauto.
    - tauto.
    - destruct_eqX ((S N,false,0):𝖡) (𝗳 a x);[|simpl;tauto].
      intros [heq|FF];[|simpl in FF;tauto].
      inversion heq;clear heq;subst.
      intros Iu.
      replace u with [x] by apply Iu.
      simpl_binding;split;[reflexivity|].
      intros [] ? EE;[|simpl;lia].
      rewrite <- E;intros _;discriminate.
    - simpl_In;intros [I|I];[eapply IHe1|eapply IHe2];eassumption.
    - rewrite T;simpl_In;intros [I|I].
      + apply in_map_iff in I as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        eapply IHe1;eassumption.
      + apply in_flat_map in I as ((b,n)&Ib&If).
        apply in_map_iff in If as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        simpl in *.
        intros (u1&u2&->&I1&I2).
        simpl_binding.
        destruct (IHe2 _ _ _ _ Ig I2) as (E1&E2).
        rewrite E1.
        apply filter_binding_lang in I1 as (_&E1');[|assumption].
        rewrite E1'.
        apply SplitRange_result in Ib as (Eb&Min);split;[tauto|].
        intros v1 v2 EE Len Ev1.
        apply Levi in EE as (w&[(->&->)|(->&->)]).
        * simpl_binding in E1'.
          apply (Min (𝗙 a w)).
          rewrite <- E1',Ev1;reflexivity.
        * apply (E2 w v2);[reflexivity|solve_length|].
          simpl_binding in E1.
          simpl_binding in Ev1.
          rewrite E1' in Ev1.
          clear E2 Ig Min E1' I2 Len IHe1 IHe2 B1 B2 T e1 e2.
          apply destr_bind_prod_full in E1 as (Ev2&h1).
          revert Ev2 h1;set (K:= d_binding(𝗙 a v2));intros.
          apply destr_bind_prod_full in Ev1 as (Ew&h2).
          revert Ew h2;set (N':= d_binding(𝗙 a w));intros.
          rewrite Ew in *.
          apply destr_bind_prod_full in Eb as (_&h3).
          destruct b as ((D,F),C).
          unfold d_binding in *;simpl in *.
          simpl_nat.
          destruct_eqX N' (S n);[reflexivity|].
          destruct h1 as [(h1&h1')|h1];[|inversion h1;reflexivity].
          destruct h2 as [(h2&h2')|h2];[|inversion h2];(destruct h3 as [(h3&h3')|h3];[|inversion h3]);
            lia.
    - rewrite T;simpl;tauto.
    - intros I.
      apply in_map_iff in I as ((g1&g2)&heq&Ig).
      symmetry in heq;inversion heq;clear heq;subst.
      intros (u1&u2&->&I1&I2).
      simpl_binding.
      apply LowerExpr_star_lang in I1 as (_&I1);
            [|apply sqExpr_star in Sq as (Bs&Sq);apply Bs].
      destruct (IHe _ _ _ _ Ig I2) as (E1&Min);split.
      + rewrite E1.
        apply lower_squares_prod_destr_true.
        tauto.
      + intros v1 v2 EE Len Ev1.
        apply Levi in EE as (w&[(->&->)|(->&->)]).
        * apply lower_squares_alt in I1 as (E2&E3);[|reflexivity].
          revert E2 E3;unfold square;simpl_binding.
          rewrite Ev1;simpl;simpl_nat.
          intros -> [h|(h&_)];lia.
        * apply (Min w v2);[reflexivity|solve_length|].
          apply lower_squares_alt in I1 as (E2&E3);[|reflexivity].
          clear Min IHe I2 Ig Len.
          simpl_binding in E1.
          simpl_binding in Ev1.
          apply destr_bind_prod_full in E1 as (Ev2&h1).
          revert Ev2 h1;set (K:= d_binding(𝗙 a v2));intros.
          apply destr_bind_prod_full in Ev1 as (Ew&h2).
          revert Ew h2;set (N':= d_binding(𝗙 a w));intros.
          rewrite Ew in *.
          destruct (𝗙 a u1) as ((D,F),C).
          unfold square,d_binding in *;simpl in *.
          subst;clear Ev2 Ew.
          f_equal;f_equal.
          assert (L: D<=N) by lia;clear E3.
          destruct h1 as [(h1&h1')|h1];[|inversion h1;reflexivity].
          destruct h2 as [(h2&h2')|h2];[|inversion h2];lia.
  Qed. 

  Lemma splitStrict_list_lang a N e f1 f2 u1 u2 :
    is_binding_finite e -> (f1,f2) ∈ (splitStrict_list a N e) -> ⟦f1⟧ u1 -> ⟦f2⟧ u2 -> ⟦e⟧ (u1++u2).
  Proof.
    intro Be;revert N f1 f2 u1 u2;induction_bin_fin e Be;intros N f1 f2 u1 u2;simpl.
    - tauto.
    - tauto.
    - destruct_eqX ((S N,false,0):𝖡) (𝗳 a x);[|simpl;tauto].
      intros [heq|FF];[|simpl in FF;tauto].
      inversion heq;clear heq;subst.
      intros -> ->;reflexivity.
    - simpl_In;intros [I|I] I1 I2;[left;eapply IHe1|right;eapply IHe2];eassumption.
    - rewrite T;simpl_In;intros [I|I].
      + apply in_map_iff in I as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        intros Iu1 (v1&v2&->&Iv1&Iv2).
        exists (u1++v1),v2;rewrite app_ass;split;[reflexivity|split;[|assumption]].
        eapply IHe1;eassumption.
      + apply in_flat_map in I as ((b,n)&Ib&If).
        apply in_map_iff in If as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        simpl in *.
        intros (v1&v2&->&I1&I2) I3.
        exists v1,(v2++u2);rewrite app_ass;split;[reflexivity|].
        split;[|eapply IHe2;eassumption].
        apply filter_binding_lang in I1 as (I1&_);assumption.
    - rewrite T;simpl;tauto.
    - intros I.
      apply in_map_iff in I as ((g1&g2)&heq&Ig).
      symmetry in heq;inversion heq;clear heq;subst.
      intros (v1&v2&->&I1&I2) (v3&v4&->&I3&I4).
      pose proof (ka_star_mid_split ⟦e⟧) as h;apply h;clear h.
      exists (v1++v2++v3),v4;repeat rewrite app_ass;split;[reflexivity|].
      split;[|assumption].
      exists v1,(v2++v3);split;[reflexivity|].
      split;[|eapply IHe;eassumption].
      apply LowerExpr_star_lang in I1;[tauto|].
      apply sqExpr_star in Sq as (Bs&Sq);apply Bs.
  Qed.

  Lemma is_binding_finite_splitStrict_list a N e f1 f2 :
    is_binding_finite e -> (f1, f2) ∈ splitStrict_list a N e ->
    is_binding_finite f1 /\ is_binding_finite f2.
  Proof.
    intro Be;repeat rewrite <- binding_finite_spec.
    revert N f1 f2;induction_bin_fin e Be;intros N f1 f2;simpl.
    - tauto.
    - tauto.
    - destruct_eqX ((S N,false,0):𝖡) (𝗳 a x);[|simpl;tauto].
      intros [heq|FF];[|simpl in FF;tauto].
      inversion heq;clear heq;subst;simpl;tauto.
    - simpl_In;intros [I|I];[eapply IHe1|eapply IHe2];eassumption.
    - rewrite T;simpl_In;intros [I|I].
      + apply in_map_iff in I as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        simpl.
        apply IHe1 in Ig as (->&->);simpl.
        apply binding_finite_spec in B2 as ->.
        rewrite orb_true_r;tauto.
      + apply in_flat_map in I as ((b,n)&Ib&If).
        apply in_map_iff in If as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        simpl in *.
        apply IHe2 in Ig as (->&->);simpl.
        eapply is_binding_finite_filter_binding,binding_finite_spec in B1 as ->.
        rewrite orb_true_r;tauto.
    - rewrite T;simpl;tauto.
    - intros I.
      apply in_map_iff in I as ((g1&g2)&heq&Ig).
      symmetry in heq;inversion heq;clear heq;subst.
      apply sqExpr_star in Sq as (Bs&_).
      pose proof (LowerExpr_star_is_binding_finite a N true Bs) as E1.
      rewrite <- binding_finite_spec in Bs,E1.
      simpl in *;apply IHe in Ig as (->&->);rewrite Bs,E1.
      repeat rewrite orb_true_r;tauto.
  Qed.
  
  Lemma splitStrict_list_inf a N e f1 f2 :
    is_binding_finite e -> (f1, f2) ∈ splitStrict_list a N e -> f1 · f2 <=KA e.
  Proof.
    intro Be;repeat rewrite <- binding_finite_spec.
    revert N f1 f2;induction_bin_fin e Be;intros N f1 f2;simpl.
    - tauto.
    - tauto.
    - destruct_eqX ((S N,false,0):𝖡) (𝗳 a x);[|simpl;tauto].
      intros [heq|FF];[|simpl in FF;tauto].
      inversion heq;clear heq;subst;simpl.
      apply ax_eq_inf,right_unit.
    - simpl_In;intros [I|I];etransitivity;
        [eapply IHe1|apply inf_cup_left|eapply IHe2|apply inf_cup_right];eassumption.
    - rewrite T;simpl_In;intros [I|I].
      + apply in_map_iff in I as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        simpl.
        etransitivity;[apply ax_eq_inf,mon_assoc|].
        apply IHe1 in Ig as ->;simpl;reflexivity.
      + apply in_flat_map in I as ((b,n)&Ib&If).
        apply in_map_iff in If as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        simpl in *.
        etransitivity;[apply ax_eq_inf;symmetry;apply mon_assoc|].
        apply IHe2 in Ig as ->;simpl.
        apply proper_prod_inf;[apply filter_binding_inf|reflexivity];assumption.
    - rewrite T;simpl;tauto.
    - intros I.
      apply in_map_iff in I as ((g1&g2)&heq&Ig).
      symmetry in heq;inversion heq;clear heq;subst.
      etransitivity;[apply ax_eq_inf,mon_assoc|].
      etransitivity;[apply proper_prod_inf;[apply ax_eq_inf;symmetry;apply mon_assoc|reflexivity]|].
      rewrite (IHe _ g1 g2) by eassumption.
      rewrite LowerExpr_inf by (apply Sq).
      apply ka_star_mid_split.
  Qed.
  
  Lemma splitStrict_list_support a N e f1 f2 :
    is_binding_finite e -> (f1,f2) ∈ (splitStrict_list a N e) -> ⌊f1·f2⌋ ⊆ ⌊e⌋.
  Proof.
    intro Be.
    revert N f1 f2;induction_bin_fin e Be;intros N f1 f2;simpl.
    - tauto.
    - tauto.
    - destruct_eqX ((S N,false,0):𝖡) (𝗳 a x);[|simpl;tauto].
      intros [heq|FF];[|simpl in FF;tauto].
      inversion heq;clear heq;subst;simpl.
      rewrite support_prod.
      apply incl_app;[reflexivity|apply incl_nil].
    - rewrite support_join;simpl_In.
      intros [I|I];[rewrite IHe1 by eassumption|rewrite IHe2 by eassumption].
      + apply incl_appl;reflexivity.
      + apply incl_appr;reflexivity.
    - rewrite T;simpl_In;intros [I|I].
      + apply in_map_iff in I as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        transitivity ⌊(g1·g2)·e2⌋.
        * repeat rewrite support_prod.
          rewrite app_ass;reflexivity.
        * rewrite support_prod.
          apply IHe1 in Ig as ->.
          rewrite support_prod;reflexivity.
      + apply in_flat_map in I as ((b,n)&Ib&If).
        apply in_map_iff in If as ((g1&g2)&heq&Ig).
        symmetry in heq;inversion heq;clear heq;subst.
        transitivity ⌊ filter_binding a b e1 · (g1 · g2) ⌋.
        * repeat rewrite support_prod.
          rewrite app_ass;reflexivity.
        * rewrite support_prod.
          apply IHe2 in Ig as ->.
          rewrite filter_binding_support,support_prod;reflexivity.
    - rewrite T;simpl;tauto.
    - intros I.
      apply in_map_iff in I as ((g1&g2)&heq&Ig).
      symmetry in heq;inversion heq;clear heq;subst.
      apply sqExpr_star in Sq as (Bs&_).
      transitivity ⌊ LowerExpr a N true e ⋆ · (g1 · g2) · e ⋆ ⌋.
      * repeat rewrite support_prod.
        repeat rewrite app_ass;reflexivity.
      * rewrite support_prod,support_prod.
        apply IHe in Ig as ->.
        unfold LowerExpr.
        repeat rewrite support_star.
        rewrite <- Σ_support.
        repeat apply incl_app;try reflexivity.
        clear.
        intros c Ic;apply In_support_list in Ic as (f&If&Ic).
        apply in_map_iff in If as (?&<-&_).
        apply filter_binding_support in Ic;assumption.
  Qed.
  
End s.

