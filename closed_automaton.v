(** * RIS.closed_automaton : computing an automaton for the α-closure of an expression. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp automata systems.
Require Import aeq_facts alpha_regexp closed_languages binding_finite.

Section s.
  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.

  Notation Regexp := (@regexp letter).

  Definition bounded_stack A B n : list stack :=
    flat_map (lists_of_length (pairs A B)) (seq 0 (S n)).

  Definition state_space e A :=
    pairs (bounded_stack ⌊e⌋ A (2*sizeExpr e)) (stateSpace e).

  Definition transitions_from A (state : stack * Regexp) l :=
    match (state,l) with
    | (s,e,open a) => flat_map (fun f => map (fun b => ((s,e),open b,((a,b)::s,f))) A) (δA (open a) e)
    | (s,e,close a) => if (pairedb s a (image s a)) && (inb (image s a) A) then
                        map (fun f => ((s,e),close (image s a),(s⊖(a,image s a),f))) (δA (close a) e)
                      else []
    | (s,e,var x) =>
      match var_perm' ⌊x⌋ s with
      | None => []
      | Some p =>
        if inclb ⌊p∙x⌋ A
        then map (fun f => ((s,e),var (p∙x),(s,f))) (δA (var x) e)
        else []
      end
    end.

  Lemma transitions_from_spec A f s e l s1 s2 e1 e2 l' :
    (s,e)∈ state_space f A ->
    ((s1,e1),l',(s2,e2)) ∈ transitions_from A (s,e) l <->
    (s1 = s /\ e1 = e /\ ⌊l'⌋ ⊆ A /\ e2 ∈ δA l e /\ s ⊣ l | l' ↦ s2) .
  Proof.
    intro Ist.
    destruct l as [a|a|x];unfold transitions_from;simpl.
    - rewrite in_flat_map;simpl.
      split.
      + intros (e'&Ie'&I).
        apply in_map_iff in I as (b&E&Ib).
        inversion E;subst.
        split;[reflexivity|].
        split;[reflexivity|].
        split;[|split;[assumption|reflexivity]].
        intros c [<-|F];[assumption|simpl in F;tauto].
      + intros (->&->&Ib&I2&St).
        unfold step in St;destruct l' as [b| |];tauto||subst.
        exists e2;split;[assumption|].
        apply in_map_iff;exists b;split;[reflexivity|].
        apply Ib;now left.
    - case_eq (pairedb s a (image s a)).
      + intros Pb.
        apply pairedb_spec in Pb.
        case_in (image s a) A.
        * split.
          -- simpl;intros I'.
             apply in_map_iff in I' as (e'&I'&Ie').
             inversion I';subst;clear I'.
             split;[reflexivity|].
             split;[reflexivity|].
             split;[|split;[assumption|split;[assumption|reflexivity]]].
             intros c [<-|F];[assumption|simpl in F;tauto].
          -- intros (->&->&Il'&Ie2&St).
             unfold step in St;destruct l' as [|b|];try tauto.
             destruct St as (Pb'&->).
             simpl;apply in_map_iff.
             exists e2;split;[|assumption].
             replace (image s a) with b in * by (apply (paired_inj Pb' Pb);reflexivity).
             reflexivity.
        * simpl;split;[tauto|].
          intros (->&->&Il'&Ie2&St).
          unfold step in St;destruct l' as [|b|];try tauto.
          destruct St as (Pb'&->).
          replace (image s a) with b in * by (apply (paired_inj Pb' Pb);reflexivity).
          apply I,Il';now left.
      + intro Pb;simpl;split;[tauto|].
        intros (->&->&Il'&Ie2&St).
        unfold step in St;destruct l' as [|b|];try tauto.
        destruct St as (Pb'&_).
        rewrite (image_spec Pb') in *.
        apply pairedb_spec in Pb';rewrite Pb' in Pb;discriminate.
    - case_eq (var_perm' ⌊x⌋ s).
      + intros p Ep.
        case_eq (inclb ⌊ p ∙ x ⌋ A).
        * intro Incl;split.
          -- intros I;apply in_map_iff in I as (e'&E&Ie').
             inversion E;subst;clear E.
             split;[reflexivity|].
             split;[reflexivity|].
             split;[|split;[assumption|]].
             ++ apply inclb_correct in Incl.
                apply Incl.
             ++ split;[reflexivity|].
                exists p;split;[reflexivity|].
                intro a;apply var_perm'_Some,Ep.
          -- intros (->&->&Incl'&Ie2&St).
             unfold step in St;destruct l' as [| |y];try tauto.
             destruct St as (->&p'&->&hp').
             apply in_map_iff;exists e2;split;[|assumption].
             f_equal;f_equal;f_equal.
             apply var_perm'_spec in hp' as (p''&Ep''&hp').
             rewrite Ep in Ep'';inversion Ep'';subst.
             symmetry;apply support_eq_action_eq,hp'.
        * intro F;simpl;split;[tauto|].
          intros (->&->&Incl'&Ie2&St).
          unfold step in St;destruct l' as [| |y];try tauto.
          destruct St as (->&p'&->&hp').
          apply var_perm'_spec in hp' as (p''&Ep''&hp').
          rewrite Ep in Ep'';inversion Ep'';subst.
          apply support_eq_action_eq in hp'.
          apply not_true_iff_false in F;apply F,inclb_correct.
          rewrite <- hp';apply Incl'.
      + intro F;simpl;split;[tauto|].
        intros (->&->&Incl'&Ie2&St).
        unfold step in St;destruct l' as [| |y];try tauto.
        destruct St as (->&p'&->&hp').
        apply var_perm'_None in F as (a&Ia&F).
        apply (F (p'∙a)),hp',Ia.
  Qed.          
            
  Definition closed_automaton (e : Regexp) (A : list atom) : NFA (stack*Regexp) letter :=
    (filter (fun st => (prj1 (fst st) =?= prj2 (fst st)) && ϵ (snd st) =?= e_un)(state_space e A),

     flat_map (fun st => flat_map (transitions_from A st) (Var e)) (state_space e A)).


  Lemma path_support u v s1 s2 : s1 ⊣ u | v ⤅ s2 -> prj1 s2 ⊆ prj1 s1 ++ ⌊u⌋
                                                   /\ prj2 s2 ⊆ prj2 s1 ++ ⌊v⌋.
  Proof.
    intro P;split;intro a;pose proof (stack_binding_both P a) as (h1&h2);simpl_In;
      intro I;apply nb_In in I.
    - clear P h2;rewrite h1 in I;clear h1;case_in a (prj1 s1);[tauto|case_in a ⌊u⌋;[tauto|]].
      exfalso;revert I.
      apply nb_not_In in I0 as ->.
      apply αfresh_support in I1 as ->.
      simpl;simpl_binding;lia.
    - clear P h1;rewrite h2 in I;clear h2;case_in a (prj2 s1);[tauto|case_in a ⌊v⌋;[tauto|]].
      exfalso;revert I.
      apply nb_not_In in I0 as ->.
      apply αfresh_support in I1 as ->.
      simpl;simpl_binding;lia.
  Qed.

  (** We have built an automaton whose language is the set of words
      [u] such that [⌊u⌋ ⊆ A] and there is a word [v ∈ ⟦e⟧] such that
      [v≡u]. *)
  Lemma lang_close_automaton e A :
    is_binding_finite e ->
    langNFA (closed_automaton e A) ([],e) ≃ restrict (cl_α ⟦e⟧) A.
  Proof.
    intro B.
    cut (forall u s e', test0 e' = false ->
                   pathNFA (closed_automaton e A) ([],e) u (s,e')
                   <-> exists w, pathNFA (NFA_of_regexp e) e w e' /\ [] ⊣ w | u ⤅ s /\ ⌊u⌋ ⊆ A).
    - intros h u;split.
      + intros ((s'&e')&P&F).
        apply h in P as (w&P&P'&S).
        * split;[|assumption].
          unfold closed_automaton in F;simpl in F;simpl_In in F.
          destruct F as (I&E).
          apply andb_true_iff in E as (E1&E2).
          unfold state_space in I;apply pairs_spec in I.
          exists w;split.
          -- apply NFA_of_regexp_spec;exists e'.
             split;[assumption|].
             unfold NFA_of_regexp;simpl;simpl_In;tauto.
          -- apply completeness;exists s';split;[assumption|].
             apply eqX_correct;tauto.
        * case_eq (test0 e');[|reflexivity].
          intro T.
          apply test0_spec,soundness in T;simpl in T.
          exfalso;cut (𝟬 (@nil letter));[tauto|].
          apply T,ϵ_spec,eqX_correct.
          unfold closed_automaton in F;simpl in F;simpl_In in F.
          destruct F as (_&E).
          apply andb_true_iff in E as (_&E);tauto.
      + intros ((w&Iw&Ew)&I).
        pose proof Iw as Ie.
        apply NFA_of_regexp_spec in Iw as (e'&P&Ie').
        apply completeness in Ew as (s&P'&Es).
        exists (s,e');split.
        * apply h.
          -- case_eq (test0 e');[|reflexivity].
             intro T.
             apply test0_spec,soundness in T;simpl in T.
             exfalso;cut (𝟬 (@nil letter));[tauto|].
             apply T,ϵ_spec,eqX_correct.
             unfold NFA_of_regexp in Ie';simpl in Ie';simpl_In in Ie';tauto.
          -- exists w;split;[assumption|split;[assumption|assumption]].
        * unfold closed_automaton;simpl;simpl_In;split.
          -- unfold state_space;apply pairs_spec;split.
             ++ unfold bounded_stack;apply in_flat_map.
                exists (length s);split.
                ** apply in_seq;split;[lia|].
                   apply size_stack in P' as ->.
                   apply (PeanoNat.Nat.le_lt_trans _ (weight w)).
                   --- unfold weight.
                       apply sum_incr.
                       intro a;unfold size;lia.
                   --- apply (PeanoNat.Nat.le_lt_trans _ (sizeExpr e));[|lia].
                       rewrite bindFind_weight_weightExpr;eauto.
                       apply bounded_weightExpr.
                ** apply lists_of_length_spec;split;[reflexivity|].
                   intros (a,b) Is.
                   apply pairs_spec;split.
                   --- rewrite <- support_lang;eauto.
                       apply path_support in P' as (Incl&_);apply Incl.
                       apply in_map_iff;exists (a,b);simpl;tauto.
                   --- apply I.
                       apply path_support in P' as (_&Incl);apply Incl.
                       apply in_map_iff;exists (a,b);simpl;tauto.
             ++ unfold NFA_of_regexp in Ie';simpl;simpl in Ie';simpl_In in Ie';tauto.
          -- unfold NFA_of_regexp in Ie';simpl;simpl in Ie';simpl_In in Ie'.
             apply andb_true_iff;rewrite eqX_correct;tauto.
    - induction u as [|l u] using rev_induction;intros s' e';simpl.
      + split.
        * intro E;inversion E;subst; clear E.
          exists [].
          split;[reflexivity|split;[eauto|apply incl_nil]].
        * intros ([]&P1&P2&Incl).
          -- simpl in P1;inversion P2;subst;reflexivity.
          -- inversion P2.
      + intros T;split.
        * intros P2;apply pathNFA_last in P2 as ((s3&e3)&P2&I).
          unfold closed_automaton in I;simpl in I.
          apply in_flat_map in I as ((s4&e4)&Ist'&I).
          apply in_flat_map in I as (l'&Il'&I).
          pose proof I as Tr.
          rewrite transitions_from_spec in I by eassumption;destruct I as (->&->&Il&Ie4&St).
          apply IHu in P2 as (w&Pw&Pw'&Iw).
          -- exists (w++[l']);split;[|split].
             ++ apply pathNFA_last.
                exists e4;split;[assumption|].
                unfold NFA_of_regexp.
                apply in_flat_map;exists e4;split.
                ** unfold state_space in Ist';apply pairs_spec in Ist';tauto.
                ** apply in_flat_map;exists l';split;[assumption|].
                   apply in_map_iff;exists e';split;[reflexivity|assumption].
             ++ eapply path_app;eauto.
             ++ rewrite support_list_app,support_list_cons,Il,Iw;simpl;intro;simpl_In;simpl; tauto.
          -- case_eq (test0 e4);[|reflexivity].
             intro T';apply (test0_δA T') in Ie4;rewrite T in Ie4;discriminate.
        * intros (w&Pw&Pw'&Ilu).
          destruct (nil_or_last w) as [->|(l'&w'&->)];[inversion Pw';simpl_words|].
          apply path_letter in Pw' as (?&?&s&E&P'&St).
          apply app_inj_tail in E as (<-&<-).
          apply pathNFA_last in Pw as (e3&Pw&Tr).
          unfold NFA_of_regexp in Tr;simpl in Tr.
          apply in_flat_map in Tr as (?&Ie3&Tr).
          apply in_flat_map in Tr as (l''&Il'&Tr).
          apply in_map_iff in Tr as (e''&E&Ie').
          inversion E;subst.
          apply pathNFA_last;exists (s,e3);split.
          -- apply IHu.
             ++ case_eq (test0 e3);[|reflexivity].
                intro T';apply (test0_δA T') in Ie';rewrite T in Ie';discriminate.
             ++ exists w';repeat split;try assumption.
                rewrite <- Ilu,support_list_app;intro;simpl_In;tauto.
          -- assert (I3 : (s,e3) ∈ state_space e A).
             ++ unfold state_space;apply pairs_spec;split;[|assumption].
                assert (exists w, ⟦e⟧ (w'++w)) as (w&Iw).
                ** clear IHu P' l u St s s' E Ilu B A.
                   apply test0_false in T as (w&Iw).
                   exists (l'::w).
                   apply NFA_of_regexp_spec.
                   apply NFA_of_regexp_spec in Iw as (f&P&If).
                   exists f;split.
                   --- apply pathNFA_app;exists e3;split;[assumption|].
                       exists e';split;
                         [unfold NFA_of_regexp;simpl;apply in_flat_map;exists e3;split;[assumption|];
                          apply in_flat_map;exists l';split;[assumption|];apply in_map_iff;exists e';tauto|].
                       clear If Pw.
                       eapply pathNFA_stateSpace;[|apply P].
                       apply (stateSpace_trans Ie3).
                       eapply δA_stateSpace,Ie'.
                   --- revert If;unfold NFA_of_regexp;simpl;simpl_In.
                       rewrite <- (stateSpace_trans Ie3).
                       rewrite δA_stateSpace in Ie'.
                       rewrite <- (stateSpace_trans Ie').
                       tauto.
                ** unfold bounded_stack;apply in_flat_map;exists ⎢s⎥;split.
                   --- apply in_seq;split;[lia|].
                       apply is_binding_finite_memory_bound in Iw;[|assumption].
                       apply size_stack in P' as ->.
                       apply (PeanoNat.Nat.le_lt_trans _ (weight w'));[|lia].
                       unfold weight.
                       apply sum_incr.
                       intro a;unfold size;lia.
                   --- apply lists_of_length_spec;split;[reflexivity|].
                       intros (a,b) I;apply pairs_spec;split.
                       +++ apply (support_lang Iw).
                           rewrite support_list_app;simpl_In;left.
                           apply path_support in P' as (P'&_).
                           apply P',in_map_iff;exists (a,b);tauto.
                       +++ apply Ilu.
                           rewrite support_list_app;simpl_In;left.
                           apply path_support in P' as (_&P').
                           apply P',in_map_iff;exists (a,b);tauto.
             ++ apply in_flat_map;exists (s,e3);split;[assumption|].
                apply in_flat_map;exists l';split;[assumption|].
                eapply transitions_from_spec;eauto.
                repeat split.
                ** rewrite <- Ilu,support_list_app,support_list_cons;intro;simpl_In;tauto.
                ** assumption.
                ** assumption.
  Qed.

          
End s.





                           