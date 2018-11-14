(** * RIS.alphaKA : axiomatisation of regular languages up-to α-equivalence. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp aeq_facts alpha_regexp closed_languages binding_finite.
Require Import positive_regexp.
Section s.
  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.

  Inductive αKA : relation regexp :=
  | αKA_αα a b e : (forall u, ⟦e⟧ u -> a #α u /\ b #α u) -> αKA e ([(a,b)]∙e)
  | αKA_KA e f : KA e f -> αKA e f.
  Hint Constructors αKA.

  Lemma KA_αKA e f : {|KA,KA'|} ⊢ e == f ->  {|αKA,KA'|} ⊢ e == f.
  Proof. intro E;induction E;try tauto||eauto. Qed.

  Global Instance goodαKA : GoodEnoughAxiom αKA.
  Proof. split;intro;auto. Qed.
  Global Instance verygoodαKA : VeryGoodAxioms αKA.
  Proof. split;intro;auto. Qed.
  
  Lemma KA_αKA_inf e f : {|KA,KA'|} ⊢ e =<= f ->  {|αKA,KA'|} ⊢ e =<= f.
  Proof. intro;apply KA_αKA,H. Qed.
  
  Lemma αKA_lang e f : {|αKA,KA'|} ⊢ e == f -> cl_α⟦e⟧≃cl_α⟦f⟧.
  Proof.
    intros E;induction E.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - Transparent regProduct.
      simpl.
      Opaque prodLang.
      simpl; rewrite cl_α_prod,IHE1,IHE2,<- cl_α_prod;reflexivity.
    - Transparent regJoin.
      Opaque joinLang.
      simpl; rewrite cl_α_join,IHE1,IHE2,cl_α_join;reflexivity.
    - Transparent regStar.
      Opaque starLang.
      simpl;rewrite cl_α_star,IHE,<-cl_α_star;reflexivity.
    - destruct H.
      + intros u;split.
        * intros (v&I&<-);exists ([(a,b)]∙v).
          rewrite act_lang;split.
          -- rewrite act_pinv_p;assumption.
          -- symmetry;apply αequiv_αfresh_transpose.
             apply H in I as (fa&fb).
             intros c Ic;unfold act;simpl;unfold_eqX;tauto.
        * intros (v&I&<-).
          rewrite act_lang in I;simpl in I.
          rewrite (@αequiv_αfresh_transpose _ _ _ _ [(a,b)] v).
          -- apply cl_α_incr,I.
          -- intro c;apply H in I;revert I.
             repeat rewrite αfresh_perm;simpl;unfold act;simpl;simpl_eqX;unfold_eqX;tauto.
      + apply cl_α_eq_lang,soundness;auto.
    - destruct H;simpl;rewrite cl_α_join;symmetry;apply join_is_order;
        simpl in IHE;rewrite cl_α_join in IHE;symmetry in IHE;apply join_is_order in IHE.
      + rewrite cl_α_prod,<- (cl_α_idem ⟦f⟧),<-cl_α_prod;apply cl_α_inf_lang.
        apply ka_star_left_ind;apply cl_α_inf;rewrite <- IHE at 2.
        rewrite cl_α_prod,cl_α_idem,<-cl_α_prod;reflexivity.
      + rewrite cl_α_prod,<- (cl_α_idem ⟦e⟧),<-cl_α_prod;apply cl_α_inf_lang.
        apply ka_star_right_ind;apply cl_α_inf;rewrite <- IHE at 2.
        rewrite cl_α_prod,cl_α_idem,<-cl_α_prod;reflexivity.
  Qed.

  Definition OpenVar e := flat_map (fun l => match l with open a => [a] | _ => [] end) (Var e).

  Definition balExpr a e := bindings e a ⊆ [ε;(0,true,0)].
  Definition freshExpr a e := bindings e a ⊆ [ε].

  Lemma balExpr_bindFin a e : is_binding_finite e -> balExpr a e <-> (forall u, ⟦e⟧ u -> a ⋄ u).
  Proof.
    intro h;rewrite <- binding_finite_spec in h;unfold balExpr;split.
    - intros I u Iu.
      cut (𝗙 a u ∈ [ε; (0, true, 0)]).
      + unfold balanced;intros [<-|[<-|F]];[| |exfalso;apply F];split;reflexivity.
      + apply I,binding_finite_true;assumption.
    - intros hL b Ib.
      apply bindings_witness in Ib as (u&Iu&<-).
      apply hL in Iu as (h1&h2).
      destruct (𝗙 a u) as ((n,m),p);unfold d_binding in h2;simpl in *;subst.
      destruct m;tauto.
  Qed.

  Lemma freshExpr_bindFin a e : is_binding_finite e -> freshExpr a e <-> (forall u, ⟦e⟧ u -> a #α u).
  Proof.
    intro h;rewrite <- binding_finite_spec in h;unfold freshExpr;split.
    - intros I u Iu.
      cut (𝗙 a u ∈ [ε]).
      + unfold fresh__α;intros [<-|F];[ |exfalso;apply F];reflexivity.
      + apply I,binding_finite_true;assumption.
    - intros hL b Ib.
      apply bindings_witness in Ib as (u&Iu&<-).
      apply hL in Iu as ->;now left.
  Qed.

  Definition balExprB a e := inclb (bindings e a) [ε;(0,true,0)].
  Definition freshExprB a e := inclb (bindings e a) [ε].

  Lemma balExprB_balExpr a e : balExprB a e = true <-> balExpr a e.
  Proof. apply inclb_correct. Qed.
  Lemma freshExprB_freshExpr a e : freshExprB a e = true <-> freshExpr a e.
  Proof. apply inclb_correct. Qed.

  
  Notation Regexp := (@regexp letter).

  Lemma δ_inf_e_α e l : {|αKA, KA'|}⊢ ⟪ l ⟫ · δ l e =<= e.
  Proof. apply KA_αKA_inf,δ_inf_e. Qed.
  Lemma Σ_bounded_α e L:
    (forall f, f ∈ L ->  {|αKA, KA'|}⊢ f =<= e) <->  {|αKA, KA'|}⊢ Σ L =<= e.
  Proof.
    induction L;simpl.
    - split.
      + intros h;apply KA_αKA;auto.
      + intros _ f F;tauto.
    - split.
      + intros h;apply inf_join_inf.
        * apply h;tauto.
        * rewrite <- IHL;intros f If.
          apply h;now right.
      + intros h f [<-|If].
        * rewrite <- h;apply inf_cup_left.
        * apply IHL.
          -- rewrite <- h;apply inf_cup_right.
          -- assumption.
  Qed.

  Lemma δ_binFin a e : is_binding_finite e -> is_binding_finite (δ a e).
  Proof.
    intros (B&h).
    unfold is_binding_finite;setoid_rewrite <- δ_lang.
    destruct a.
    - exists ((flat_map
                 (fun b => match b with
                           | (0,false,S n) => [(0,false,n);(0,true,n);(1,false,S n)]
                           | ((n,m),p) => [(S n,m,p)]
                           end)
                 B)++B).
      intros b u I;simpl.
      apply (h b) in I.
      revert I;simpl_binding;simpl;simpl_In;unfold_eqX;subst.
      + destruct (𝗙 a u) as (([|[|n]],m),p);unfold prod_binding;simpl;simpl_nat;intro I;left.
        * apply in_flat_map;exists (0,false,S p).
          replace (S p) with (p+1) by lia.
          split;[assumption|].
          simpl;destruct m;tauto.
        * apply in_flat_map;exists (0,m,p).
          split;[assumption|].
          destruct m;destruct p;simpl;tauto.
        * apply in_flat_map;exists (S n,m,p).
          split;[assumption|].
          simpl;tauto.
      + rewrite prod_unit_l;tauto.  
    - exists ((flat_map
                 (fun b => match b with
                           | ((S n,m),p) => [(n,m,p)]
                           | _ => []
                           end)
                 B)++B).
      intros b u I;simpl.
      apply (h b) in I.
      revert I;simpl_binding;simpl;simpl_In;unfold_eqX;subst.
      + destruct (𝗙 a u) as (([|n],m),p);unfold prod_binding;simpl;simpl_nat;intro I;left.
        * apply in_flat_map;exists (1,m,p).
          split;[assumption|];simpl;tauto.
        * apply in_flat_map;exists (S(S n),m,p).
          split;[assumption|];simpl;tauto.
      + rewrite prod_unit_l;tauto.
    - exists ((flat_map
                 (fun b => match b with
                           | ((0,true),p) => [(0,false,p)]
                           | _ => []
                           end)
                 B)++B).
      intros b u I;simpl.
      apply (h b) in I.
      revert I;simpl_binding;simpl;simpl_In;case_in b ⌊x⌋;simpl. 
      + destruct (𝗙 b u) as (([|n],m),p);unfold prod_binding;simpl;simpl_nat;intro I'.
        * destruct m;[tauto|].
          left;apply in_flat_map;exists (0,true,p).
          split;[assumption|];simpl;tauto.
        * tauto.
      + rewrite prod_unit_l;tauto.
  Qed.

  Lemma δ_support e l : ⌊δ l e⌋ ⊆ ⌊ e ⌋.
  Proof.
    induction e;simpl;try reflexivity.
    - unfold support in *;simpl;rewrite IHe1,IHe2;reflexivity.
    - destruct_eqX (ϵ e1) 𝟭.
      + unfold support in *;simpl;rewrite IHe1,IHe2;intro;simpl_In;tauto.
      + unfold support in *;simpl;rewrite IHe1;intro;simpl_In;tauto.
    - unfold support in *;simpl;rewrite IHe;intro;simpl_In;tauto.
    - destruct (eq_letter l x);simpl;intro;simpl;tauto.
  Qed.

  Lemma 𝐇_support e f : f ∈ 𝐇 e -> ⌊f⌋ ⊆ ⌊e⌋.
  Proof.
    Transparent 𝐇.
    revert f;induction e;intro f;simpl.
    - tauto.
    - intros [<-|F];[reflexivity|tauto].
    - simpl_In;unfold support in *;simpl.
      firstorder.
    - rewrite lift_prod_spec;intros (f1&f2&I1&I2&->).
      unfold support in *;simpl.
      rewrite (IHe1 _ I1),(IHe2 _ I2);reflexivity.
    - rewrite in_flat_map.
      intros (A&I__A&If).
      apply in_map_iff in If as (M&<-&I__M).
      unfold support in *;simpl.
      cut (forall f, f ∈ M -> ⌊f⌋⊆⌊e⌋).
      + intros I;assert (E:⌊Σ M⌋⊆⌊e⌋).
        * rewrite <- Σ_support.
          intros a Ia;apply In_support_list in Ia as (f&If&Ia).
          apply (I f If),Ia.
        * generalize dependent (Σ M).
          clear A I__A I__M IHe;intros.
          induction M;simpl.
          -- rewrite E,app_nil_r;reflexivity.
          -- rewrite E at 1.
             rewrite (I a) by (now left).
             rewrite IHM.
             ++ intro;simpl_In;tauto.
             ++ intros f If;apply I;now right.
      + intros f If.
        apply IHe,(subsets_In I__A),(shuffles_equiv I__M),If.
    - intros [<- |F];[reflexivity|tauto].
      Opaque 𝐇.
  Qed.
  
  Lemma spines_support e e1 e2 : (e1,e2)∈ spines e -> ⌊e1⌋++⌊e2⌋ ⊆ ⌊e⌋.
  Proof.
    revert e1 e2;induction e;intros f1 f2;simpl.
    - tauto.
    - intros [E|F];[|tauto].
      inversion E;subst;intro;simpl_In;tauto.
    - simpl_In;intros [I|I].
      + rewrite IHe1 by assumption.
        unfold support;simpl;intro;simpl_In;tauto.
      + rewrite IHe2 by assumption.
        unfold support;simpl;intro;simpl_In;tauto.
    - simpl_In;intros [I|I].
      + apply in_flat_map in I as ((g1&g2)&I1&I2).
        apply in_map_iff in I2 as (f'&E&I2).
        inversion E;subst;clear E.
        unfold support in *;simpl.
        apply 𝐇_support in I2.
        apply IHe1 in I1.
        unfold support in *;intro;simpl in *;simpl_In in *;firstorder.
      + apply in_flat_map in I as ((g1&g2)&I1&I2).
        apply in_map_iff in I2 as (f'&E&I2).
        inversion E;subst;clear E.
        unfold support in *;simpl.
        apply 𝐇_support in I2.
        apply IHe2 in I1.
        unfold support in *;intro;simpl in *;simpl_In in *;firstorder.
    - simpl_In;intros [I|I].
      + apply in_flat_map in I as (e'&I1&I2).
        apply in_map_iff in I2 as (e''&E&I2).
        inversion E;subst;clear E.
        unfold support in *;simpl.
        apply 𝐇_support in I1. 
        apply 𝐇_support in I2.
        rewrite I1,I2.
        unfold support in *;intro;simpl in *;simpl_In in *;firstorder.
      + apply in_flat_map in I as ((g1&g2)&I1&I2).
        apply in_flat_map in I2 as (e1&I2&I3).
        apply in_map_iff in I3 as (e2&E&I3).
        inversion E;subst;clear E.
        unfold support in *;simpl.
        apply 𝐇_support in I2.
        apply 𝐇_support in I3.
        apply IHe in I1.
        unfold support in *;intro;simpl in *;simpl_In in *;firstorder.
    - intros [E|[E|F]];tauto||(inversion E;subst);intro;simpl_In;simpl;tauto.
  Qed.

  Lemma act_prod p e1 e2 : p ∙ (e1 · e2) = p∙ e1 · p ∙e2.
  Proof. reflexivity. Qed.
  Lemma act_join p e1 e2 : p ∙ (e1 ∪ e2) = p∙ e1 ∪ p ∙e2.
  Proof. reflexivity. Qed.
  Lemma act_star p e : p ∙ (e⋆) = (p∙ e)⋆.
  Proof. reflexivity. Qed.

  Lemma In_OpenVar a u e : open a ∈ u -> ⟦e⟧ u -> a ∈ OpenVar e.
  Proof.
    intros Ia Iu;unfold OpenVar;simpl.
    apply in_flat_map;exists (open a);split;[|simpl;tauto].
    apply (Var_spec Iu),Ia.
  Qed.

  Transparent joinLang.
  Remark cl_α_Σ L u : (cl_α ⟦Σ L⟧) u <-> exists e, e ∈ L /\ (cl_α ⟦e⟧) u.
  Proof.
    induction L;simpl.
    - split.
      + intros (w&Iw&_);exfalso;apply Iw.
      + intros (e&F&_);exfalso;apply F.
    - rewrite (cl_α_join _ _ u);simpl.
      unfold join,joinLang;rewrite IHL;clear IHL.
      firstorder subst.
      left;exists x0;tauto.
  Qed.
  Opaque joinLang.

  Lemma balanced_alt a u : a ⋄ u <-> 𝗙 a u ∈ [ε;(0,true,0)].
  Proof.
    unfold balanced;destruct (𝗙 a u) as ((n,k),m);simpl_binding.
    split.
    - intros (->&->);destruct k;tauto.
    - intros [E|[E|E]];inversion E;subst;tauto.
  Qed.
  Lemma αfresh_alt a u : a #α u <-> 𝗙 a u ∈ [ε].
  Proof.
    unfold fresh__α;destruct (𝗙 a u) as ((n,k),m);simpl_binding.
    split.
    - intros ->;now left. 
    - intros [<-|F];[reflexivity|exfalso;apply F]. 
  Qed.

  Lemma perm_comm_pair a b (u:list letter) : [(a,b)] ∙ u = [(b,a)] ∙ u.
  Proof.
    apply equiv_perm_act;[|reflexivity].
    intro;simpl;unfold act;simpl;unfold_eqX;reflexivity.
  Qed.
  Lemma αKA_lang_inf e f : {|αKA,KA'|} ⊢ e =<= f -> cl_α⟦e⟧ ≲ cl_α ⟦f⟧.
  Proof.
    intros E;unfold ax_inf in E.
    apply αKA_lang in E;simpl in E.
    rewrite cl_α_join in E.
    apply join_is_order;symmetry;apply E.
  Qed.

  Global Instance αKA_KleeneAlgebra : KleeneAlgebra Regexp (ax_eq αKA KA') (ax_inf αKA KA').
  Proof.
    repeat split;repeat intro.
    - rewrite H,H0;reflexivity.
    - rewrite H,H0;reflexivity.
    - rewrite H;reflexivity.
    - apply KA_αKA;auto.
    - apply KA_αKA;auto.
    - apply KA_αKA;auto.
    - apply KA_αKA;auto.
    - apply KA_αKA;auto.
    - apply KA_αKA;eauto.
    - apply KA_αKA;auto.
    - apply KA_αKA;auto.
    - apply KA_αKA;auto.
    - apply KA_αKA;auto.
    - apply KA_αKA;auto.
    - apply KA_αKA;auto.
    - unfold ax_inf in H;rewrite H;reflexivity.
    - unfold ax_inf;rewrite <- H;reflexivity.
    - apply KA_αKA;auto.
    - eapply ax_eq_ax',H;auto.
    - eapply ax_eq_ax',H;auto.
  Qed.
  

  Lemma Σ_map_equiv_α {A} f g (L : list A) :
    (forall e, e ∈ L -> {|αKA, KA'|}⊢ f e == g e) ->
    {|αKA, KA'|} ⊢ Σ (map f L) == Σ (map g L).
  Proof.
    intro hyp.
    induction L as [|e L].
    - reflexivity.
    - simpl;rewrite (hyp e) by (now left).
      apply ax_eq_add;[reflexivity|].
      apply IHL;intros;apply hyp;now right.
  Qed.

  Lemma δ_proper_αKA_not_open l :
    (forall a, l <> open a) ->
    Proper ((ax_eq αKA KA') ==> (ax_eq αKA KA')) (δ l).
  Proof.
    intros Nl e1 e2 E;induction E.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - simpl;unfold_eqX.
      + rewrite IHE1,IHE2,E2;reflexivity.
      + exfalso.
        apply αKA_lang in E1.
        apply ϵ_spec,cl_α_nil,E1,cl_α_nil,ϵ_spec in E.
        apply N,E.
      + exfalso.
        apply αKA_lang in E1.
        apply ϵ_spec,cl_α_nil,E1,cl_α_nil,ϵ_spec in E.
        apply N,E.
      + rewrite IHE1,E2;reflexivity.
    - simpl;rewrite IHE1,IHE2;reflexivity.
    - simpl;rewrite IHE,E;reflexivity.
    - destruct H as [a b e h|e f h];simpl.
      + case_eq (test0 (δ l e)).
        * intros T0;apply test0_spec in T0;rewrite (KA_αKA T0) at 1.
          destruct_eqX a b;[rewrite perm_a_a_eq_nil,act_nil;symmetry;apply KA_αKA,T0|].
          case_eq (test0 (δ l ([(a,b)]∙e))).
          -- intros T1;apply test0_spec in T1;rewrite (KA_αKA T1);reflexivity.
          -- intros T1;exfalso;apply test0_false in T1 as (u&Iu).
             apply δ_lang,act_lang in Iu;simpl in Iu.
             pose proof (h _ Iu) as (Ea&Eb).
             revert Ea Eb;repeat rewrite αfresh_perm;unfold fresh__α;simpl_binding.
             unfold act;simpl;simpl_eqX.
             revert Iu;rewrite act_lists_cons.
             destruct l as [c|c|x];[exfalso;apply (Nl c);reflexivity| |];simpl.
             ++ unfold act at 1;simpl;unfold act at 1;simpl;unfold_eqX.
                ** intros _ _;destruct (𝗙 a u) as (([],?),?);
                     unfold prod_binding;simpl;clear;discriminate.
                ** intros _;destruct (𝗙 b u) as (([],?),?);
                     unfold prod_binding;simpl;clear;discriminate.
                ** intros I _ _;apply δ_lang,(soundness T0) in I.
                   apply I.
             ++ case_in a ⌊x⌋;[|case_in b ⌊x⌋].
                ** intros _ _;destruct (𝗙 a u) as (([],?),?);
                     unfold prod_binding;simpl;clear;discriminate.
                ** intros _;destruct (𝗙 b u) as (([],?),?);
                     unfold prod_binding;simpl;clear;discriminate.
                ** rewrite (@action_invariant _ _ _ _ _ _ (var x) [(a,b)]).
                   --- intros Iu _ _;apply δ_lang,(soundness T0) in Iu.
                       apply Iu.
                   --- unfold support;simpl.
                       apply map_eq_id.
                       intros c Ic;unfold act;simpl.
                       unfold_eqX;subst;reflexivity||(exfalso;apply I,Ic)||(exfalso;apply I0,Ic).
        * intros T0;apply test0_false in T0 as (u&Iu).
          cut (a # l /\ b # l /\ forall u, ⟦δ l e⟧ u -> a #α u /\ b #α u).
          -- intros (Fa&Fb&Fe).
             etransitivity;[apply ax_eq_ax,αKA_αα,Fe|].
             rewrite δ_act,(@action_invariant _ _ _ _ _ _ l).
             ++ reflexivity.
             ++ simpl;apply map_eq_id.
                intros c Ic;unfold act;simpl.
                unfold_eqX;subst;reflexivity||(exfalso;apply Fa,Ic)||(exfalso;apply Fb,Ic).
          -- cut (forall u, ⟦ δ l e ⟧ u -> (a # l) /\ (b # l) /\ a #α u /\ b #α u);
               [intros h';split;[apply (h' u Iu)|split;[apply (h' u Iu)|apply h']]|].
             clear u Iu.
             intros u Iu;apply δ_lang in Iu.
             pose proof (h _ Iu) as (Ea&Eb).
             revert Ea Eb;unfold fresh__α;simpl_binding.
             destruct l as [c|c|x];[exfalso;apply (Nl c);reflexivity| |];clear;simpl.
             ++ destruct_eqX a c;[|destruct_eqX b c;[|]].
                ** destruct (𝗙 c u) as (([],?),?);
                     unfold prod_binding;simpl;clear;discriminate.
                ** destruct (𝗙 c u) as (([],?),?);
                     unfold prod_binding;simpl;clear;discriminate.
                ** now repeat rewrite prod_unit_l;firstorder.
             ++ case_in a ⌊x⌋;[|case_in b ⌊x⌋].
                ** destruct (𝗙 a u) as (([],?),?);
                     unfold prod_binding;simpl;clear;discriminate.
                ** destruct (𝗙 b u) as (([],?),?);
                     unfold prod_binding;simpl;clear;discriminate.
                ** now repeat rewrite prod_unit_l;firstorder.
      + apply KA_αKA,δ_proper_KA,ax_eq_ax,h.
    - destruct H;simpl in *;revert IHE;simpl_eqX;unfold_eqX;intros IHE.
      + rewrite <- (mon_assoc _ _ _) in IHE.
        rewrite (ka_idem _) in IHE.
        cut ({|αKA, KA'|}⊢ e⋆·f =<= f).
        * intro L.
          rewrite <- (mon_assoc _ _ _).
          rewrite (ka_idem _).
          cut ({|αKA, KA'|}⊢ (δ l e · e ⋆) · f =<= δ l f);[intro H;apply H|].
          rewrite <- (mon_assoc _ _ _).
          rewrite L.
          apply IHE.
        * eapply ax_eq_ax';[|apply E].
          auto.
      + cut ({|αKA, KA'|}⊢ e⋆·f =<= f).
        * intro L.
          rewrite <- (mon_assoc _ _ _).
          rewrite (ka_idem _).
          cut ({|αKA, KA'|}⊢ (δ l e · e ⋆) · f =<= δ l f);[intro H;apply H|].
          rewrite <- (mon_assoc _ _ _).
          rewrite L.
          apply IHE.
        * eapply ax_eq_ax';[|apply E].
          auto.
      + cut ({|αKA, KA'|}⊢ δ l e · f ⋆ ∪ δ l f · f ⋆ =<= δ l e);[intro H;apply H|].
        transitivity (δ l e · f ⋆ ∪ δ l e · f ⋆).
        * apply proper_join_inf;[reflexivity|].
          apply proper_prod_inf;[|reflexivity].
          etransitivity;[|apply IHE].
          apply inf_cup_right.
        * rewrite (ka_idem _).
          eapply ax_eq_ax';[apply KA_star_right_ind|].
          cut ({|αKA, KA'|}⊢ δ l e · f =<= δ l e);[intro H;apply H|].
          transitivity (δ l e · f ∪ δ l f);[apply inf_cup_left|apply IHE].
      + cut ({|αKA, KA'|}⊢ δ l e · f ⋆ =<= δ l e);[intro H;apply H|].
        eapply ax_eq_ax';[apply KA_star_right_ind|].
        cut ({|αKA, KA'|}⊢ δ l e · f =<= δ l e);[intro H;apply H|apply IHE].
  Qed.

  Lemma δ_proper_αKA_not_open_inf l :
    (forall a, l <> open a) ->
    Proper ((ax_inf αKA KA') ==> (ax_inf αKA KA')) (δ l).
  Proof.
    intros F e1 e2 E.
    apply (δ_proper_αKA_not_open F) in E.
    simpl in E;apply E.
  Qed.

  Lemma positive_αKA e f : {|αKA,KA'|} ⊢ e == f -> {|αKA,KA'|} ⊢ positive e == positive f.
  Proof.
    intro Eq;induction Eq.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - simpl;rewrite IHEq1,IHEq2,Eq1,Eq2;reflexivity.
    - simpl;rewrite IHEq1,IHEq2;reflexivity.
    - simpl;rewrite IHEq,Eq;reflexivity.
    - destruct H.
      + rewrite positive_act.
        apply ax_eq_ax,αKA_αα.
        intros u;rewrite positive_lang.
        intros (Iu&_);apply H;assumption.
      + apply KA_αKA,positive_KA,ax_eq_ax,H.
    - destruct H;simpl in *.
      + assert (Eq' : {|αKA, KA'|}⊢ e · f =<= f) by apply Eq;clear Eq.
        assert (IH : {|αKA, KA'|}⊢ (positive e · f ∪ e · positive f) =<= positive f)
          by apply IHEq;clear IHEq.
        cut ({|αKA, KA'|}⊢ ((positive e · e ⋆) · f ∪ e ⋆ · positive f) =<= positive f);
          [intro h;apply h|].
        apply inf_join_inf.
        * rewrite <- (KA_αKA (positive_star e)).
          rewrite <- star_switch_side,<- (mon_assoc _ _ _).
          etransitivity;[|apply ka_star_left_ind].
          -- apply proper_prod_inf;[reflexivity|].
             etransitivity;[|apply IH].
             apply inf_cup_left.
          -- etransitivity;[|apply IH].
             etransitivity;[|apply inf_cup_left].
             apply proper_prod_inf;[reflexivity|].
             apply KA_αKA_inf,positive_inf.
        * apply ka_star_left_ind.
          etransitivity;[|apply IH].
          apply inf_cup_right.
      + assert (Eq' : {|αKA, KA'|}⊢ e · f =<= e) by apply Eq;clear Eq.
        assert (IH : {|αKA, KA'|}⊢ (positive e · f ∪ e · positive f) =<= positive e)
          by apply IHEq;clear IHEq.
        cut ({|αKA, KA'|}⊢ (positive e · f ⋆ ∪ e · (positive f · f⋆)) =<= positive e);
          [intro h;apply h|].
        apply inf_join_inf.
        * apply ka_star_right_ind.
          etransitivity;[|apply IH].
          apply inf_cup_left.
        * rewrite <- (KA_αKA (positive_star f)).
          rewrite (mon_assoc _ _ _).
          etransitivity;[|apply ka_star_right_ind].
          -- apply proper_prod_inf;[|reflexivity].
             etransitivity;[|apply IH].
             apply inf_cup_right.
          -- etransitivity;[|apply IH].
             etransitivity;[|apply inf_cup_right].
             apply proper_prod_inf;[|reflexivity].
             apply KA_αKA_inf,positive_inf.
  Qed.

  Lemma positive_αKA_inf e f : {|αKA,KA'|} ⊢ e =<= f -> {|αKA,KA'|} ⊢ positive e =<= positive f.
  Proof. apply positive_αKA. Qed.

  Infix " =α " := (ax_eq αKA KA') (at level 80).
  Infix " <=α " := (ax_inf αKA KA') (at level 80).

  Lemma αKA_act p e f : e =α f -> p ∙ e =α p ∙ f.
  Proof.
    intro eq;induction eq.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - unfold act;simpl;replace actReg with act by reflexivity;rewrite IHeq1,IHeq2;reflexivity.
    - unfold act;simpl;replace actReg with act by reflexivity;rewrite IHeq1,IHeq2;reflexivity.
    - unfold act;simpl;replace actReg with act by reflexivity;rewrite IHeq;reflexivity.
    - destruct H as [b c e h|e f h];[|apply KA_αKA,KA_act,ax_eq_ax,h].
      etransitivity;[apply ax_eq_ax,(@αKA_αα (p∙b) (p∙c))|].
      + intros u Iu;apply act_lang,h in Iu.
        repeat rewrite αfresh_perm,inverse_inv in Iu.
        assumption.
      + repeat rewrite action_compose.
        erewrite equiv_perm_act;[reflexivity| |reflexivity].
        intro a;repeat rewrite <- action_compose;unfold act at 1 6;simpl.
        destruct_eqX a b;[reflexivity|].
        destruct_eqX a c;unfold_eqX.
        * reflexivity.
        * reflexivity.
        * exfalso;eapply N,act_bij;eassumption.
        * exfalso;eapply N0,act_bij;eassumption.
        * reflexivity.
    - destruct H as [e f|e f];unfold act;simpl;replace actReg with act by reflexivity;
        (eapply ax_eq_ax';[|apply IHeq]).
      + apply KA_star_left_ind.
      + apply KA_star_right_ind.
  Qed.
  
  Lemma test0_αKA  e f : e =α f -> test0 e = test0 f.
  Proof.
    case_eq (test0 e);case_eq (test0 f);[reflexivity| | |reflexivity].
    - intros Iu E.
      apply test0_spec,KA_αKA in E as ->.
      intros E;apply test0_false in Iu as (u&Iu).
      cut (cl_α ⟦e_zero⟧ u).
      + intros (?&F&_);exfalso;apply F.
      + eapply αKA_lang;[apply E|].
        exists u;split;[assumption|reflexivity].
    - intros E Iu.
      apply test0_spec,KA_αKA in E as ->.
      intros E;apply test0_false in Iu as (u&Iu).
      cut (cl_α ⟦e_zero⟧ u).
      + intros (?&F&_);exfalso;apply F.
      + eapply αKA_lang;[symmetry;apply E|].
        exists u;split;[assumption|reflexivity].
  Qed.
  
  Lemma ϵ_αKA  e f : e =α f -> ϵ e = ϵ f.
  Proof.
    intro E;apply αKA_lang in E.
    destruct (ϵ_zero_or_un e) as [E1|E1];rewrite E1.
    - symmetry;apply ϵ_spec.
      cut (cl_α ⟦f⟧ []).
      + intros (u&Iu&Eu).
        destruct u;[apply Iu|apply αequiv_length in Eu;discriminate].
      + apply E;exists [];split;[|reflexivity].
        apply ϵ_spec,E1.
    - symmetry;apply ϵ_zero.
      cut (~ cl_α ⟦f⟧ []).
      + intros h Iu;apply h;exists [];split;[assumption|reflexivity].
      + rewrite <- (E []);intros (u&Iu&Eu).
        destruct u;[|apply αequiv_length in Eu;discriminate].
        apply ϵ_zero in E1;tauto.
  Qed.

  Lemma Σ_map_app {A} (f g : A -> Regexp) L :
    Σ (map f L) ∪ Σ (map g L) =α Σ (map (fun x => f x ∪ g x) L).
  Proof.
    apply ax_inf_PartialOrder;unfold Basics.flip;split.
    - apply inf_join_inf;apply Σ_bounded;intros e Ie;apply in_map_iff in Ie as (a&<-&Ia);
        (transitivity (f a ∪ g a);[|apply Σ_bigger;apply in_map_iff;exists a;tauto]).
      + apply inf_cup_left.
      + apply inf_cup_right.
    - apply Σ_bounded;intros e Ie;apply in_map_iff in Ie as (a&<-&Ia).
      apply inf_join_inf.
      + etransitivity;[|apply inf_cup_left].
        apply Σ_bigger,in_map_iff;exists a;tauto.
      + etransitivity;[|apply inf_cup_right].
        apply Σ_bigger,in_map_iff;exists a;tauto.
  Qed.

  Lemma is_binding_finite_ax_eq e f : 
    e =α f -> is_binding_finite e <-> is_binding_finite f.
  Proof.
    intro E;apply αKA_lang in E.
    split;intros (B&IB);exists B;intros a u Iu.
    - cut (cl_α ⟦e⟧ u);[|apply E;exists u;split;[assumption|reflexivity]].
      intros (v&Iv&Ev).
      rewrite <- (αequiv_binding Ev);apply IB,Iv.
    - cut (cl_α ⟦f⟧ u);[|apply E;exists u;split;[assumption|reflexivity]].
      intros (v&Iv&Ev).
      rewrite <- (αequiv_binding Ev);apply IB,Iv.
  Qed.

  Lemma is_binding_finite_ax_inf e f : is_binding_finite f -> e <=α f -> is_binding_finite e.
  Proof.
    intros Bf E;apply (is_binding_finite_ax_eq E),binding_finite_spec in Bf.
    simpl in Bf;apply andb_true_iff in Bf as (Be&_);apply binding_finite_spec,Be.
  Qed.

  Lemma αKA_inf_act p e f : e <=α f -> p∙e <=α p∙f.
  Proof. intros E;apply (αKA_act p) in E;apply E. Qed.


End s.

Infix " =α " := (ax_eq αKA KA') (at level 80).
Infix " <=α " := (ax_inf αKA KA') (at level 80).

