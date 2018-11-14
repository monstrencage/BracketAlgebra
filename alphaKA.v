Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp aeq_facts alpha_regexp closed_languages binding_finite.
Require Import positive_regexp.
Section s.
  Context {atom : Set}{𝐀 : Atom atom}.
  Context {X : Set} {𝐗 : Alphabet 𝐀 X}.

  (** * Axiomatisation *)
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

  (* Definition δα c l e := *)
  (*   match l with *)
  (*   | open a => δ l e ∪ Σ (flat_map *)
  (*                           (fun b => *)
  (*                              flat_map *)
  (*                                (fun E => *)
  (*                                   if freshExprB a (fst E) *)
  (*                                   then [[(a,b)]∙fst E·⟪close a⟫·(δ(close b) (snd E))] *)
  (*                                   else *)
  (*                                     flat_map *)
  (*                                       (fun F => *)
  (*                                          flat_map *)
  (*                                            (fun f' => *)
  (*                                               map *)
  (*                                                 (fun F' => *)
  (*                                                    ([(a,b)]∙fst F) *)
  (*                                                      ·⟪open c⟫ *)
  (*                                                      ·([(a,b);(a,c)]∙f') *)
  (*                                                      ·⟪close a⟫ *)
  (*                                                      ·([(a,c)]∙fst F') *)
  (*                                                      ·⟪close c⟫ *)
  (*                                                      ·δ (close a) (snd F') *)
  (*                                                 ) *)
  (*                                                 ((fun p => balExprB a (f' · fst p)) *)
  (*                                                    :> spines (δ(close b)(snd E)))) *)
  (*                                            (𝐇 (δ (open a) (snd F)))) *)
  (*                                       ((fun p => freshExprB a (fst p)) :> spines (fst E)) *)
  (*                                ) *)
  (*                                ((fun p => balExprB b (fst p)) :> spines (δ (open b) e))) *)
  (*                           ((fun b => negb(a=?=b)):>OpenVar e)) *)
  (*   | l => δ l e *)
  (*   end. *)
    
  (* Lemma δα_spec c l e : *)
  (*   c # e -> *)
  (*   is_binding_finite e -> *)
  (*   ({|αKA,KA'|} ⊢ ⟪l⟫·δα c l e =<= e) *)
  (*   /\ δ l e <=KA δα c l e *)
  (*   /\ (forall w, cl_α ⟦e⟧ (l::w) <-> cl_α ⟦δα c l e⟧ w). *)
  (* Proof. *)
  (*   intros Fc B;cut  (({|αKA,KA'|} ⊢ ⟪l⟫·δα c l e =<= e) *)
  (*                 /\ δ l e <=KA δα c l e *)
  (*                 /\ (forall w, cl_α ⟦e⟧ (l::w) -> cl_α ⟦δα c l e⟧ w)); *)
  (*   [intros (h1&h2&h3);split;[assumption|split;[assumption|intros w;split;[apply h3|]]]; *)
  (*    intros (u&Iu&Eu);eapply (αKA_lang_inf h1);exists (l::u);split; *)
  (*    [exists[l],u;split;[reflexivity|split;[reflexivity|assumption]]|apply αl,Eu]|]. *)
  (*   destruct l as [a|a|x]. *)
  (*   - simpl;set (L:= *)
  (*                   flat_map *)
  (*                     (fun b => *)
  (*                        flat_map *)
  (*                          (fun E => *)
  (*                             if freshExprB a (fst E) *)
  (*                             then [[(a,b)]∙fst E·⟪close a⟫·(δ(close b) (snd E))] *)
  (*                             else *)
  (*                               flat_map *)
  (*                                 (fun F => *)
  (*                                    flat_map *)
  (*                                      (fun f' => *)
  (*                                         map *)
  (*                                           (fun F' => *)
  (*                                              ([(a,b)]∙fst F) *)
  (*                                                ·⟪open c⟫ *)
  (*                                                ·([(a,b);(a,c)]∙f') *)
  (*                                                ·⟪close a⟫ *)
  (*                                                ·([(a,c)]∙fst F') *)
  (*                                                ·⟪close c⟫ *)
  (*                                                ·δ (close a) (snd F') *)
  (*                                           ) *)
  (*                                           ((fun p => balExprB a (f' · fst p)) *)
  (*                                              :> spines (δ(close b)(snd E)))) *)
  (*                                      (𝐇 (δ (open a) (snd F)))) *)
  (*                                 ((fun p => freshExprB a (fst p)) :> spines (fst E)) *)
  (*                          ) *)
  (*                          ((fun p => balExprB b (fst p)) :> spines (δ (open b) e))) *)
  (*                     ((fun b => negb(a=?=b)):>OpenVar e)). *)
  (*     split;[|split]. *)
  (*     + transitivity (⟪ open a ⟫ · δ (open a) e ∪ ⟪ open a ⟫ ·Σ L);[apply ax_eq_inf;auto|]. *)
  (*       apply inf_join_inf. *)
  (*       * apply δ_inf_e_α. *)
  (*       * rewrite (KA_αKA (Σ_distr_l _ _)). *)
  (*         apply Σ_bounded_α. *)
  (*         intros f If. *)
  (*         apply in_map_iff in If as (e'&<-&If). *)
  (*         unfold L in If;clear L. *)
  (*         apply in_flat_map in If as (b&Ib&If). *)
  (*         apply in_flat_map in If as ((e1&e2)&Il&If). *)
  (*         simpl_In in Il;rewrite balExprB_balExpr in Il. *)
  (*         destruct Il as (I__E&B1);simpl in *. *)
  (*         simpl_In in Ib;destruct Ib as (Ib&Nb). *)
  (*         apply negb_true_iff,eqX_false in Nb. *)
  (*         case_eq (freshExprB a e1). *)
  (*         -- intros F1;rewrite F1 in *. *)
  (*            destruct If as [<-|F];[|exfalso;apply F]. *)
  (*            apply freshExprB_freshExpr in F1. *)
  (*            rewrite <- (δ_inf_e_α e (open b)). *)
  (*            transitivity  (⟪ open b ⟫ · (e1·(⟪close b⟫· δ (close b) e2))). *)
  (*            ++ apply ax_eq_inf. *)
  (*               repeat rewrite (KA_αKA (ax_eq_ax _ (KA_prod_assoc _ _ _))). *)
  (*               apply ax_eq_prod;[|reflexivity]. *)
  (*               replace ((⟪ open a ⟫ · [(a, b)] ∙ e1) · ⟪ close a ⟫) *)
  (*                 with ([(a,b)]∙((⟪ open b ⟫ · e1) · ⟪ close b ⟫)). *)
  (*               ** symmetry;apply ax_eq_ax,(@αKA_αα a b). *)
  (*                  intros u (U&x&->&(y&w&->&->&I)&->). *)
  (*                  unfold fresh__α;simpl_binding;unfold_eqX. *)
  (*                  eapply δ_binFin in B. *)
  (*                  apply (spines_homogeneous B) in I__E as (I__E&_). *)
  (*                  apply homogeneous_is_binding_finite in I__E. *)
  (*                  split. *)
  (*                  --- apply (is_binding_finite_bindings I__E a) in I. *)
  (*                      apply F1 in I as [<-|F];[|exfalso;apply F]. *)
  (*                      reflexivity. *)
  (*                  --- apply (is_binding_finite_bindings I__E b) in I. *)
  (*                      apply B1 in I as [<-|[<-|F]];[| |exfalso;apply F];reflexivity. *)
  (*               ** repeat rewrite act_prod. *)
  (*                  unfold act at 1 3;simpl. *)
  (*                  unfold act at 1 3;simpl. *)
  (*                  unfold act at 1 3;simpl. *)
  (*                  unfold_eqX;reflexivity. *)
  (*            ++ apply KA_αKA_inf. *)
  (*               etransitivity;[|apply ax_eq_inf,ax_eq_prod; *)
  (*                               [reflexivity|symmetry;apply spines_eq]]. *)
  (*               apply proper_prod_inf;[reflexivity|]. *)
  (*               transitivity (e1·e2). *)
  (*               ** apply proper_prod_inf;[reflexivity|]. *)
  (*                  apply δ_inf_e. *)
  (*               ** apply Σ_bigger,in_map_iff. *)
  (*                  exists (e1,e2);simpl;split;tauto. *)
  (*         -- intros F0;rewrite F0 in If. *)
  (*            apply in_flat_map in If as ((f1&f2)&I__F&If). *)
  (*            simpl_In in I__F;rewrite freshExprB_freshExpr in I__F;destruct I__F as (I__F&Fa);simpl in *. *)
  (*            apply in_flat_map in If as (f'&If'&If). *)
  (*            apply in_map_iff in If as ((g1&g2)&<-&I__G). *)
  (*            simpl_In in I__G;rewrite balExprB_balExpr in I__G;destruct I__G as (I__G&Ba);simpl in *. *)
  (*            transitivity  (⟪ open b ⟫ · (f1·(⟪open a⟫ *)
  (*                                               ·(f' *)
  (*                                                   ·(⟪close b⟫ *)
  (*                                                       ·(g1 *)
  (*                                                           ·(⟪close a⟫·δ(close a) g2))))))). *)
  (*            ++ apply ax_eq_inf. *)
  (*               repeat rewrite (KA_αKA (ax_eq_ax _ (KA_prod_assoc _ _ _))). *)
  (*               apply ax_eq_prod;[|reflexivity]. *)
  (*               repeat rewrite <- (KA_αKA (ax_eq_ax _ (KA_prod_assoc _ _ _))). *)
  (*               assert ( a <> c /\ b <> c) as (N1&N2). *)
  (*               ** split;intros <-. *)
  (*                  --- exfalso. *)
  (*                      unfold freshExprB in F0;rewrite <-not_true_iff_false,inclb_correct in F0. *)
  (*                      apply F0;cut (a # e1). *)
  (*                      +++ intros F';apply bindings_fresh in F' as [-> | ->]; *)
  (*                            [apply incl_nil|reflexivity]. *)
  (*                      +++ revert Fc I__E;clear. *)
  (*                          intros I1 Is I2;apply I1;clear I1. *)
  (*                          eapply δ_support. *)
  (*                          eapply (spines_support Is). *)
  (*                          simpl_In;tauto. *)
  (*                  --- exfalso. *)
  (*                      revert Fc Ib;clear. *)
  (*                      unfold OpenVar;intros. *)
  (*                      apply in_flat_map in Ib as (l&Il&Ia). *)
  (*                      destruct l as [a|a|x];try (exfalso;apply Ia). *)
  (*                      destruct Ia as [<-|Ia];[|exfalso;apply Ia]. *)
  (*                      induction e;simpl in *;try tauto. *)
  (*                      +++ simpl_In in *;destruct Il as [Il|Il]. *)
  (*                          *** apply IHe1,Il. *)
  (*                               unfold support in *;simpl in *;simpl_In in Fc;tauto. *)
  (*                          *** apply IHe2,Il. *)
  (*                               unfold support in *;simpl in *;simpl_In in Fc;tauto. *)
  (*                      +++ simpl_In in *;destruct Il as [Il|Il]. *)
  (*                          *** apply IHe1,Il. *)
  (*                               unfold support in *;simpl in *;simpl_In in Fc;tauto. *)
  (*                          *** apply IHe2,Il. *)
  (*                              unfold support in *;simpl in *;simpl_In in Fc;tauto. *)
  (*                      +++ destruct Il as [->|F];[|tauto]. *)
  (*                          apply Fc;simpl;tauto. *)
  (*               ** transitivity (⟪ open b ⟫ · f1 · *)
  (*                                           [(a,c)]∙(⟪ open a ⟫ · f' *)
  (*                                                               · ⟪ close b ⟫ · g1 · ⟪ close a ⟫)). *)
  (*                  --- transitivity ([(a,b)]∙ *)
  (*                                       (⟪ open b ⟫ · f1 · *)
  (*                                                   [(a,c)]∙(⟪ open a ⟫ *)
  (*                                                              · f' *)
  (*                                                              · ⟪ close b ⟫)) *)
  (*                                       · [(a,c)]∙ (g1 · ⟪ close a ⟫)). *)
  (*                      +++ repeat rewrite act_prod;simpl. *)
  (*                          repeat rewrite action_compose;simpl. *)
  (*                          unfold act at 4 6 8 10;simpl. *)
  (*                          unfold act at 4 6 8 10;simpl. *)
  (*                          unfold act at 4 6 8 10;simpl. *)
  (*                          simpl_eqX. *)
  (*                          repeat rewrite <- (KA_αKA (ax_eq_ax _ (KA_prod_assoc _ _ _))). *)
  (*                          repeat (apply ax_eq_prod;[reflexivity|]). *)
  (*                          reflexivity. *)
  (*                      +++ etransitivity;[apply ax_eq_prod; *)
  (*                                         [symmetry;apply ax_eq_ax,αKA_αα|reflexivity]|]. *)
  (*                          *** intros u (u1&u2&->&(x&w1&->&->&I1)&I2). *)
  (*                              apply act_lang in I2. *)
  (*                              destruct I2 as (v&y&E&(z&w2&->&->&I2)&->). *)
  (*                              apply (act_bij [(a,c)]) in E;rewrite act_p_pinv in E;subst. *)
  (*                              unfold fresh__α;simpl_binding. *)
  (*                              split. *)
  (*                              ---- transitivity *)
  (*                                     (ε ⋅ (𝗙 a w1 ⋅ 𝗙 (([(a, c)] ∗) ∙ a) *)
  (*                                             (open a :: w2 ++ [close b]))); *)
  (*                                     [f_equal;f_equal;apply 𝗙_perm|]. *)
  (*                                   simpl_binding;simpl. *)
  (*                                   unfold act;simpl;simpl_eqX;unfold_eqX. *)
  (*                                   cut (c # w2). *)
  (*                                   ++++ intro F;apply αfresh_support in F as ->;simpl. *)
  (*                                        eapply is_binding_finite_bindings in I1. *)
  (*                                        **** apply Fa in I1 as [<-|F];[|exfalso;apply F]. *)
  (*                                             reflexivity. *)
  (*                                        **** apply homogeneous_is_binding_finite. *)
  (*                                             apply spines_homogeneous in I__F;[tauto|]. *)
  (*                                             apply homogeneous_is_binding_finite. *)
  (*                                             apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                             apply δ_binFin;assumption. *)
  (*                                   ++++ intro Ic;apply Fc. *)
  (*                                        eapply δ_support. *)
  (*                                        rewrite <- (spines_support I__E). *)
  (*                                        simpl_In;left. *)
  (*                                        rewrite <- (spines_support I__F). *)
  (*                                        simpl_In;right. *)
  (*                                        eapply δ_support. *)
  (*                                        rewrite <- (𝐇_support If'). *)
  (*                                        apply (support_lang I2),Ic. *)
  (*                              ---- transitivity *)
  (*                                     ((0, false, 1)  ⋅ (𝗙 b w1 ⋅ 𝗙 (([(a, c)] ∗) ∙ b) *)
  (*                                             (open a :: w2 ++ [close b]))); *)
  (*                                     [f_equal;f_equal;apply 𝗙_perm|]. *)
  (*                                   simpl_binding;simpl. *)
  (*                                   unfold act;simpl;simpl_eqX;unfold_eqX. *)
  (*                                   cut (𝗙 b (w1 ++ open a ::w2) ∈ [ε;(0, true, 0)]). *)
  (*                                   ++++ intro E. *)
  (*                                        transitivity ((0,false,1)⋅𝗙 b (w1++open a::w2)⋅(1,false,0)); *)
  (*                                          [|destruct E as [<-|[<-|F]];(exfalso;apply F)||reflexivity]. *)
  (*                                        simpl_binding. *)
  (*                                        repeat rewrite prod_assoc;reflexivity. *)
  (*                                   ++++ apply B1. *)
  (*                                        eapply is_binding_finite_bindings. *)
  (*                                        **** apply homogeneous_is_binding_finite. *)
  (*                                             apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                             apply δ_binFin,B. *)
  (*                                        **** apply (soundness (spines_eq e1)). *)
  (*                                             apply Σ_lang. *)
  (*                                             exists (f1·f2);split; *)
  (*                                               [apply in_map_iff;exists (f1,f2);tauto|]. *)
  (*                                             exists w1,(open a::w2);repeat split;auto. *)
  (*                                             apply δ_lang. *)
  (*                                             apply (soundness (𝐇_eq _)),Σ_lang. *)
  (*                                             exists f';tauto. *)
  (*                          *** repeat rewrite act_prod. *)
  (*                              repeat rewrite <- (KA_αKA (ax_eq_ax _ (KA_prod_assoc _ _ _))). *)
  (*                              reflexivity. *)
  (*                  --- repeat rewrite act_prod. *)
  (*                      repeat rewrite <- (KA_αKA (ax_eq_ax _ (KA_prod_assoc _ _ _))). *)
  (*                      repeat (apply ax_eq_prod;[reflexivity|]). *)
  (*                      repeat rewrite <- act_prod. *)
  (*                      symmetry;apply ax_eq_ax,αKA_αα. *)
  (*                      intros u (x&?&->&->&u1&?&->&I1&y&?&->&->&u2&?&->&I2&->). *)
  (*                      split. *)
  (*                      +++ unfold fresh__α;simpl_binding. *)
  (*                          cut (𝗙 a (u1++u2) ∈ [ε;(0,true,0)]). *)
  (*                          *** intro E. *)
  (*                              transitivity ((0,false,1)⋅𝗙 a (u1++u2)⋅(1,false,0)); *)
  (*                                [|destruct E as [<-|[<-|F]];(exfalso;apply F)||reflexivity]. *)
  (*                              simpl_binding;rewrite prod_unit_l. *)
  (*                              repeat rewrite prod_assoc;reflexivity. *)
  (*                          *** apply Ba. *)
  (*                              apply is_binding_finite_bindings. *)
  (*                              ---- apply binding_finite_spec;simpl. *)
  (*                                   apply orb_true_iff;right. *)
  (*                                   apply andb_true_iff;split;apply binding_finite_spec. *)
  (*                                   ++++ apply homogeneous_is_binding_finite. *)
  (*                                        eapply homogeneous_𝐇,If'. *)
  (*                                        apply δ_binFin. *)
  (*                                        apply homogeneous_is_binding_finite. *)
  (*                                        apply spines_homogeneous in I__F;[tauto|]. *)
  (*                                        apply homogeneous_is_binding_finite. *)
  (*                                        apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                        apply δ_binFin,B. *)
  (*                                   ++++ apply homogeneous_is_binding_finite. *)
  (*                                        apply spines_homogeneous in I__G;[tauto|]. *)
  (*                                        apply δ_binFin. *)
  (*                                        apply homogeneous_is_binding_finite. *)
  (*                                        apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                        apply δ_binFin,B. *)
  (*                              ---- exists u1,u2;tauto. *)
  (*                      +++ apply αfresh_support. *)
  (*                          intro Ic. *)
  (*                          repeat (setoid_rewrite support_list_cons in Ic) *)
  (*                          ||(setoid_rewrite support_list_app in Ic). *)
  (*                          simpl_In in Ic;simpl in Ic. *)
  (*                          destruct Ic as [[->|F]|[F|[[->|F]|[F|F]]]];try tauto. *)
  (*                          *** eapply Fc,δ_support,(spines_support I__E). *)
  (*                              rewrite <- (spines_support I__F). *)
  (*                              rewrite <- (@δ_support f2 (open a)). *)
  (*                              rewrite <- (𝐇_support If'). *)
  (*                              apply (support_lang I1) in F;simpl_In;tauto. *)
  (*                          *** eapply Fc,δ_support,(spines_support I__E). *)
  (*                              rewrite <- (@δ_support e2 (close b)). *)
  (*                              rewrite <- (spines_support I__G). *)
  (*                              apply (support_lang I2) in F;simpl_In;tauto. *)
  (*            ++ apply KA_αKA_inf. *)
  (*               rewrite <- (δ_inf_e (open b) e). *)
  (*               apply proper_prod_inf;[reflexivity|]. *)
  (*               transitivity (e1·e2). *)
  (*               ** transitivity (f1 · (⟪ open a ⟫ · (f' · (⟪close b⟫ · (δ (close b) e2))))). *)
  (*                  --- apply proper_prod_inf;[reflexivity|]. *)
  (*                      apply proper_prod_inf;[reflexivity|]. *)
  (*                      apply proper_prod_inf;[reflexivity|]. *)
  (*                      apply proper_prod_inf;[reflexivity|]. *)
  (*                      transitivity (g1·g2). *)
  (*                      +++ apply proper_prod_inf;[reflexivity|]. *)
  (*                          apply δ_inf_e. *)
  (*                      +++  etransitivity;[|apply ax_eq_inf;symmetry;apply spines_eq]. *)
  (*                           apply Σ_bigger,in_map_iff. *)
  (*                           exists (g1,g2);simpl;split;tauto. *)
  (*                  --- rewrite δ_inf_e. *)
  (*                      repeat rewrite (ax_eq_inf (ax_eq_ax _ (KA_prod_assoc _ _ e2))). *)
  (*                      apply proper_prod_inf;[|reflexivity]. *)
  (*                      etransitivity;[|apply ax_eq_inf;symmetry;apply spines_eq]. *)
  (*                      transitivity (f1·f2). *)
  (*                      +++ rewrite <- (δ_inf_e (open a) f2),(𝐇_eq (δ (open a) f2)). *)
  (*                          apply proper_prod_inf;[reflexivity|]. *)
  (*                          apply proper_prod_inf;[reflexivity|]. *)
  (*                          apply Σ_bigger;assumption. *)
  (*                      +++ apply Σ_bigger,in_map_iff. *)
  (*                          exists (f1,f2);simpl;split;tauto.      *)
  (*               ** etransitivity;[|apply ax_eq_inf;symmetry;apply spines_eq]. *)
  (*                  apply Σ_bigger,in_map_iff. *)
  (*                  exists (e1,e2);simpl;split;tauto. *)
  (*     + apply inf_cup_left. *)
  (*     + intros w;simpl. *)
  (*       rewrite (cl_α_join _ _ w). *)
  (*       intros (u&Iu&Eu). *)
  (*       destruct u as [|l u]. *)
  (*       -- exfalso;apply αequiv_length in Eu;simpl in Eu;discriminate. *)
  (*       -- pose proof Eu as E;apply aeq_first_letter in Eu as [(->&Eu)|F]. *)
  (*          ++ left;exists u;split;[|assumption]. *)
  (*             apply δ_lang,Iu. *)
  (*          ++ right;destruct F as (b&x&N&->&Ex). *)
  (*             symmetry in Ex;inversion Ex;subst. *)
  (*             pose proof E as Eu. *)
  (*             apply (aeq_first_letter_open N) in E as (u1&u2&->&B1&hβ). *)
  (*             apply cl_α_Σ. *)
  (*             pose proof Iu as Iw. *)
  (*             apply δ_lang in Iu. *)
  (*             apply spines_split in Iu as (e1&e2&I__E&I1&I2). *)
  (*             destruct hβ as [(Fa&Ew)|(u1'&u2'&w1'&w2'&->&->&Fa&Ba&Ew)]. *)
  (*             ** unfold L;clear L;eexists;split. *)
  (*                --- apply in_flat_map;exists b;split. *)
  (*                    +++ simpl_In. *)
  (*                        split;[eapply In_OpenVar,Iw;now left|]. *)
  (*                        simpl_eqX;reflexivity. *)
  (*                    +++ apply in_flat_map. *)
  (*                        exists (e1,e2);split. *)
  (*                        *** simpl_In;split;[assumption|]. *)
  (*                            apply balExprB_balExpr;simpl. *)
  (*                            intros β Iβ. *)
  (*                            cut (β = 𝗙 b u1). *)
  (*                            ---- intros ->;revert B1;clear. *)
  (*                                 apply balanced_alt. *)
  (*                            ---- symmetry. *)
  (*                                 apply bindings_witness in Iβ as (?&I&<-). *)
  (*                                 cut (homogeneous e1);[rewrite homogeneous_alt; *)
  (*                                                       intro H;apply H;tauto|]. *)
  (*                                 apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                 apply δ_binFin,B. *)
  (*                        *** simpl;replace (freshExprB a e1) with true;[now left|]. *)
  (*                            symmetry;apply freshExprB_freshExpr. *)
  (*                            intros β Iβ. *)
  (*                            cut (β = 𝗙 a u1). *)
  (*                            ---- rewrite Fa;intros ->;now left. *)
  (*                            ---- symmetry. *)
  (*                                 apply bindings_witness in Iβ as (?&I&<-). *)
  (*                                 cut (homogeneous e1);[rewrite homogeneous_alt; *)
  (*                                                       intro H;apply H;tauto|]. *)
  (*                                 apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                 apply δ_binFin,B. *)
  (*                --- eexists;split. *)
  (*                    +++ rewrite <- (soundness (ax_eq_ax KA' (KA_prod_assoc _ _ _)) _). *)
  (*                        exists ([(a,b)]∙u1);eexists;split;[reflexivity|split]. *)
  (*                        *** apply act_lang;rewrite act_pinv_p;assumption. *)
  (*                        *** exists [close a],u2;split;[reflexivity|split]. *)
  (*                            ---- reflexivity. *)
  (*                            ---- apply δ_lang,I2. *)
  (*                    +++ rewrite perm_comm_pair;assumption. *)
  (*             ** apply spines_split in I1 as (f1&f2&I__F&I11&I12). *)
  (*                apply δ_lang in I12. *)
  (*                apply δ_lang in I2. *)
  (*                apply spines_split in I2 as (g1&g2&I__G&I21&I22). *)
  (*                apply 𝐇_lang,Σ_lang in I12 as (f'&If'&I12). *)
  (*                apply δ_lang in I22. *)
  (*                eexists;split. *)
  (*                --- unfold L;clear L. *)
  (*                    apply in_flat_map;exists b;split. *)
  (*                    +++ simpl_In;split. *)
  (*                        *** eapply In_OpenVar;eauto;simpl;tauto. *)
  (*                        *** simpl_eqX;reflexivity. *)
  (*                    +++ apply in_flat_map;exists (e1,e2);split. *)
  (*                        *** simpl_In;split;[assumption|]. *)
  (*                            simpl. *)
  (*                            apply balExprB_balExpr;intros β I. *)
  (*                            apply bindings_witness in I as (u'&Iu'&<-). *)
  (*                            apply balanced_alt. *)
  (*                            eapply homogeneous_alt with (a0:=b)(u:=u1'++open a::u2') in Iu'. *)
  (*                            ---- unfold balanced;rewrite <- Iu';apply B1. *)
  (*                            ---- apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                 apply δ_binFin,B. *)
  (*                            ---- rewrite (soundness (spines_eq _) _). *)
  (*                                 apply Σ_lang;exists (f1·f2);split. *)
  (*                                 ++++ apply in_map_iff;exists (f1,f2);tauto. *)
  (*                                 ++++ eexists;eexists;split;[reflexivity|]. *)
  (*                                      split;[assumption|]. *)
  (*                                      apply δ_lang. *)
  (*                                      apply (soundness (𝐇_eq _)),Σ_lang. *)
  (*                                      exists f';tauto. *)
  (*                        *** simpl;replace (freshExprB a e1) with false. *)
  (*                            ---- apply in_flat_map;exists (f1,f2);split. *)
  (*                                 ++++ simpl_In;split;[assumption|]. *)
  (*                                      simpl. *)
  (*                                      apply freshExprB_freshExpr;unfold freshExpr. *)
  (*                                      intros β Iβ;left;symmetry. *)
  (*                                      apply bindings_witness in Iβ as (u'&Iu'&<-). *)
  (*                                      rewrite <- Fa;eapply homogeneous_alt;eauto. *)
  (*                                      apply spines_homogeneous in I__F;[tauto|]. *)
  (*                                      apply homogeneous_is_binding_finite. *)
  (*                                      apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                      apply δ_binFin,B. *)
  (*                                 ++++ apply in_flat_map;exists f';split;[assumption|]. *)
  (*                                      apply in_map_iff;exists (g1,g2);split;[reflexivity|]. *)
  (*                                      simpl_In;split;[assumption|]. *)
  (*                                      simpl. *)
  (*                                      apply balExprB_balExpr;intros β I. *)
  (*                                      apply bindings_witness in I as (u'&Iu'&<-). *)
  (*                                      apply balanced_alt. *)
  (*                                      eapply homogeneous_alt with (a0:=a)(u:=u2'++w1') in Iu'. *)
  (*                                      **** unfold balanced;rewrite <- Iu';apply Ba. *)
  (*                                      **** apply homogeneous_prod. *)
  (*                                           ----- eapply homogeneous_𝐇,If'. *)
  (*                                           apply δ_binFin,homogeneous_is_binding_finite. *)
  (*                                           apply spines_homogeneous in I__F;[tauto|]. *)
  (*                                           apply homogeneous_is_binding_finite. *)
  (*                                           apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                           apply δ_binFin,B. *)
  (*                                           ----- apply spines_homogeneous in I__G;[tauto|]. *)
  (*                                           apply δ_binFin. *)
  (*                                           apply homogeneous_is_binding_finite. *)
  (*                                           apply spines_homogeneous in I__E;[tauto|]. *)
  (*                                           apply δ_binFin,B. *)
  (*                                      **** exists u2',w1';split;[reflexivity|tauto]. *)
  (*                            ---- symmetry;apply not_true_iff_false;intro F. *)
  (*                                 cut (a #α (u1'++open a::u2')). *)
  (*                                 ++++ unfold fresh__α;simpl_binding. *)
  (*                                      rewrite Fa,prod_unit_l. *)
  (*                                      destruct Ba as (Ca&Da). *)
  (*                                      apply close_balanced_prefix in Da. *)
  (*                                      revert Da;unfold close_balanced;clear. *)
  (*                                      destruct (𝗙 a u2') as ((?&?)&?). *)
  (*                                      simpl_binding;intros ->. *)
  (*                                      unfold prod_binding;simpl;intro E;inversion E;lia. *)
  (*                                 ++++ eapply freshExpr_bindFin. *)
  (*                                      **** apply homogeneous_is_binding_finite. *)
  (*                                           apply spines_homogeneous in I__E as (h&_);[apply h|]. *)
  (*                                           apply δ_binFin,B. *)
  (*                                      **** apply freshExprB_freshExpr,F. *)
  (*                                      **** apply (soundness (spines_eq _)),Σ_lang. *)
  (*                                           exists (f1·f2);split;[apply in_map_iff;exists (f1,f2);tauto|]. *)
  (*                                           eexists;eexists;split;[reflexivity|]. *)
  (*                                           split;[tauto|]. *)
  (*                                           apply δ_lang. *)
  (*                                           apply (soundness (𝐇_eq _)),Σ_lang. *)
  (*                                           exists f';tauto. *)
  (*                --- eexists;split. *)
  (*                    +++ simpl;eexists;eexists;split;[reflexivity|]. *)
  (*                        split;[|eassumption]. *)
  (*                        eexists;eexists;split;[reflexivity|]. *)
  (*                        split;[|reflexivity]. *)
  (*                        eexists;eexists;split;[reflexivity|]. *)
  (*                        split;[|apply act_lang;rewrite act_pinv_p;eassumption]. *)
  (*                        eexists;eexists;split;[reflexivity|]. *)
  (*                        split;[|reflexivity]. *)
  (*                        eexists;eexists;split;[reflexivity|]. *)
  (*                        split;[|apply act_lang;rewrite act_pinv_p;eassumption]. *)
  (*                        eexists;eexists;split;[reflexivity|]. *)
  (*                        split;[|reflexivity]. *)
  (*                        apply act_lang;rewrite act_pinv_p;eassumption. *)
  (*                    +++ replace (cons (a,b)) with (app [(a,b)]) by reflexivity. *)
  (*                        repeat rewrite app_nil_r. *)
  (*                        rewrite <-action_compose. *)
  (*                        repeat rewrite (perm_comm_pair a b). *)
  (*                        rewrite action_compose;simpl. *)
  (*                        repeat rewrite app_ass;simpl. *)
  (*                        apply Ew. *)
  (*                        cut (c # (open b::u1'++open a::u2'++close b::w1'++close a::w2')). *)
  (*                        *** repeat rewrite support_list_app *)
  (*                            ||rewrite support_list_cons;simpl_In;tauto. *)
  (*                        *** intro I;eapply Fc,support_lang,I. *)
  (*                            apply δ_lang,(soundness(spines_eq _)),Σ_lang. *)
  (*                            exists (e1·e2);split;[apply in_map_iff;exists (e1,e2);tauto|]. *)
  (*                            exists (u1'++open a::u2');eexists. *)
  (*                            split;[repeat rewrite app_ass;reflexivity|]. *)
  (*                            split. *)
  (*                            ---- apply (soundness(spines_eq _)),Σ_lang. *)
  (*                                 exists (f1·f2);split;[apply in_map_iff;exists (f1,f2);tauto|]. *)
  (*                                 eexists;eexists;split;[reflexivity|]. *)
  (*                                 split;[assumption|]. *)
  (*                                 apply δ_lang,(soundness(𝐇_eq _)),Σ_lang. *)
  (*                                 exists f';tauto. *)
  (*                            ---- apply δ_lang,(soundness(spines_eq _)),Σ_lang. *)
  (*                                 exists (g1·g2);split;[apply in_map_iff;exists (g1,g2);tauto|]. *)
  (*                                 exists w1';eexists;split;[reflexivity|]. *)
  (*                                 split;[assumption|]. *)
  (*                                 apply δ_lang;assumption. *)
  (*   - split;[|split]. *)
  (*     + apply KA_αKA_inf. *)
  (*       rewrite (@fundamental_theorem _ _ e (close a::Var e)) at 2 by (apply incl_tl;reflexivity). *)
  (*       etransitivity;[|apply inf_cup_right]. *)
  (*       simpl;apply inf_cup_left. *)
  (*     + reflexivity. *)
  (*     + intros w;intros (u&Iu&Eu). *)
  (*       destruct u as [|l u]. *)
  (*       -- exfalso;apply αequiv_length in Eu;simpl in Eu;discriminate. *)
  (*       -- apply aeq_first_letter in Eu as [(->&Eu)|F]. *)
  (*          ++ exists u;split;[|assumption]. *)
  (*             apply δ_lang,Iu. *)
  (*          ++ exfalso;destruct F as (_&b&_&_&F). *)
  (*             discriminate. *)
  (*   - split;[|split]. *)
  (*     + apply KA_αKA_inf. *)
  (*       rewrite (@fundamental_theorem _ _ e (var x::Var e)) at 2 by (apply incl_tl;reflexivity). *)
  (*       etransitivity;[|apply inf_cup_right]. *)
  (*       simpl;apply inf_cup_left. *)
  (*     + reflexivity. *)
  (*     + intros w;intros (u&Iu&Eu). *)
  (*       destruct u as [|l u]. *)
  (*       -- exfalso;apply αequiv_length in Eu;simpl in Eu;discriminate. *)
  (*       -- apply aeq_first_letter in Eu as [(->&Eu)|F]. *)
  (*          ++ exists u;split;[|assumption]. *)
  (*             apply δ_lang,Iu. *)
  (*          ++ exfalso;destruct F as (_&b&_&_&F). *)
  (*             discriminate. *)
  (* Qed. *)

  (* Proposition fundamental_theorem_α e c A: *)
  (*   c # e -> *)
  (*   is_binding_finite e ->  *)
  (*   Var e ⊆ A -> {|αKA,KA'|} ⊢ e == ϵ e ∪ Σ_{A} (fun a => ⟪a⟫ · (δα c a e)). *)
  (* Proof. *)
  (*   intros Fc B. *)
  (*   assert ((forall l, ({|αKA,KA'|} ⊢ ⟪l⟫·δα c l e =<= e)) *)
  (*           /\ (forall l, δ l e <=KA δα c l e) *)
  (*           /\  (forall l, (forall w, cl_α ⟦e⟧ (l::w) <-> cl_α ⟦δα c l e⟧ w))) *)
  (*     as (hyp1&hyp2&hyp3). *)
  (*   - split;[|split];intro l;pose proof (δα_spec l Fc B) as (h1&h2&h3);tauto. *)
  (*   - intros I;apply ax_inf_PartialOrder;split;[|unfold Basics.flip]. *)
  (*     + apply KA_αKA_inf. *)
  (*       rewrite (fundamental_theorem I) at 1. *)
  (*       apply proper_join_inf;[reflexivity|]. *)
  (*       clear I;induction A;[reflexivity|]. *)
  (*       simpl;apply proper_join_inf;[|apply IHA]. *)
  (*       rewrite hyp2;reflexivity. *)
  (*     + apply inf_join_inf. *)
  (*       * apply KA_αKA_inf. *)
  (*         rewrite (fundamental_theorem I) at 2. *)
  (*         apply inf_cup_left. *)
  (*       * clear I;induction A;simpl. *)
  (*         -- apply KA_αKA_inf;simpl;unfold ax_inf. *)
  (*            apply ax_eq_ax,KA_zero. *)
  (*         -- replace e_prod with prod by reflexivity. *)
  (*            rewrite (hyp1 a),IHA;auto. *)
  (*            apply ax_eq_inf;auto. *)
  (* Qed. *)

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

