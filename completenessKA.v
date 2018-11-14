(** * RIS.completenessKA : Link with relation-algebra to import the completeness proof of Kleene algebra. *)
Require Import tools algebra language regexp.
Require Import RelationAlgebra.syntax RelationAlgebra.kleene RelationAlgebra.boolean RelationAlgebra.lang RelationAlgebra.lset RelationAlgebra.sums RelationAlgebra.normalisation.
Require Import RelationAlgebra.regex RelationAlgebra.ka_completeness RelationAlgebra.kat_tac.

Set Implicit Arguments.
Set Strict Implicit.
Set Printing Implicit Defensive.

Section proof.
  
  Global Instance dec_sigma : decidable_set sigma :=
    Build_decidable_set (fun x y => Bool.iff_reflect _ _ (iff_Symmetric _ _ (BinPos.Pos.eqb_eq x y))).

  Notation E := (@regexp regex.sigma).
  
  Fixpoint regexp_to_regex' (e : E) : regex :=
    match e with
    | e_un => r_one
    | e_zero => r_zer
    | e_add e f => r_pls (regexp_to_regex' e) (regexp_to_regex' f)
    | e_prod e f => r_dot (regexp_to_regex' e) (regexp_to_regex' f)
    | e_star e => r_str (regexp_to_regex' e)
    | ⟪a⟫ => r_var a
    end.

  Fixpoint regexp_to_expr (e : E) : expr_(BKA) (fun _ => xH) (fun _ => xH) xH xH :=
    match e with
    | e_un => (syntax.e_one BinNums.xH)
    | e_zero => (syntax.e_zer BinNums.xH BinNums.xH)
    | e_add e f => syntax.e_pls (regexp_to_expr e) (regexp_to_expr f)
    | e_prod e f => syntax.e_dot (regexp_to_expr e) (regexp_to_expr f)
    | e_star e => syntax.e_str (regexp_to_expr e)
    | ⟪a⟫ => syntax.e_var a
    end.
  Fixpoint regex'_to_regexp (e : regex) : E :=
    match e with
    | r_one => e_un
    | r_zer => e_zero
    | r_pls e f => e_add (regex'_to_regexp e) (regex'_to_regexp f)
    | r_dot e f => e_prod (regex'_to_regexp e) (regex'_to_regexp f)
    | r_str e => e_star (regex'_to_regexp e)
    | r_var a => ⟪a⟫
    end.

  Lemma regex'_to_regexp_id e : regex'_to_regexp (regexp_to_regex' e) = e.
  Proof. induction e;simpl;congruence. Qed.

  Lemma regexp_to_regex'_id e : regexp_to_regex' (regex'_to_regexp e) = e.
  Proof. induction e;simpl;congruence. Qed.

  Lemma to_expr_id e : to_expr e = regexp_to_expr (regex'_to_regexp e).
  Proof. induction e;simpl;congruence. Qed.
  
  Lemma equiv_id (l m : lang' sigma) : l ≃ m <-> l == m.
  Proof.
    unfold sequiv,eq_lang.
    unfold lattice.weq;simpl;tauto.
  Qed.
  
  Lemma regex'_to_regexp_lang e : ⟦regex'_to_regexp e⟧ ≃ lang e.
  Proof.
    induction e;simpl.
    - rewrite equiv_id,lang_0;reflexivity.
    - rewrite equiv_id,lang_1.
      intro u;split;[intros ->|intros <-];reflexivity.
    - rewrite IHe1,IHe2,equiv_id,lang_pls.
      unfold lattice.cup;simpl.
      reflexivity.
    - rewrite IHe1,IHe2,equiv_id,lang_dot;clear IHe1 IHe2.
      unfold monoid.dot;simpl.
      unfold lang.lang_dot;simpl.
      intros u;split.
      + intros (v&w&->&Iv&Iw).
        exists v;[assumption|].
        exists w;[assumption|].
        reflexivity.
      + intros [v Iv [w Iw ->]].
        exists v,w;tauto.
    - rewrite IHe;clear IHe.
      intro u;split.
      + intros (n&In);revert u In;induction n.
        * intros ? ->;reflexivity.
        * intros u (u1&u2&->&I&Ih).
          apply IHn in Ih.
          unfold lang;simpl.
          destruct u1;simpl.
          -- apply Ih.
          -- apply lang_dot.
             exists u1;[apply I|exists u2;[apply Ih|reflexivity]].
      + induction u using len_induction.
        * intros _;exists O;reflexivity.
        * intros I;apply lang_dot in I as [u1 I1 [u2 I2 ->]].
          apply H in I2 as (n&I2);[|rewrite app_length;lia].
          exists (S n),(a::u1),u2;repeat split.
          -- apply I1.
          -- apply I2.
    - rewrite equiv_id,lang_var;simpl.
      intro u;split;[intros ->|intros <-];reflexivity.
  Qed.
  Lemma regexp_to_regex'_lang e : ⟦e⟧ ≃ lang (regexp_to_regex' e).
  Proof.
    rewrite <- regex'_to_regexp_lang,regex'_to_regexp_id;reflexivity.
  Qed.


  Canonical Structure regexp_lattice_ops : lattice.ops :=
    lattice.mk_ops E (ax_inf regexp.KA KA') (ax_eq regexp.KA KA')
                   join join star zero zero.

  CoInductive regexp_unit := regexp_tt.

  Definition lat_ops := (fun _ _ : regexp_unit => regexp_lattice_ops).
  Definition mon_prod := (fun _ _ _ : regexp_unit => fun e f : E => e · f).
  Definition mon_un := (fun _ : regexp_unit => un : E).
  Definition mon_star := (fun _ : regexp_unit => star : E -> E).
  Definition mon_itr := (fun _ : regexp_unit => fun e : E => e · e⋆).
  Definition mon_neg := (fun _ _ : regexp_unit => fun e : E => e).

  Hint Unfold lat_ops mon_prod mon_un mon_star mon_itr.
  
  Canonical Structure regexp_ops :=
    monoid.mk_ops regexp_unit
                  lat_ops
                  mon_prod
                  mon_un
                  mon_itr
                  mon_star
                  mon_neg
                  mon_prod
                  mon_prod.


  
  Lemma KA_regexp_to_expr e f :
    e =KA f -> regexp_to_expr e == regexp_to_expr f.
  Proof.
    intro E;induction E.
    - reflexivity.
    - symmetry;auto.
    - etransitivity;eassumption.
    - simpl;apply monoid.dot_weq;assumption.
    - simpl;apply lattice.cup_weq;assumption. 
    - simpl;apply monoid.str_weq;assumption.
    - destruct H;simpl;ka.
    - destruct H;simpl.
      + cut (regexp_to_expr e^* * regexp_to_expr f <== regexp_to_expr f).
        * intro h;apply leq_iff_cup,h.
        * apply str_ind_l,leq_iff_cup,IHE.
      + cut (regexp_to_expr e * regexp_to_expr f^* <== regexp_to_expr e).
        * intro h;apply leq_iff_cup,h.
        * apply str_ind_r,leq_iff_cup,IHE.
  Qed.
      
  Instance regexp_laws: monoid.laws level.BKA regexp_ops.
  Proof.
    split;intros;simpl;autounfold;auto;
      try (unfold level.lower;simpl;discriminate)||(repeat right;intros).
    - split;simpl;try (unfold level.lower;simpl;discriminate).
      + apply ax_inf_PreOrder.
      + apply ax_inf_PartialOrder.
      + intros;split.
        * intros <-;split;unfold ax_inf.
          -- rewrite (mon_assoc _ _),(ka_idem _);reflexivity.
          -- rewrite (semiring_comm _),<-(mon_assoc _ _),(ka_idem _);reflexivity.
        * intros (->&->);rewrite (ka_idem _);reflexivity.
      + intros;right;apply zero_minimal.
    - rewrite H,H0;reflexivity.
    - apply ax_eq_inf;auto.
    - apply ax_eq_inf;auto.
    - apply ax_eq_inf;auto.
    - apply ax_eq_inf;auto.
    - apply one_inf_star.
    - rewrite <- ka_star_unfold at 2.
      apply inf_cup_right.
    - apply star_left_ind,H0.
    - apply star_right_ind,H0.
  Qed.
      
  Definition inject : expr_(BKA) (fun _ => xH) (fun _ => xH) xH xH -> E :=
    @eval _ (fun _ => xH) (fun _ => xH) regexp_ops (fun _ => regexp_tt)
     (fun x => ⟪x⟫) _ _.
                                  
  Lemma inject_regexp_to_expr e : inject (regexp_to_expr e) = e.
  Proof.
    induction e;simpl;try reflexivity.
    - rewrite <- IHe1,<-IHe2 at 2;reflexivity.
    - rewrite <- IHe1,<-IHe2 at 2;reflexivity.
    - rewrite <- IHe at 2;reflexivity.
  Qed.

  Lemma CompletenessKA_sigma (e f : E) : ⟦e⟧ ≃ ⟦f⟧ -> e =KA f.
  Proof.
    intros Eq.
    repeat rewrite regexp_to_regex'_lang in Eq.
    rewrite equiv_id in Eq.
    apply ka_complete_weq in Eq.
    unfold weq in Eq;simpl in Eq.
    unfold r_weq in Eq.
    repeat rewrite to_expr_id,regex'_to_regexp_id in Eq.
    rewrite <- inject_regexp_to_expr,<- (inject_regexp_to_expr e).
    replace (ax_eq _ _) with (@weq regexp_lattice_ops) by reflexivity.
    unfold weq in Eq;simpl in Eq.
    unfold e_weq in Eq.
    unfold inject;apply (Eq regexp_ops regexp_laws (fun _ => regexp_tt) (fun x => ⟪x⟫)).
  Qed.

  Context {X : Set} {decX : decidable_set X}.
  
  Lemma to_nat : forall Σ : list X, exists f : X -> nat, exists g, forall x, x ∈ Σ -> Some x = g (f x).
  Proof.
    intros Σ;induction Σ as [|a l].
    - exists (fun x => O),(fun _ => None);simpl;tauto.
    - destruct IHl as (f&g&ih).
      case_in a l.
      + exists f,g;intros x [<-|I'];apply ih;tauto.
      + exists (fun x => if x =?= a then O else S (f x)).
        exists (fun n => match n with O => Some a | S n => g n end).
        intros x [<-|Ix];unfold_eqX;try discriminate||reflexivity.
        apply ih,Ix.
  Qed.

  Lemma to_sigma : forall Σ : list X, exists f : X -> sigma, exists g, forall x, x ∈ Σ -> Some x = g (f x).
  Proof.
    intro Σ;destruct (to_nat Σ) as (f&g&hg).
    exists (fun x => BinPos.Pos.of_succ_nat (f x)).
    exists (fun n => g (Nat.pred (BinPos.Pos.to_nat n))).
    intros x Ix.
    rewrite Pnat.SuccNat2Pos.pred_id.
    apply hg,Ix.
  Qed.

  
  Lemma no_var_no_fun : (forall e : @regexp X, Var e = [] -> e =KA 𝟭 \/ e =KA 𝟬).
  Proof.
    intro e;rewrite <- test1_spec,<-test0_spec.
    induction e;simpl;try tauto.
    - simpl;intro E.
      apply app_eq_nil in E as (E1&E2).
      apply IHe1 in E1 as [-> | ->];apply IHe2 in E2 as [-> | ->];simpl;
        repeat rewrite Bool.orb_true_r;tauto.
    - simpl;intro E.
      apply app_eq_nil in E as (E1&E2).
      apply IHe1 in E1 as [-> | ->];apply IHe2 in E2 as [-> | ->];simpl;
        repeat rewrite Bool.orb_true_r;tauto.
    - intros E;apply IHe in E as [-> | ->];try rewrite Bool.orb_true_r;tauto.
    - discriminate.
  Qed.
  
  Fixpoint map_expr {A B : Set} (σ : A -> B) (e : @regexp A) :=
    match e with
    | e_zero => 𝟬
    | e_un => 𝟭
    | ⟪a⟫ => ⟪σ a⟫
    | e_add e f => map_expr σ e ∪ map_expr σ f
    | e_prod e f => map_expr σ e · map_expr σ f
    | e_star e => map_expr σ e ⋆
    end.

  Lemma map_expr_ax_eq {A B : Set} (σ : A -> B) e f :
    e =KA f -> map_expr σ e =KA map_expr σ f.
  Proof.
    intro E;induction E;simpl;auto.
    - etransitivity;eassumption.
    - destruct H;simpl;auto.
    - destruct H;simpl;eauto.
  Qed.
  
  Lemma get_terms :
    forall e f : @regexp X, exists e' f' : E, (e' =KA f' -> e =KA f) /\ (⟦e⟧ ≃ ⟦f⟧ -> ⟦e'⟧ ≃ ⟦f'⟧).
  Proof.
    intros e f.
    remember (Var e++Var f) as Σ;
      assert (Var e ⊆ Σ /\ Var f ⊆ Σ) as (he&hf)
        by (rewrite HeqΣ;split;intro;simpl_In;tauto);clear HeqΣ.
    assert (hyp: ((e=KA 𝟭 \/ e=KA 𝟬) /\ (f=KA 𝟭 \/ f=KA 𝟬))
                 \/ exists ϕ (ψ : sigma -> X), forall x, x ∈ Σ -> x = ψ (ϕ x)).
    - case_eq Σ.
      + intros ->;left.
        split;apply no_var_no_fun.
        * destruct (Var e) as [|x ?];[reflexivity|exfalso;apply (he x);now left].
        * destruct (Var f) as [|x ?];[reflexivity|exfalso;apply (hf x);now left].
      + intros x0 _ <-;right.
        destruct (to_sigma Σ) as (ϕ&ψ&hyp).
        exists ϕ,(fun x => match ψ x with None => x0 | Some y => y end).
        intros x Ix;rewrite <- (hyp x Ix);reflexivity.
    - destruct hyp as [([Ee | Ee]&[Ef | Ef])|(ϕ&ψ&hyp)].
      + exists e_un,e_un;split.
        * intros _;rewrite Ee,Ef;reflexivity.
        * reflexivity.
      + exists e_un,e_zero;split.
        * intros FF.
          apply test0_KA in FF;discriminate.
        * apply soundness in Ee as ->.
          apply soundness in Ef as ->.
          intro FF;exfalso;apply (FF []);reflexivity.
      + exists e_zero,e_un;split.
        * intros FF.
          apply test0_KA in FF;discriminate.
        * apply soundness in Ee as ->.
          apply soundness in Ef as ->.
          intro FF;exfalso;apply (FF []);reflexivity.
      + exists e_zero,e_zero;split.
        * intros _;rewrite Ee,Ef;reflexivity.
        * reflexivity.
      + exists (map_expr ϕ e),(map_expr ϕ f);split.
        * assert (h1 : forall e, Var e ⊆ Σ -> map_expr ψ (map_expr ϕ e) = e).
          -- clear e he f hf;intro e;induction e;simpl;try reflexivity.
             ++ intro ih;apply incl_app_split in ih as (ih1&ih2).
                rewrite IHe1,IHe2 by assumption;reflexivity.
             ++ intro ih;apply incl_app_split in ih as (ih1&ih2).
                rewrite IHe1,IHe2 by assumption;reflexivity.
             ++ intro ih;rewrite IHe by assumption;reflexivity.
             ++ intro Ix;f_equal;symmetry;apply hyp,Ix;now left.
          -- rewrite <- (h1 _ he), <- (h1 _ hf) at 2;clear h1.
             apply map_expr_ax_eq.
        * assert (h2: forall e u, ⟦map_expr ϕ e⟧ u <-> exists v, ⟦e⟧ v /\ u = map ϕ v).
          -- clear hyp ψ e f he hf.
             induction e;intro u;simpl.
             ++ firstorder.
             ++ split.
                ** intros -> ;exists [] ;split;reflexivity.
                ** intros (?&->&->);reflexivity.
             ++ unfold join,joinLang.
                rewrite IHe1,IHe2.
                firstorder.
             ++ unfold prod,prodLang.
                setoid_rewrite IHe1;setoid_rewrite IHe2;clear IHe1 IHe2.
                split;[intros (u1&u2&->&(v1&I1&->)&(v2&I2&->))
                      |intros (v&(v1&v2&->&I1&I2)&->)].
                ** exists (v1++v2);split.
                   --- exists v1,v2;tauto.
                   --- rewrite map_app;reflexivity.
                ** exists (map ϕ v1),(map ϕ v2);rewrite map_app.
                   firstorder.
             ++ transitivity ((fun u => (exists v : list X, ⟦ e ⟧ v /\ u = map ϕ v))⋆ u);
                  [revert u;apply proper_starLang;intro u;apply IHe|clear IHe].
                split.
                ** intros (n&In);revert u In;induction n;simpl.
                   --- intros ? -> ;exists [];split;[exists O|];reflexivity.
                   --- intros u (u1&u2&->&(v1&I1&->)&I2).
                       apply IHn in I2 as (v2&(n'&I2)&->).
                       exists (v1++v2);rewrite map_app;split;[|reflexivity].
                       exists (S n'),v1,v2;tauto.
                ** intros (v&(n&Iv)&-> );revert v Iv;induction n.
                   --- intros ? -> ;exists O;reflexivity.
                   --- intros u (u1&u2&->&I1&I2).
                       apply IHn in I2 as (n'&I2).
                       exists (S n' ),(map ϕ u1) , (map ϕ u2) ;rewrite map_app;firstorder.
             ++ split;[intros ->;exists [x];split|intros (v&->&->)];reflexivity.
          -- intros h3 u.
             repeat rewrite h2.
             setoid_rewrite (h3 _);reflexivity.
  Qed.

  Theorem CompletenessKA (e f : @regexp X) : e =KA f <-> ⟦e⟧ ≃ ⟦f⟧.
  Proof.
    split;[apply soundness|].
    pose proof (get_terms e f) as (e'&f'&h1&h2).
    intros I;apply h1,CompletenessKA_sigma,h2,I.
  Qed.
End proof.
  
