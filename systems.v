(** * RIS.systems : affine systems of equations *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Recdef.
Require Import Bool.

Require Import tools algebra language regexp automata completenessKA.

(** * Solving affine systems *)
Section system.
  (** We fix a decidable set of variables. *)
  Context {Q : Set}{decQ: decidable_set Q }.

  (** We fix a set [X] equipped with the operations of Kleene
      algebra. We do not however assume any axioms. *)
  Context {X : Set}.
  Context {jX: Join X}{pX: Product X}{zX: Zero X}{uX:Un X}{sX:Star X}.

  (** An affine system with variables of type [Q] and values of type
  [X] is a finite set of inequations either of the shape [x<=q] or
  [x·q<=q']. *)
  Definition cst_leq : Set := X * Q.

  Definition var_leq : Set := X * Q * Q.

  Definition system : Set := list cst_leq * list var_leq.

  (** We may extract the set of variables appearing in a system. *)
  Definition vars_system : system -> list Q :=
    fun S => (map snd (fst S))++(flat_map (fun e => [snd(fst e);snd e]) (snd S)).

  (** We define the size of a system to be its number of variables. *)
  Definition sizeSys (S : system) := ⎢{{vars_system S}}⎥.

  (** A vector is a map from variables to values. *)
  Definition vector := Q -> X.

  (** If [V] is a vector, [S] a system and [q] a variable, we may
      compute an expression representing the constraints on [q]: we
      take the union [x1 ∪ ... ∪ xn ∪ x'1 · q1 ∪ x'k · qk], where the
      inequations in [S] with [q] on the right hand side are [xi<=q]
      and [x'i·qi<=q]. *)
  Definition ExprVar (V : vector) (S : system) (x : Q) :=
    (Σ (flat_map (fun L => if (snd L) =?= x then [fst L] else []) (fst S)))
      ∪ (Σ (flat_map (fun L => if (snd L) =?= x then [fst (fst L)·V (snd (fst L))] else []) (snd S))).

  (** A vector [E] is an exact solution of [S] with respect to some
      relation [=X] if for every variable in the system we have 
      [E(q) =X ExprVar E S q]. *)
  Definition exact_solution (eqX : relation X) (S : system) (E : Q -> X) : Prop :=
    (forall q, q ∈ vars_system S -> eqX (E q)  (ExprVar E S q)).

  (** It is a weak solution with respect to a relation [<=X] if for
      every contraint is satisfied, meaning that:
      - if [x<=q] then [x <=X E q]
      - if [x·q<=q'] then [x·(E q) <=X (E q')].
   *)
  Definition weak_solution (leqX : relation X) (S : system) (E : Q -> X) : Prop :=
    (forall e q, (e,q) ∈ (fst S) -> leqX e (E q))
    /\ (forall p e q, (e,p,q) ∈ (snd S) -> leqX (e · E p) (E q)).

  (** A vector is a lower bound (of the solutions) if it is is
      pointwise smaller than every weak solution. *)
  Definition lower_bound leqX S E : Prop :=
    (forall F, weak_solution leqX S F -> forall q, q ∈ vars_system S -> leqX (E q) (F q)).

  (** The least solution is a weak solution that is a lower bound. *)
  Definition least_solution leqX S E :=
    weak_solution leqX S E /\ lower_bound leqX S E.

  (** [cst S q] is the sum of constants [xi] such that [xi<=q] is in [S]. *)
  Definition cst (M : system) q := Σ (flat_map (fun C => if (snd C =?= q) then [fst C] else []) (fst M)).

  (** [loop S q] is the sum of constants [xi] such that [xi·q<=q] is in [S]. *)
  Definition loop (M : system) q := Σ (flat_map (fun C => if (snd C =?= q) && (snd(fst C)=?=q)
                                                       then [fst (fst C)] else []) (snd M)).

  (** [succ S q] is the list of pairs [(x,p)] such that [p<>q] and [x·p<=q] is in [S]. *)
  Definition succ (M : system) q := (flat_map (fun C => if (snd C =?= q) && negb (snd(fst C)=?=q)
                                                     then [(fst (fst C),snd (fst C))] else [])
                                              (snd M)).

  (** [elim_var M q] yields a system that is equivalent to [M] except
      that [q] does not appear in it. It is obtained by removing all
      the constraints involving [q], and adding
      - [x · (loop M q)⋆ ·(cst M q) <= p] for every [x·q<=p] in the system;
      - [x · (loop M q)⋆ · y · p' <= p] for every [x·q<=p] and every [y,p'] in [succ M q]. *)
  Definition elim_var (M : system) q : system :=
    (((fun C => negb (snd C =?= q)) :> fst M)
       ++ (flat_map (fun C => if (negb (snd C =?= q)) && (snd(fst C)=?=q)
                           then [(fst(fst C) · (loop M q) ⋆ · (cst M q),snd C)]
                           else [])
                    (snd M)),
     (flat_map (fun C => if (negb (snd C =?= q))
                      then
                        if (snd(fst C)=?=q)
                        then
                          map (fun C' => (fst(fst C) · (loop M q) ⋆ · fst C',snd C',snd C)) (succ M q)
                        else [C]
                      else [])
               (snd M))).

  (** We compute a vector [solution_sys n M] by iterating
      [elim_var]. [n] is a natural number used to ensure
      termination. To get the correct result, [n] should be greater
      than the size of the system. *)
  Fixpoint solution_sys n (M : system) : (Q -> X) :=
    match n with
    | 0 => (fun _ => zero)
    | S n =>
      match {{vars_system M}} with
      | [] => (fun _ => zero)
      | q::_ =>
        let E := solution_sys n (elim_var M q) in
        (fun p => if p =?= q
               then (loop M q) ⋆ · (cst M q ∪ Σ (map (fun C => (fst C · E (snd C))) (succ M q)))
               else E p)
      end
    end.

  Section solutions.
    (** We temporarily fix an equivalence relation [⩵] and a partial
        order [≦], and assume they provide a Kleene algebra
        structure to the set [X]. *)
    Context {eqX leqX : relation X}.
    Context {equivX : @Equivalence X eqX} {preX : @PreOrder X leqX}.
    Context {poX : @PartialOrder X eqX equivX leqX preX}.
    Context {kaX : @KleeneAlgebra X eqX leqX jX pX zX uX sX}.
    Infix " ≦ " := leqX (at level 80).
    Infix " ⩵ " := eqX (at level 80).
    (* begin hide *)
    Instance join_semilattice : Semilattice X eqX join.
    Proof. destruct kaX;eapply IdemSemiRing_Semilattice;eauto. Qed.

    Definition inf_cup_left := (@inf_cup_left X _ _ _ _ join_semilattice proper_join ka_joinOrder).
    Definition inf_cup_right :=
      (@inf_cup_right X _ _ _ _ _ _ join_semilattice proper_join ka_joinOrder).
    Definition inf_join_inf := (@inf_join_inf X eqX leqX _ _ _ _ join_semilattice proper_join _).
    Definition proper_join_inf := (@proper_join_inf X eqX leqX _ _ join_semilattice proper_join _).
    (* end hide *)

    (** An exact solution is in particular a weak one. *)
    Lemma exact_solution_is_weak_solution S E :
      exact_solution eqX S E -> weak_solution leqX S E.
    Proof.
      intros hyp;split.
      - intros e q I.
        rewrite (hyp q).
        + unfold ExprVar.
          etransitivity;[|apply inf_cup_left].
          apply Σ_bigger.
          apply in_flat_map;exists (e,q);split;[assumption|].
          simpl;simpl_beq;now left.
        + unfold vars_system;simpl_In;left.
          apply in_map_iff;exists (e,q);tauto.
      - intros p e q I.
        rewrite (hyp q).
        + unfold ExprVar;etransitivity;[|apply inf_cup_right].
          apply Σ_bigger.
          apply in_flat_map;exists (e,p,q);split;[assumption|].
          simpl;simpl_beq;now left.
        + unfold vars_system;simpl_In;right.
          apply in_flat_map;exists (e,p,q);split;[assumption|].
          now right;left.
    Qed.

    (** Equivalent vectors yield equivalent [ExprVar]. *)
    Lemma ExprVar_ext E F S q :
      (forall p, p ∈ vars_system S -> E p ⩵ F p) -> ExprVar E S q ⩵ ExprVar F S q.
    Proof.
      intros h1;unfold ExprVar;apply proper_join;[reflexivity|].
      cut (forall p e q, ((e,p),q) ∈ (snd S) -> p ∈ vars_system S).
      - induction (snd S) as [|((e,p),q0) l].
        + intros _;reflexivity.
        + intros hyp;simpl;unfold_eqX.
          * simpl;apply proper_join.
            -- rewrite h1;[reflexivity|].
               apply (hyp p e q);now left.
            -- apply IHl;intros ? ? ? I;eapply hyp;right;apply I.
          * simpl;apply IHl;intros ? ? ? I;eapply hyp;right;apply I.
      - clear q;intros p e q I;unfold vars_system;simpl_In;right.
        apply in_flat_map;exists ((e,p),q);split;[assumption|left;reflexivity].
    Qed.

    Lemma weak_solution_ext E F S :
      (forall p, p ∈ vars_system S -> E p ⩵ F p) -> weak_solution leqX S E <-> weak_solution leqX S F.
    Proof.
      intros hyp;unfold weak_solution;split;intros (h1&h2);(split;[intros e q|intros p e q];intros I).
      - rewrite <- hyp.
        + apply h1,I.
        + unfold vars_system;simpl_In;left.
          apply in_map_iff;exists (e,q);tauto.
      - rewrite <- hyp, <- hyp.
        + apply h2,I.
        + unfold vars_system;simpl_In;right.
          apply in_flat_map;exists ((e,p),q);split;[assumption|right;left;reflexivity].
        + unfold vars_system;simpl_In;right.
          apply in_flat_map;exists ((e,p),q);split;[assumption|left;reflexivity].
      - rewrite hyp.
        + apply h1,I.
        + unfold vars_system;simpl_In;left.
          apply in_map_iff;exists (e,q);tauto.
      - rewrite hyp, hyp.
        + apply h2,I.
        + unfold vars_system;simpl_In;right.
          apply in_flat_map;exists ((e,p),q);split;[assumption|right;left;reflexivity].
        + unfold vars_system;simpl_In;right.
          apply in_flat_map;exists ((e,p),q);split;[assumption|left;reflexivity].
    Qed.

    Lemma exact_solution_ext E F S :
      (forall p, p ∈ vars_system S -> E p ⩵ F p) -> exact_solution eqX S E <-> exact_solution eqX S F.
    Proof.
      intros hyp;split;intros h q I.
      - rewrite <- hyp by assumption.
        rewrite <- (ExprVar_ext q hyp).
        apply h,I.
      - rewrite hyp by assumption.
        rewrite (ExprVar_ext q hyp).
        apply h,I.
    Qed.

    Lemma lower_bound_ext E F S :
      (forall p, p ∈ vars_system S -> E p ⩵ F p) -> lower_bound leqX S E <-> lower_bound leqX S F.
    Proof.
      intros hyp;split;intros h G IG q Iq;rewrite <- (h G IG q Iq);rewrite (hyp _ Iq);reflexivity.
    Qed.

    Lemma least_solution_ext E F S :
      (forall p, p ∈ vars_system S -> E p ⩵ F p) ->
      least_solution leqX S E <-> least_solution leqX S F.
    Proof.
      intros hyp;split;intros (h1&h2);apply (weak_solution_ext hyp) in h1;
        apply (lower_bound_ext hyp) in h2;split;assumption.
    Qed.

    (**  The zero vector is always a lower bound. *)
    Lemma lower_bound_zero M : lower_bound leqX M (fun _ => zero).
    Proof. intros E _ ? _;apply zero_minimal. Qed.

    (** It's also the least solution of any system devoid of variables. *)
    Lemma solution_no_var M : sizeSys M = 0 -> exact_solution eqX M (fun _ => zero).
    Proof.
      intro E;unfold sizeSys in E;apply length_zero_iff_nil in E.
      destruct M as ([|(?&q)]&S);[destruct S as [|((?&q)&?)] |].
      - intros q;simpl;tauto.
      - exfalso;cut (q ∈ []);[intro h;apply h|].
        rewrite <- E;simpl_In;simpl;tauto.
      - exfalso;cut (q ∈ []);[intro h;apply h|].
        rewrite <- E;simpl_In;simpl;tauto.
    Qed.

    (** Eliminating variables eliminates variables. *)
    Lemma vars_elim M q : vars_system (elim_var M q) ⊆ vars_system M ∖ q.
    Proof.
      unfold vars_system,elim_var;simpl;intro;simpl_In.
      rewrite rm_In;simpl_In.
      rewrite map_app;simpl_In.
      intros [[I|I]|I].
      - apply in_map_iff in I as ((v,x)&<-&Ix);simpl_In in Ix.
        destruct Ix as (Ix&E).
        revert E;simpl;unfold_eqX;simpl;[discriminate|intros _].
        split;[|intros ->;tauto].
        left;apply in_map_iff;exists (v,x);simpl;tauto.
      - apply in_map_iff in I as ((v,x)&<-&Ix);simpl_In in Ix.
        apply in_flat_map in Ix as (((v'&x1)&x2)&I1&I2).
        revert I2;simpl;unfold_eqX;simpl;try tauto.
        intros [heq|F];[inversion heq;clear heq;subst|tauto].
        split;[|intros ->;tauto].
        right;apply in_flat_map;exists (v',q,x);simpl;tauto.
      - apply in_flat_map in I as (((v&x1)&x2)&I1&I2).
        apply in_flat_map in I1 as (((v'&y1)&y2)&I3&I4).
        revert I4;simpl;unfold_eqX;simpl;try tauto;subst.
        + intros I1;apply in_map_iff in I1 as ((w&z)&heq&Iz).
          inversion heq;clear heq;subst.
          destruct I2 as [<-|[<-|I2]];[| |simpl in I2;tauto];simpl.
          * unfold succ in Iz.
            apply in_flat_map in Iz as (((v&y1)&y2)&I&Iz).
            revert Iz;simpl;unfold_eqX;simpl;try tauto.
            intros [heq|F];[inversion heq;clear heq;subst|tauto].
            split;[|intros ->;tauto].
            right;apply in_flat_map;exists (w,x1,q);simpl;tauto.
          * split;[|intros ->;tauto].
            right;apply in_flat_map;exists (v',q,x2);simpl;tauto.
        + intros [heq|F];[inversion heq;clear heq;subst|tauto].
          destruct I2 as [<-|[<-|I2]];[| |simpl in I2;tauto];simpl;
            (split;[|intros ->;tauto]);right;apply in_flat_map;exists (v,x1,x2);simpl;tauto.
    Qed.

    (** The vector [solution_sys n M] is uniformly zero on variables
        that do not appear in the system. *)
    Lemma solution_sys_zero n M :
      forall x, ~ x ∈ vars_system M -> solution_sys n M x = zero.
    Proof.
      revert M;induction n;intros M x.
      - simpl;reflexivity.
      - intros nI;simpl.
        case_eq {{vars_system M}};[reflexivity|].
        intros q l E.
        unfold_eqX;subst.
        + exfalso;apply nI,In_undup;rewrite E;now left.
        + apply IHn.
          intros I;apply vars_elim,rm_In in I as (I&_).
          apply nI,I.
    Qed.

    (** For any weak solution [F] the following inequalities hold. *)
    Lemma loop_spec M F q : weak_solution leqX M F -> loop M q ⋆ · F q ≦ F q.
    Proof.
      intros hF.
      apply ka_star_left_ind.
      unfold loop;rewrite Σ_distr_r.
      apply Σ_bounded;intros f If.
      apply in_map_iff in If as (g&<-&Ig).
      apply in_flat_map in Ig as (((e,p'),q')&Ig&Ig').
      revert Ig';simpl;unfold_eqX;simpl;try tauto.
      intros [->|F'];[|tauto].
      apply hF;tauto.
    Qed.
    Lemma cst_spec M F q : weak_solution leqX M F -> cst M q ≦ F q.
    Proof.
      intros hF.
      unfold cst;apply Σ_bounded.
      intros f If.
      apply in_flat_map in If as ((e,p)&Ip&If).
      revert If;simpl;unfold_eqX;simpl;try tauto.
      intros [->|F'];[|tauto].
      apply hF;tauto.
    Qed.
    Lemma succ_spec M F q : weak_solution leqX M F -> forall e p, (e,p) ∈ succ M q -> e · F p ≦ F q.
    Proof.
      intros hF e p Ip.
      unfold succ in Ip;apply in_flat_map in Ip as (((e'&p')&q')&Ip'&Ip).
      revert Ip;simpl;unfold_eqX;simpl;try tauto.
      intros [heq|F'];[inversion heq;subst;clear heq|tauto].
      apply hF;tauto.
    Qed.

    (** Eliminating variables preserves weak solutions. *)
    Lemma elim_var_solutions M F q : weak_solution leqX M F -> weak_solution leqX (elim_var M q) F.
    Proof.
      intros hF;pose proof hF as (h1&h2);split.
      - intros e x.
        unfold elim_var;simpl;simpl_In.
        rewrite negb_true_iff,eqX_false;simpl.
        rewrite in_flat_map;simpl.
        intros [(I&N)|(((a&x1)&x2)&I1&I2)].
        + apply h1,I.
        + revert I2;simpl;unfold_eqX;simpl;try tauto.
          intros [heq|?];[inversion heq;clear heq;subst|tauto].
          rewrite (cst_spec _ hF),<-(mon_assoc _ _ _),(loop_spec _ hF).
          apply h2,I1.
      - intros x e y.
        unfold elim_var;simpl;simpl_In.
        rewrite in_flat_map.
        intros (((v,x1)&x2)&I&I').
        revert I';simpl;unfold_eqX;simpl;tauto||subst.
        + intro I';apply in_map_iff in I' as ((v'&y')&heq&Iy).
          inversion heq;clear heq;subst.
          rewrite <-(mon_assoc _ _ _),(succ_spec hF Iy).
          rewrite <-(mon_assoc _ _ _),(loop_spec _ hF).
          apply h2,I.
        + intros [heq|?];[inversion heq;clear heq;subst|tauto].
          apply h2,I.
    Qed.

    (** If the parameter [n] is big enough, [solution_sys n S] is an
        exact solution and a lower bound of the system [S]. *)
    Theorem solution_sys_spec S n :
      sizeSys S <= n ->
      exact_solution eqX S (solution_sys n S)
      /\ lower_bound leqX S (solution_sys n S).  
    Proof.
      revert S;induction n;intros M hn.
      - split;[apply solution_no_var;lia|apply lower_bound_zero].
      - simpl;case_eq {{vars_system M}}.
        + intros E;split;[|apply lower_bound_zero].
          apply solution_no_var.
          unfold sizeSys;rewrite E;reflexivity.
        + intros q V EV.
          destruct (IHn (elim_var M q)) as (sol&least);[|clear hn IHn].
          * transitivity (⎢{{vars_system M}}∖q⎥);
              [apply NoDup_incl_length;[apply NoDup_undup
                                       |repeat rewrite undup_equivalent;apply vars_elim]|].
            rewrite EV;simpl;simpl_eqX;simpl.
            unfold sizeSys in hn;rewrite EV in hn;simpl in hn.
            unfold rm;rewrite filter_length;lia.
          * revert sol least.
            set (M' := elim_var M q).
            set (E := (solution_sys n M')).
            set (q_expr := loop M q ⋆ · (cst M q ∪ Σ (map (fun C : X * Q => fst C · E (snd C))
                                                          (succ M q)))).
            set (E' := (fun p : Q => if p =?= q then q_expr else E p)).
            intros sol least.
            cut (exact_solution eqX M E');[intro solE';split;[assumption|]|].
            -- intros F solF.
               intros p Ip.
               unfold E';unfold_eqX;subst;[|case_in p (vars_system M');
                                            [apply least;[apply elim_var_solutions,solF|assumption]
                                            |unfold E;rewrite (solution_sys_zero _ I);
                                             apply zero_minimal]].
               unfold q_expr;rewrite semiring_left_distr.
               apply inf_join_inf.
               ++ rewrite <- (loop_spec _ solF),(cst_spec _ solF);reflexivity.
               ++ rewrite <- (loop_spec _ solF);apply proper_prod_inf;[reflexivity|].
                  apply Σ_bounded;intros f If.
                  apply in_map_iff in If as ((g&p)&<-&I).
                  simpl.
                  rewrite <- (succ_spec solF I).
                  apply proper_prod_inf;[reflexivity|].
                  case_in p (vars_system M');
                    [apply least;[apply elim_var_solutions,solF|assumption]
                    |unfold E;rewrite (solution_sys_zero _ I0);
                     apply zero_minimal].
            -- intros p Ip.
               unfold E' at 1;destruct_eqX p q;[|case_in p (vars_system M')].
               ++ subst;unfold ExprVar,q_expr.
                  transitivity (cst M q ∪ ((loop M q · q_expr)
                                             ∪ Σ (map (fun C : X * Q => fst C · E (snd C)) (succ M q)))).
                  ** apply poX;unfold Basics.flip;split.
                     --- transitivity
                           (cst M q ∪ (Σ (map (fun C : X * Q => fst C · E (snd C)) (succ M q))
                                         ∪ loop M q· q_expr));
                           [|apply proper_join_inf;
                             [reflexivity|rewrite (semiring_comm _ _);reflexivity]].
                         rewrite (mon_assoc _ _).
                         etransitivity;[apply proper_prod_inf;[reflexivity|apply inf_cup_left]|].
                         apply ka_star_left_ind.
                         rewrite (semiring_left_distr _ _ _).
                         apply inf_join_inf.
                         +++ etransitivity;[|apply inf_cup_right].
                             apply proper_prod_inf;[reflexivity|].
                             unfold q_expr.
                             rewrite <- one_inf_star.
                             rewrite left_unit.
                             reflexivity.
                         +++ etransitivity;[|apply inf_cup_right].
                             apply proper_prod_inf;[reflexivity|].
                             unfold q_expr.
                             rewrite <- ka_star_unfold at 2.
                             rewrite (semiring_right_distr _ _ _).
                             etransitivity;[|apply inf_cup_right].
                             rewrite (mon_assoc _ _ _);reflexivity.
                     --- apply inf_join_inf;[|apply inf_join_inf].
                         +++ rewrite <- one_inf_star.
                             rewrite left_unit.
                             apply inf_cup_left.
                         +++ rewrite <- ka_star_unfold.
                             rewrite (semiring_right_distr _ _ _).
                             etransitivity;[|apply inf_cup_right].
                             rewrite <- (mon_assoc _ _ _).
                             reflexivity.
                         +++ rewrite <- one_inf_star.
                             rewrite left_unit.
                             apply inf_cup_right.
                  ** unfold cst,loop.
                     etransitivity;[apply proper_join;
                                    [reflexivity|apply proper_join;[apply  Σ_distr_r|reflexivity]]|].
                     etransitivity;[apply proper_join;[reflexivity|apply algebra.Σ_app]|].
                     etransitivity;[apply algebra.Σ_app|].
                     etransitivity;[|symmetry;apply algebra.Σ_app].
                     apply poX;unfold Basics.flip;split;
                       apply Σ_bounded;intros f If;simpl_In in If.
                     --- destruct If as [If|[If|If]].
                         +++ apply in_flat_map in If as ((e&p)&I&If).
                             revert If;simpl;unfold_eqX;simpl;try tauto.
                             intros [->|F];[|tauto];subst.
                             apply Σ_bigger;simpl_In;left.
                             apply in_flat_map;exists (f,q);simpl;simpl_eqX;simpl;tauto.
                         +++ apply in_map_iff in If as (g&<-&Ig).
                             apply in_flat_map in Ig as (((e&p)&q')&I&Ig).
                             revert Ig;simpl;unfold_eqX;simpl;tauto||subst.
                             intros [->|F];[|tauto];subst.
                             apply Σ_bigger;simpl_In;right.
                             apply in_flat_map;exists (g,q,q);simpl;simpl_eqX;simpl.
                             split;[assumption|].
                             left.
                             unfold E';simpl_eqX;reflexivity.
                         +++ apply in_map_iff in If as ((e&g)&<-&Ig).
                             unfold succ in Ig.
                             apply in_flat_map in Ig as (((e'&p)&q')&I&Ig).
                             revert Ig;simpl;unfold_eqX;simpl;tauto||subst.
                             intros [heq|F];[inversion heq;clear heq|tauto];subst.
                             apply Σ_bigger;simpl_In;right.
                             apply in_flat_map;exists (e,g,q);simpl;simpl_eqX;simpl.
                             split;[assumption|].
                             left.
                             unfold E';simpl_eqX;reflexivity.
                     --- destruct If as [If|If].
                         +++ apply in_flat_map in If as ((e&p)&Ie&If).
                             revert If;simpl;unfold_eqX;simpl;try tauto.
                             intros [->|F];[|tauto];subst.
                             apply Σ_bigger;simpl_In;left.
                             apply in_flat_map;exists (f,q);simpl;simpl_eqX;simpl;tauto.
                         +++ apply in_flat_map in If as (((e&p)&p')&Ie&If).
                             revert If;simpl;unfold_eqX;simpl;try tauto.
                             intros [<-|F];[|tauto];subst.
                             unfold E';unfold_eqX.
                             *** subst;apply Σ_bigger;simpl_In;right.
                                 simpl_In;left.
                                 apply in_map_iff;exists e;split;[reflexivity|].
                                 apply in_flat_map;exists (e,q,q);split;[assumption|].
                                 simpl;simpl_beq;now left.
                             *** subst;apply Σ_bigger;simpl_In;right.
                                 simpl_In;right.
                                 apply in_map_iff;exists (e,p);split;[reflexivity|].
                                 unfold succ.
                                 apply in_flat_map;exists (e,p,q);split;[assumption|].
                                 simpl;simpl_eqX;now left.
               ++ rewrite (sol _ I).
                  apply poX;unfold Basics.flip;split;unfold ExprVar;
                    apply inf_join_inf;apply Σ_bounded;intros f If;simpl in *;simpl_In in If.
                  ** apply in_flat_map in If as ((e&p')&Ip'&If).
                     revert If;simpl;unfold_eqX;simpl;try tauto.
                     intros [<-|F];[|tauto];subst.
                     clear I sol least.
                     simpl_In in Ip'.
                     destruct Ip' as [(Ip'&_)|Ip'].
                     --- etransitivity;[|apply inf_cup_left].
                         apply Σ_bigger,in_flat_map;exists (e,p);simpl;simpl_eqX;simpl;tauto.
                     --- apply in_flat_map in Ip' as (((f&p')&q')&Ip'&Ie).
                         revert Ie;simpl;simpl_eqX;unfold_eqX;simpl;try tauto.
                         intros [heq|F];[inversion heq;clear heq|tauto];subst.
                         transitivity (f · E' q).
                         +++ unfold E';simpl_eqX.
                             rewrite <- (mon_assoc _ _ _).
                             apply proper_prod_inf;[reflexivity|].
                             unfold q_expr.
                             apply proper_prod_inf;[reflexivity|].
                             apply inf_cup_left.
                         +++ etransitivity;[|apply inf_cup_right].
                             apply Σ_bigger,in_flat_map;exists (f,q,p);simpl;simpl_eqX;simpl;tauto.
                  ** apply in_flat_map in If as (((e&p')&q')&Ip'&If).
                     revert If;simpl;unfold_eqX;simpl;try tauto.
                     intros [<-|F];[|tauto];subst.
                     etransitivity;[|apply inf_cup_right].
                     apply in_flat_map in Ip' as (((f&q1)&q2)&If&Ip').
                     revert Ip';simpl.
                     destruct_eqX q2 q;[simpl;tauto|].
                     destruct_eqX q1 q;simpl;subst.
                     --- intros Ip'.
                         apply in_map_iff in Ip' as ((g&q')&heq&Ig).
                         inversion heq;clear heq;subst.
                         transitivity (f · E' q).
                         +++ repeat rewrite <- (mon_assoc _ _ _).
                             apply proper_prod_inf;[reflexivity|].
                             unfold E';simpl_eqX;unfold q_expr.
                             apply proper_prod_inf;[reflexivity|].
                             etransitivity;[|apply inf_cup_right].
                             apply Σ_bigger,in_map_iff;exists (g,p');simpl;tauto.
                         +++ apply Σ_bigger,in_flat_map;exists (f,q,p);simpl;simpl_eqX;simpl;tauto.
                     --- intros [heq|F];[inversion heq;clear heq;subst|tauto].
                         apply Σ_bigger,in_flat_map;exists (e,p',p);unfold E';simpl;simpl_eqX;simpl;tauto.
                  ** apply in_flat_map in If as ((e&p')&Ip'&If).
                     revert If;simpl;unfold_eqX;simpl;try tauto.
                     intros [<-|F];[|tauto];subst.
                     etransitivity;[|apply inf_cup_left].
                     apply Σ_bigger,in_flat_map;exists (e,p);split;[|simpl;simpl_eqX;now left].
                     simpl_In;left.
                     simpl;simpl_eqX;tauto.
                  ** apply in_flat_map in If as (((e&p')&q')&Ip'&If).
                     revert If;simpl;unfold_eqX;simpl;try tauto.
                     intros [<-|F];[|tauto];subst.
                     unfold E';unfold_eqX;subst.
                     --- unfold q_expr.
                         rewrite (mon_assoc _ _ _).
                         rewrite (semiring_left_distr _ _ _).
                         apply inf_join_inf.
                         +++ etransitivity;[|apply inf_cup_left].
                             apply Σ_bigger,in_flat_map;exists (e·loop M q⋆·cst M q,p);simpl.
                             split;[|simpl_eqX;simpl;tauto].
                             simpl_In;right.
                             apply in_flat_map;exists (e,q,p);split;[assumption|].
                             simpl;simpl_eqX;simpl;tauto.
                         +++ repeat rewrite Σ_distr_l.
                             repeat rewrite map_map.
                             transitivity(Σ (map (fun x => (e · loop M q⋆ · fst x) · E (snd x))
                                                 (succ M q))).
                             *** apply Σ_bounded;intros f If.
                                 apply in_map_iff in If as ((g&p')&<-&I').
                                 rewrite (mon_assoc _ _ _).
                                 apply Σ_bigger,in_map_iff;exists (g,p');tauto.
                             *** etransitivity;[|apply inf_cup_right].
                                 apply Σ_incl;intros f If.
                                 apply in_map_iff in If as ((g&p')&<-&I').
                                 simpl;apply in_flat_map;exists ((e · loop M q ⋆) · g,p',p).
                                 simpl;simpl_eqX;simpl;split;[|tauto].
                                 apply in_flat_map;exists (e,q,p);split;[assumption|].
                                 simpl;simpl_eqX;simpl.
                                 apply in_map_iff;exists (g,p');simpl;tauto.
                     --- etransitivity;[|apply inf_cup_right].
                         apply Σ_bigger,in_flat_map;exists (e,p',p);simpl;simpl_eqX;simpl.
                         split;[|tauto].
                         apply in_flat_map;exists (e,p',p);split;[assumption|].
                         simpl;simpl_eqX;simpl;tauto.
               ++ unfold E;rewrite (solution_sys_zero _ I).
                  unfold ExprVar.
                  replace (flat_map (fun L => if snd L =?= p then [fst L] else []) (fst M))
                    with (@nil X).
                  ** replace (flat_map (fun L => if snd L =?= p
                                              then [fst (fst L) · E' (snd (fst L))] else [])
                                       (snd M))
                       with (@nil X);[simpl;rewrite (ka_idem _);reflexivity|].
                     symmetry.
                     cut (forall L, L ∈ (snd M) -> snd L <> p).
                     --- generalize (snd M).
                         clear;induction l;simpl;[reflexivity|].
                         intro hyp.
                         transitivity (@nil X++[]);[|reflexivity].
                         f_equal.
                         +++ unfold_eqX;[|reflexivity].
                             exfalso;apply (hyp a);tauto.
                         +++ apply IHl;intros;apply hyp;tauto.
                     --- intros ((f&p')&q').
                         simpl;intros I' ->.
                         apply I;unfold vars_system.
                         destruct_eqX p' q;subst.
                         +++ simpl_In;left.
                             apply in_map_iff;exists((f · loop M q ⋆) · cst M q,p);split;[reflexivity|].
                             simpl;simpl_In;right.
                             apply in_flat_map;exists (f,q,p);split;[assumption|].
                             simpl;simpl_eqX;simpl;tauto.
                         +++ simpl_In;right.
                             apply in_flat_map;exists (f,p',p);split;[|simpl;tauto].
                             simpl;simpl_In.
                             apply in_flat_map;exists (f,p',p);simpl;simpl_eqX;simpl;tauto.
                  ** cut (forall L, L ∈ (fst M) -> snd L <> p).
                     --- generalize (fst M).
                         clear;induction l;simpl;[reflexivity|].
                         intro hyp.
                         transitivity (@nil X++[]);[reflexivity|].
                         f_equal.
                         +++ unfold_eqX;[|reflexivity].
                             exfalso;apply (hyp a);tauto.
                         +++ apply IHl;intros;apply hyp;tauto.
                     --- intros (f&p').
                         simpl;intros I' ->.
                         apply I;unfold vars_system.
                         simpl_In;left.
                         apply in_map_iff;exists(f,p);split;[reflexivity|].
                         simpl;simpl_In;left.
                         simpl_eqX;simpl;tauto.
    Qed.

    (** Every least solution is in fact an exact solution. *)
    Lemma least_solution_is_exact S E :
      least_solution leqX S E -> exact_solution eqX S E.
    Proof.
      intros (ws&lb).
      set (n := sizeSys S).
      assert (hyp : n <= sizeSys S) by reflexivity.
      apply solution_sys_spec in hyp as (h1&h2).
      revert h1 h2;set(E0 := (solution_sys (sizeSys S) S));intros.
      cut (forall q, q ∈ vars_system S -> E q ⩵ E0 q).
      - intros h q Iq;rewrite (h q Iq),(h1 q Iq).
        clear ws lb h1 h2.
        unfold ExprVar;simpl;apply proper_join;[reflexivity|].
        clear Iq;revert h;unfold vars_system;simpl.
        induction (snd S)  as [|((a,p1),p2) l];intros h;[reflexivity|].
        simpl;unfold_eqX;simpl.
        + apply proper_join.
          * rewrite h;[reflexivity|].
             simpl_In;right;apply in_flat_map;exists (a,p1,q);simpl;tauto.
          * apply IHl.
            revert h;clear;intros h r I; apply h.
            revert I;simpl;simpl_In;tauto.
        + apply IHl.
          revert h;clear;intros h r I; apply h.
          revert I;simpl;simpl_In;tauto.
      - intros q Iq;apply poX;unfold Basics.flip;split.
        * apply lb,Iq.
          eapply exact_solution_is_weak_solution,h1.
        * apply h2,Iq;apply ws.
    Qed.
    
  End solutions.

  (** Now, if we generalize the previous result, we show that for
      every system, the vector [solution_sys(sizeSys S) S] is the
      least solution of [S] for every choice of [⩵,≦], as long as they
      satisfy the axioms of Kleene algebras. *)
  Corollary least_solution_exists : forall S : system,
      forall (eqX leqX : relation X),
      forall (equivX : @Equivalence X eqX) (preX : @PreOrder X leqX),
      forall (poX : @PartialOrder X eqX equivX leqX preX),
      forall (kaX : @KleeneAlgebra X eqX leqX jX pX zX uX sX),
        least_solution leqX S (solution_sys (sizeSys S) S).
  Proof.
    intros;split.
    - apply exact_solution_is_weak_solution,solution_sys_spec;reflexivity.
    - apply solution_sys_spec;reflexivity.
  Qed.
  
End system.

Arguments system : clear implicits.

(** * Automata as affine systems *)
Section automata_system.
  Context {X : Set}{decX: decidable_set X }.
  Context {Q : Set}{decQ: decidable_set Q }.

  (** Given an [NFA] with states of type [Q] and alphabet of type [X],
      we may generate a system [sys_of_NFA A] with constants [regexp X] and
      variables [Q]. *)
  Definition sys_of_NFA {Q : Set} (A : NFA Q X) : system Q (@regexp X) :=
    (map (fun q => (e_un,q)) (fst A),
     map (fun tr => (⟪snd(fst tr)⟫,snd tr,fst(fst tr))) (snd A)).

  (** There exists vector that assigns to every state a regular
      expression denoting its language, and that is a weak solution of
      [sys_of_NFA A]. *)
  Lemma sys_of_NFA_solution (A : NFA Q X) :
    exists F,
      (forall q, ⟦F q⟧ ≃ langNFA A q)
      /\ weak_solution (fun e f => ⟦e⟧ ≲ ⟦f⟧) (sys_of_NFA A) F.
  Proof.
    cut (exists F, forall q, ⟦F q⟧ ≃ langNFA A q).
    - intros (F&hF);exists F;split;[apply hF|].
      unfold sys_of_NFA;split;simpl.
      + intros e q;rewrite in_map_iff;intros (p&heq&I);inversion heq;clear heq;subst.
        intros ? ->;apply hF;exists q;simpl;tauto.
      + intros p e q;rewrite in_map_iff;intros (((p',x),q')&heq&I);inversion heq;clear heq;subst.
        intros ? (?&u&->&->&Iu).
        apply hF in Iu as (f&P&If);apply hF.
        exists f;split;[|assumption].
        exists p;split;tauto.
    - cut (forall qs, qs ⊆ statesNFA A -> exists F, forall q, q ∈ qs -> ⟦F q⟧ ≃ langNFA A q).
      + intros h;destruct (h (statesNFA A)) as (F&hF);[reflexivity|].
        exists (fun q => if inb q (statesNFA A) then F q else zero).
        intros q;case_in q (statesNFA A);[apply hF,I|].
        intros u;split;intros Iu;exfalso;[apply Iu|apply I;apply statesNFA_spec].
        destruct Iu as (f&P&If).
        destruct u as [|x u].
        * rewrite P in *;tauto.
        * destruct P as (p&Tr&_);right;exists (q,x,p);simpl;tauto.
      + induction qs as [|q qs].
        * intros _;exists (fun _ => zero);intro;simpl;tauto.
        * intro I;destruct IHqs as (F&hF).
          -- intros p Ip;apply I;now right.
          -- case_in q qs.
             ++ exists F;intros p [<-|Ip];apply hF;assumption.
             ++ assert (R: rational (langNFA A q)) by (unfold rational;exists Q,decQ,A,q;reflexivity).
                apply KleeneTheorem in R as (e&R).
                exists (fun p => if p =?= q then e else F p).
                intros p [<-|Ip];simpl_eqX.
                ** assumption.
                ** apply hF,Ip.
  Qed.

  (** [pathSys M p u q n] is a proposition saying ``there exists a
      path in [M] of length not exceeding [n] from [p] to [q] labelled
      with [u]''.*)
  Fixpoint pathSys (M : system Q (@regexp X)) p u q n :=
    match n with
    | 0 => p = q /\ u = []
    | S n => exists e r v1 v2 , u = v1 ++ v2 /\ (e,r,p) ∈ (snd M) /\ ⟦e⟧ v1 /\ pathSys M r v2 q n
    end.

  (** [langSys M q] is the set of words [uv] such that there is a path
  from [q] to some state [p] labelled with [u], [e<=p] is in [M] and
  [v∈⟦e⟧]. *)
  Definition langSys M q : (@language X) :=
    fun u => exists n p e v1 v2, u = v1 ++ v2 /\ pathSys M q v1 p n /\ (e,p) ∈ fst M /\ ⟦e⟧ v2.

  (** Every weak solution (w.r.t. language ordering) is greater than
      [langSys M q]. *)
  Lemma langSys_inf_sol M F :
    weak_solution (fun e f => ⟦e⟧ ≲ ⟦f⟧) M F -> forall q, langSys M q ≲ ⟦F q⟧.
  Proof.
    intros (hcst&hvar) q u (n&p&e&v&w&->&P&Ie&Iw).
    revert q v P;induction n;intros q v P.
    - destruct P as (->&->);simpl.
      apply (hcst e p Ie w Iw).
    - destruct P as (f&r&v1&v2&->&Tr&If&P).
      rewrite app_ass.
      apply (hvar r f q Tr).
      exists v1,(v2++w);split;[reflexivity|split;[assumption|]].
      apply (IHn r v2 P).
  Qed.

  (** The language of an NFA is contained in the language of its
      system. *)
  Lemma sys_of_NFA_lang A q : langNFA A q ≲ langSys (sys_of_NFA A) q.
  Proof.
    intros u (f&P&If);exists ⎢u⎥,f,un,u,[];split;[|split;[|split]].
    - rewrite app_nil_r;reflexivity.
    - clear If;revert q P;induction u as [|x u];intros q Iq;simpl.
      + rewrite Iq;tauto.
      + destruct Iq as (p&Tr&P).
        exists ⟪x⟫,p,[x],u;split;[reflexivity|].
        split;[|split;[reflexivity|]].
        * apply in_map_iff;exists (q,x,p);simpl;tauto.
        * apply IHu,P.
    - unfold sys_of_NFA;simpl;apply in_map_iff;exists f;tauto.
    - reflexivity.
  Qed.

  Definition eqX := (fun e f :@regexp X => ⟦e⟧ ≃ ⟦f⟧).
  Definition leqX := (fun e f :@regexp X => ⟦e⟧ ≲ ⟦f⟧).
  
  Instance eqX_eq : Equivalence eqX.
  Proof.
    split;intro;intros;unfold eqX.
    - reflexivity.
    - symmetry;apply H.
    - etransitivity;eassumption.
  Qed.
        
  Instance leqX_o : PreOrder leqX.
  Proof.
    split;intro;intros;unfold leqX.
    - reflexivity.
    - etransitivity;eassumption.
  Qed.

  Instance leqX_po : PartialOrder eqX leqX.
  Proof. intros x y;unfold eqX,leqX;apply inf_lang_PartialOrder. Qed.

  Instance kaX : KleeneAlgebra regexp eqX leqX.
  Proof.
    unfold eqX,leqX;split.
    - intros x y E x' y' E';simpl;rewrite E,E';reflexivity.
    - intros x y E x' y' E';simpl;rewrite E,E';reflexivity.
    - intros x y E;simpl;rewrite E;reflexivity.
    - split.
      + split.
        * intros a b c;simpl;apply mon_assoc.
        * split;intro a;simpl;[apply left_unit|apply right_unit].
      + split.
        * intros a b c;simpl;apply mon_assoc.
        * split;intro a;simpl;[apply left_unit|apply right_unit].
      + intros a b;simpl;apply semiring_comm.
      + split;intro a;simpl;[apply left_absorbing|apply right_absorbing].
      + intros a b c;simpl;apply semiring_left_distr.
      + intros a b c;simpl;apply semiring_right_distr.
    - intros a;simpl;apply ka_idem.
    - intros a b;simpl;apply ka_joinOrder.
    - intro a;simpl;apply ka_star_unfold.
    - intros a b;simpl;apply ka_star_left_ind.
    - intros a b;simpl;apply ka_star_right_ind.
  Qed.

  (** There is a least solution of [sys_of_NFA A] that associates to
      every state its language. *)
  Theorem sys_of_NFA_least_solution (A : NFA Q X) :
    exists F, (forall q, ⟦F q⟧ ≃ langNFA A q) /\ least_solution (fun e f => ⟦e⟧ ≲ ⟦f⟧) (sys_of_NFA A) F.
  Proof.
    destruct (sys_of_NFA_solution A) as (F&EF&WF);exists F;split;[assumption|].
    split;[assumption|].
    intros G WG q Iq.
    rewrite EF, sys_of_NFA_lang.
    apply langSys_inf_sol,WG.
  Qed.
  
End automata_system.

(** * The Antimirov system *)
Section regexp.
  Context {X : Set}{decX: decidable_set X }.
    
  Lemma vars_Antimirov e : vars_system (sys_of_NFA (NFA_of_regexp e)) ⊆ stateSpace e.
  Proof.
    unfold vars_system,sys_of_NFA,NFA_of_regexp;simpl;intros f;simpl_In.
    repeat setoid_rewrite in_map_iff||setoid_rewrite in_flat_map;simpl;simpl_In.
    intros [I|I].
    - destruct I as ((e1,e2)&<-&g&<-&I).
      simpl_In in I;tauto.
    - destruct I as (((e1,e2),e3)&(((f1&x)&f3)&<-&I1)&I2).
      destruct I1 as (g&Ig&g'&Ig'&g''&E&Ig'').
      inversion E;clear E;subst.
      simpl in I2;destruct I2 as [<-|[<-|F]];[|tauto|tauto].
      eapply stateSpace_trans;[eassumption|].
      eapply δA_stateSpace;eauto.
  Qed.

  Lemma Antimirov_inf e a f : e ∈ δA a f -> ⟪a⟫·e<=KA f.
  Proof.
    revert e;induction f;intro e;simpl;try tauto.
    - simpl_In;intros [I|I];[rewrite IHf1 by assumption|rewrite IHf2 by assumption].
      + apply inf_cup_left.
      + apply inf_cup_right.
    - simpl_In;rewrite in_map_iff;(intros [I|I];[|revert I;unfold_eqX;[intro I|simpl;tauto]]).
      + destruct I as (f&<-&I).
        rewrite (mon_assoc _ _ _),(IHf1 _ I);reflexivity.
      + rewrite (IHf2 _ I).
        rewrite <- (@left_unit _ _ prod un _) at 1.
        unfold un,regUn;simpl;rewrite <-E,ϵ_inf_e;reflexivity.
    - rewrite in_map_iff;intros (g&<-&Ig).
      rewrite (mon_assoc _ _ _).
      rewrite (IHf _ Ig).
      replace (e_star f) with (star f) by reflexivity.
      rewrite <- ka_star_unfold at 2.
      apply inf_cup_right.
    - unfold_eqX;simpl;[|tauto].
      intros [<-|F];[|tauto].
      apply ax_eq_inf;eauto.
  Qed.

  Theorem Antimirov_fundamental_theorem e A : Var e ⊆ A -> e =KA ϵ e ∪ Σ_{A} (fun a => ⟪a⟫·Σ (δA a e)).
  Proof.
    intros V;induction e.
    - simpl.
      erewrite join_list_equivalent;[rewrite (KA_ACI0 (join_list_zero _ ));eauto| |reflexivity].
      intros x Ix;simpl;eauto.
    - simpl.
      erewrite join_list_equivalent;[rewrite (KA_ACI0 (join_list_zero _ ));eauto| |reflexivity].
      intros x Ix;simpl;eauto.
    - replace e_add with join by reflexivity.
      rewrite ϵ_add;simpl.
      rewrite IHe1 at 1 by (intros x I;apply V;simpl;simpl_In;tauto).
      repeat rewrite <- (mon_assoc _ _ _).
      apply ax_eq_add;[reflexivity|].
      rewrite IHe2 at 1 by (intros x I;apply V;simpl;simpl_In;tauto).
      rewrite (semiring_comm _ _).
      repeat rewrite <- (mon_assoc _ _ _).
      apply ax_eq_add;[reflexivity|].
      rewrite (semiring_comm _ _).
      rewrite <- (KA_ACI0 (join_list_add _ _ _)).
      apply join_list_equivalent;[|reflexivity].
      intros a _;rewrite <- semiring_left_distr,algebra.Σ_app;reflexivity.
    - replace e_prod with prod by reflexivity.
      rewrite ϵ_prod;simpl.
      rewrite IHe1 at 1 by (intros x I;apply V;simpl;simpl_In;tauto).
      rewrite semiring_right_distr.
      rewrite IHe2 at 1 by (intros x I;apply V;simpl;simpl_In;tauto);clear.
      rewrite semiring_left_distr.
      repeat rewrite <- (mon_assoc _ _ _).
      apply ax_eq_add;[reflexivity|].
      rewrite (semiring_comm _ _).
      rewrite <- join_list_left_distr.
      rewrite <- join_list_right_distr.
      rewrite <- (KA_ACI0 (join_list_add _ _ _)).
      apply join_list_equivalent;[|reflexivity].
      intros a _;rewrite <- algebra.Σ_app,semiring_left_distr;apply ax_eq_add.
      + rewrite <- (mon_assoc _ _ _),Σ_distr_r;reflexivity.
      + repeat rewrite Σ_distr_l.
        destruct (ϵ_zero_or_un e1) as [-> | ->];simpl_eqX;simpl;
          [replace e_un with un by reflexivity|].
        * apply ax_inf_PartialOrder;unfold Basics.flip;split;apply Σ_bounded;intros f If.
          -- apply in_map_iff in If as (g&<-&Ig).
             rewrite left_unit;apply Σ_bigger;tauto.
          -- transitivity (prod un f);[rewrite left_unit;reflexivity|].
             apply Σ_bigger,in_map_iff;exists f;tauto.
        * replace (prod e_zero) with (prod zero) by reflexivity.
          clear N;induction (δA a e2) as [|e l];simpl;[reflexivity|].
          rewrite IHl,left_absorbing,(ka_idem _);reflexivity.
    - replace e_star with star by reflexivity.
      simpl in V;apply IHe in V;clear IHe;simpl;replace e_un with un by reflexivity.
      apply ax_inf_PartialOrder;unfold Basics.flip;split.
      + transitivity ((𝟭 ∪ Σ_{ A} (fun a : X => ⟪a⟫·Σ (map (fun g : regexp => g · e ⋆) (δA a e))))·e⋆);
          [etransitivity;[|apply proper_prod_inf;[apply inf_cup_left|reflexivity]];
           rewrite left_unit;reflexivity|].
        apply ka_star_right_ind.
        rewrite semiring_right_distr,left_unit.
        apply inf_join_inf.
        * rewrite V at 1;apply inf_join_inf.
          -- rewrite ϵ_sub_id;apply inf_cup_left.
          -- etransitivity;[|apply inf_cup_right].
             clear V;induction A;simpl;[reflexivity|].
             apply proper_join_inf;[|assumption].
             apply proper_prod_inf;[reflexivity|].
             apply Σ_bounded;intros f If.
             transitivity (f·e⋆);[rewrite <- one_inf_star,right_unit;reflexivity|].
             apply Σ_bigger,in_map_iff;exists f;tauto.
        * rewrite <- join_list_right_distr.
          etransitivity;[|apply inf_cup_right].
          clear V;induction A;simpl;[reflexivity|].
          apply proper_join_inf;[|assumption].
          rewrite <- (mon_assoc _ _ _).
          apply proper_prod_inf;[reflexivity|].          
          rewrite Σ_distr_r,map_map.
          apply Σ_bounded;intros f If.
          apply in_map_iff in If as (g&<-&Ig).
          rewrite <- (mon_assoc _ _ _).
          transitivity (g · e⋆);
            [apply proper_prod_inf;[reflexivity
                                   |rewrite <- ka_star_unfold_right at 2;apply inf_cup_right]|].
          apply Σ_bigger,in_map_iff;exists g;tauto.
      + rewrite (ka_star_unfold_eq e).
        apply proper_join_inf;[reflexivity|].
        rewrite V at 1;rewrite semiring_right_distr.
        etransitivity;[|apply inf_cup_right].
        rewrite <- join_list_right_distr.
        clear V;induction A;simpl;[reflexivity|].
        apply proper_join_inf;[|assumption].
        rewrite <- (mon_assoc _ _ _).
        apply proper_prod_inf;[reflexivity|].           
        apply Σ_bounded;intros f If.
        apply in_map_iff in If as (g&<-&Ig).
        apply proper_prod_inf;[|reflexivity].
        apply Σ_bigger;tauto.
    - simpl;replace e_zero with zero by reflexivity.
      rewrite left_unit.
      cut (x ∈ A);[|apply V;now left].
      cut ((forall x, x ∈ A ->
                 Σ_{ A} (fun a : X =>  ⟪ a ⟫ ·Σ (if a =?= x then [e_un] else [])) =KA ⟪ x ⟫)
           /\ (forall x,~ x ∈ A ->
                Σ_{ A} (fun a : X =>  ⟪ a ⟫ ·Σ (if a =?= x then [e_un] else [])) =KA (@e_zero X)));
        [intros (h&_) I;rewrite (h _ I);reflexivity|clear x V].
      induction A;simpl;[split;intro x;[tauto|reflexivity]|].
      destruct IHA as (h1&h2).
      split;intros x;case_in x A;unfold_eqX;tauto||intros _.
      + rewrite h1 by assumption;simpl.
        rewrite right_unit.
        replace e_un with un by reflexivity.
        rewrite right_unit,(ka_idem _);reflexivity.
      + simpl;rewrite right_absorbing,left_unit.
        apply h1,I.
      + rewrite h2 by assumption;simpl.
        rewrite right_unit.
        replace e_un with un by reflexivity.
        replace e_zero with zero by reflexivity.
        rewrite right_unit,right_unit;reflexivity.
      + rewrite h2 by assumption;simpl.
        rewrite right_absorbing,(ka_idem _);reflexivity.
  Qed.
  
  Lemma Antimirov_sys e :
    exact_solution (ax_eq KA KA') (sys_of_NFA (NFA_of_regexp e)) id.
  Proof.
    intros f If;simpl;unfold ExprVar,id.
    apply vars_Antimirov in If.
    rewrite (Antimirov_fundamental_theorem (stateSpace_Var If)).
    apply ax_eq_add.
    + destruct (ϵ_zero_or_un f) as [E|E];rewrite E;apply ax_inf_PartialOrder;
        unfold Basics.flip;split.
      * apply Σ_bigger;apply in_flat_map;exists (e_un,f);simpl;simpl_eqX;split;[|now left].
        apply in_map_iff;exists f;split;[reflexivity|simpl_In].
        split;[assumption|].
        rewrite E;simpl_eqX;reflexivity.
      * apply Σ_bounded;intros g Ig.
        apply in_flat_map in Ig as ((x&h)&Ih&Ig).
        revert Ig;simpl;unfold_eqX;simpl;[subst|tauto].
        intros [<-|F];[|tauto].
        unfold sys_of_NFA,NFA_of_regexp in Ih;simpl in Ih.
        apply in_map_iff in Ih as (g&heq&Ig).
        inversion heq;clear heq;subst;reflexivity.
      * replace e_zero with zero by reflexivity;apply zero_minimal.
      * replace (flat_map _ _) with (@nil (@regexp X));[reflexivity|].
        symmetry.
        cut (forall g, g ∈ (fst (sys_of_NFA (NFA_of_regexp e))) ->
                  (fun L : regexp * regexp => if snd L =?= f then [fst L] else []) g = []).
        -- clear;intro h;induction (fst (sys_of_NFA (NFA_of_regexp e))) as [|L l];[reflexivity|].
           simpl;rewrite h,IHl.
           ++ reflexivity.
           ++ intros;apply h;now right.
           ++ now left.
        -- intros h Ih.
           unfold sys_of_NFA,NFA_of_regexp in Ih;simpl in Ih.
           apply in_map_iff in Ih as (g&<-&Ig);simpl.
           unfold_eqX;[subst|reflexivity].
           simpl_In in Ig;destruct Ig as (_&Eg).
           rewrite E in Eg;revert Eg;simpl_eqX;discriminate.
    + transitivity (Σ (map (fun a : X => ⟪ a ⟫ · Σ (δA a f)) (Var e))).
      * clear;generalize (fun a : X => ⟪ a ⟫ · Σ (δA a f));intro g.
        induction (Var e);[reflexivity|].
        simpl;rewrite IHl;reflexivity.
      * transitivity (Σ (flat_map (fun a : X => map (prod ⟪ a ⟫) (δA a f)) (Var e))).
        -- clear If;induction (Var e);simpl;[reflexivity|].
           rewrite IHl,Σ_distr_l,algebra.Σ_app;reflexivity.
        -- apply KA_ACI0,Σ_equivalent;intro g.
           repeat rewrite in_flat_map.
           unfold sys_of_NFA,NFA_of_regexp;simpl.
           repeat setoid_rewrite in_flat_map||setoid_rewrite in_map_iff.
           split.
           ++ intros (a&Ia&h&<-&Ih).
              exists (⟪a⟫,h,f);split.
              ** exists (f,a,h);split;[reflexivity|].
                 exists f;split;[assumption|].
                 exists a;split;[assumption|].
                 exists h;tauto.
              ** simpl;simpl_eqX;now left.
           ++ intros (((g1&g2)&g3)&(((h1&b)&h2)&E&f'&If'&c&Ic&g'&E'&Ig')&Ig).
              inversion E;inversion E';clear E E';subst.
              revert Ig;simpl;unfold_eqX;simpl;[subst;intros [<-|F]|];try tauto.
              exists b;split;[assumption|].
              exists g2;tauto.
  Qed.

  Lemma δA_proper_KA l :
    Proper ((ax_eq KA KA') ==> (ax_eq KA KA')) (fun e => Σ (δA l e)).
  Proof.
    intros e1 e2 E;induction E.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - simpl;unfold_eqX.
      + repeat rewrite <- algebra.Σ_app.
        repeat rewrite <- Σ_distr_r.
        rewrite IHE1,IHE2,E2;reflexivity.
      + exfalso.
        apply soundness in E1;apply ϵ_spec,E1,ϵ_spec in E.
        apply N,E.
      + exfalso.
        apply soundness in E1;apply ϵ_spec,E1,ϵ_spec in E.
        apply N,E.
      + repeat rewrite app_nil_r.
        repeat rewrite <- Σ_distr_r.
        rewrite IHE1,E2;reflexivity.
    - simpl.
      repeat rewrite <- algebra.Σ_app.
      rewrite IHE1,IHE2;reflexivity.
    - simpl;repeat rewrite <- algebra.Σ_app.
      repeat rewrite <- Σ_distr_r.
      rewrite IHE,E;reflexivity.
    - destruct H;simpl;repeat rewrite <- algebra.Σ_app||rewrite <- Σ_distr_r.
      + unfold_eqX;simpl;repeat rewrite <- algebra.Σ_app||rewrite <- Σ_distr_r.
        * rewrite (ax_eq_ax _ (KA_right_distr _ _ _)).
          repeat rewrite (ax_eq_ax _ (KA_add_assoc _ _ _)).
          repeat rewrite (ax_eq_ax _ (KA_prod_assoc _ _ _)).
          reflexivity.
        * exfalso;revert E0 N;simpl.
          destruct (ϵ_zero_or_un f) as [-> | ->];[tauto|discriminate].
        * rewrite (ax_eq_ax _ (KA_right_distr _ _ _)).
          repeat rewrite (ax_eq_ax _ (KA_add_assoc _ _ _)).
          repeat rewrite (ax_eq_ax _ (KA_prod_assoc _ _ _)).
          reflexivity.
        * exfalso;revert E N;simpl.
          destruct (ϵ_zero_or_un e) as [-> | ->];[tauto|discriminate].
        * repeat rewrite right_unit.
          repeat rewrite (ax_eq_ax _ (KA_prod_assoc _ _ _));reflexivity.
      + apply ax_eq_ax;auto.
      + apply ax_eq_ax;auto.
      + unfold_eqX;repeat rewrite (ax_eq_ax _ (KA_right_distr _ _ _))
                   || rewrite (ax_eq_ax _ (KA_left_distr _ _ _))
                   || rewrite (ax_eq_ax _ (KA_add_assoc _ _ _))
                   || rewrite (ax_eq_ax _ (KA_prod_assoc _ _ _))
                   ||rewrite <- algebra.Σ_app||rewrite <- Σ_distr_r.
        * apply ax_eq_add;[|reflexivity].
          rewrite <- (ax_eq_ax _ (KA_add_assoc _ _ _)), <- (ax_eq_ax _ (KA_add_assoc _ _ _)).
          apply ax_eq_add;[reflexivity|].
          apply ax_eq_ax;auto.
        * simpl;repeat rewrite right_unit;reflexivity.
      + destruct (ϵ_zero_or_un e) as [-> | ->];destruct (ϵ_zero_or_un f) as [-> | ->];simpl_eqX;
          repeat rewrite (ax_eq_ax _ (KA_right_distr _ _ _))
          || rewrite (ax_eq_ax _ (KA_left_distr _ _ _))
          || rewrite <- (ax_eq_ax _ (KA_add_assoc _ _ _))
          ||rewrite <- algebra.Σ_app||rewrite <- Σ_distr_r
          ||(simpl;repeat rewrite right_unit);
          (apply ax_eq_add;[reflexivity|]);[|now auto |now auto|now auto].
        rewrite <- (ka_idem (Σ (δA l g))) at 1.
        rewrite (mon_assoc _ _ _),(semiring_comm (Σ (δA l f) · g) _),
        <- (mon_assoc _ _ _),(semiring_comm (Σ (δA l f) · g) _);reflexivity.
      + reflexivity.
      + simpl_eqX;reflexivity.
      + rewrite right_unit;unfold_eqX;simpl;rewrite right_unit;reflexivity.
      + simpl_eqX;reflexivity.
      + rewrite right_absorbing;unfold_eqX;simpl;rewrite right_unit;reflexivity.
      + apply ka_idem.
      + rewrite (semiring_comm (Σ (δA l e) · e⋆) _), <- (mon_assoc _ _ _),(ka_idem _).
        unfold_eqX;[|simpl;rewrite left_unit;reflexivity].
        rewrite <- Σ_distr_r,(ka_idem _);reflexivity.
    - destruct H;simpl in *;revert IHE;simpl_eqX;unfold_eqX;
        repeat rewrite <- algebra.Σ_app||rewrite <- Σ_distr_r
        ||(simpl;rewrite right_unit);intros IHE.
      + rewrite <- (ax_eq_ax _ (KA_add_assoc _ _ _)) in IHE.
        rewrite (ax_eq_ax _ (KA_idem _)) in IHE.
        cut (e⋆·f <=KA f).
        * intro L.
          rewrite <- (ax_eq_ax _ (KA_add_assoc _ _ _)).
          rewrite (ax_eq_ax _ (KA_idem _)).
          cut ((Σ(δA l e) · e ⋆) · f <=KA Σ (δA l f));[intro H;apply H|].
          rewrite <- (ax_eq_ax _ (KA_prod_assoc _ _ _)).
          rewrite L.
          apply IHE.
        * eapply ax_eq_ax';[|apply E].
          auto.
      + cut (e⋆·f <=KA f).
        * intro L.
          rewrite <- (ax_eq_ax _ (KA_add_assoc _ _ _)).
          rewrite (ax_eq_ax _ (KA_idem _)).
          cut ((Σ(δA l e) · e ⋆) · f <=KA Σ(δA l f));[intro H;apply H|].
          rewrite <- (ax_eq_ax _ (KA_prod_assoc _ _ _)).
          rewrite L.
          apply IHE.
        * eapply ax_eq_ax';[|apply E].
          auto.
      + cut (Σ(δA l e) · f ⋆ ∪ Σ(δA l f) · f ⋆ <=KA Σ(δA l e));[intro H;apply H|].
        transitivity (Σ(δA l e) · f ⋆ ∪ Σ(δA l e) · f ⋆).
        * apply proper_join_inf;[reflexivity|].
           apply proper_prod_inf;[|reflexivity].
           etransitivity;[|apply IHE].
           apply inf_cup_right.
        * rewrite (ax_eq_ax _ (KA_idem _)).
           eapply ax_eq_ax';[apply KA_star_right_ind|].
           cut (Σ(δA l e) · f <=KA Σ(δA l e));[intro H;apply H|].
           transitivity (Σ(δA l e) · f ∪ Σ(δA l f));[apply inf_cup_left|apply IHE].
      + cut (Σ(δA l e) · f ⋆ <=KA Σ(δA l e));[intro H;apply H|].
        eapply ax_eq_ax';[apply KA_star_right_ind|].
        cut (Σ(δA l e) · f <=KA Σ(δA l e));[intro H;apply H|apply IHE].
  Qed.

  Theorem CompletenessKA {A : Set} `{decidable_set A} :
    forall (e f : @regexp A), e =KA f <-> ⟦e⟧ ≃ ⟦f⟧.
  Proof. exact completenessKA.CompletenessKA. Qed.

  Corollary CompletenessKA_inf {A : Set} `{decidable_set A} :
    forall (e f : @regexp A), e <=KA f <-> ⟦e⟧ ≲ ⟦f⟧.
  Proof.
    intros e f;unfold ax_inf;rewrite CompletenessKA;simpl.
    rewrite (ka_joinOrder _ _);split;[intros ->;reflexivity|intros <-;reflexivity].
  Qed.
  
  Theorem least_solution_Antimirov e :
    least_solution (ax_inf KA KA') (sys_of_NFA (NFA_of_regexp e)) id.
  Proof.
    split.
    - apply exact_solution_is_weak_solution, Antimirov_sys.
    - intros E WS f If.
      apply CompletenessKA_inf.
      destruct (sys_of_NFA_least_solution (NFA_of_regexp e)) as (F&h1&h2&h3).
      rewrite <- (h3 E).
      + rewrite h1,<- NFA_of_regexp_langNFA;[reflexivity|].
        apply vars_Antimirov,If.
      + split.
        * intros x q I;apply CompletenessKA_inf,WS,I.
        * intros p x q I;apply CompletenessKA_inf,WS,I.
      + assumption.
  Qed.

End regexp.
  
Definition equate {A : Set} {decA : decidable_set A} (x y : A) : A -> A :=
  fun z => if z =?= y then x else z.
(** * Inclusion of two systems *)
Section inf_system.
  Context {Q1 : Set}{decQ1: decidable_set Q1 }.
  Context {Q2 : Set}{decQ2: decidable_set Q2 }.
  Context {X : Set}{decX: decidable_set X }.
  Context {jX: Join X}{pX: Product X}{zX: Zero X}{uX:Un X}{sX:Star X}.

  Definition system_homomorphism (S1 : system Q1 X) (S2 : system Q2 X) (φ : Q1 -> Q2) :=
    (forall a x, (a,x) ∈ fst S1 -> (a,φ x) ∈ fst S2) /\
    (forall a x x', (a,x,x') ∈ snd S1 -> (a,φ x,φ x') ∈ snd S2).
    
  Lemma inf_system (S1 : system Q1 X) (S2 : system Q2 X) (φ : Q1 -> Q2) :
    system_homomorphism S1 S2 φ ->
    forall leqX E, weak_solution leqX S2 E -> weak_solution leqX S1 (E∘φ).
  Proof.
    intros (hcst&hvar) leqX E (Ecst&Evar).
    split.
    - intros e x Ix.
      apply hcst,Ecst in Ix;apply Ix.
    - intros x e x' Ix.
      apply hvar,Evar in Ix;apply Ix.
  Qed.

  
End inf_system.
(** * Intersection of two systems *)
Section intersect.
  Context {Q1 : Set}{decQ1: decidable_set Q1 }.
  Context {Q2 : Set}{decQ2: decidable_set Q2 }.
  Context {X : Set}{decX: decidable_set X }.
  Context {jX: Join X}{pX: Product X}{zX: Zero X}{uX:Un X}{sX:Star X}.

  Definition intersect (S1 : system Q1 X) (S2 : system Q2 X) : system (Q1*Q2) X :=
    (flat_map (fun E => flat_map (fun F => if (fst E=?=fst F) then [(fst E,(snd E,snd F))] else [])
                              (fst S2)) (fst S1),
     flat_map (fun E => flat_map (fun F => if (fst (fst E)=?=fst (fst F))
                                     then [(fst (fst E),(snd (fst E),snd (fst F)),(snd E,snd F))]
                                     else [])
                              (snd S2)) (snd S1)).
  
  Lemma intersect_left S1 S2 : system_homomorphism (intersect S1 S2) S1 fst.
  Proof.
    split.
    - intros a (x,y) I;unfold intersect in I;simpl in I.
      apply in_flat_map in I as ((a',x')&I1&I).
      apply in_flat_map in I as ((b,y')&I2&I).
      revert I;simpl;unfold_eqX;simpl;[|tauto].
      intros [heq|F];[inversion heq;clear heq;subst|];tauto.
    - intros a (x1,y1) (x2,y2) I;unfold intersect in I;simpl in I.
      apply in_flat_map in I as (((a',x1'),x2')&I1&I).
      apply in_flat_map in I as (((b,y1'),y2')&I2&I).
      revert I;simpl;unfold_eqX;simpl;[|tauto].
      intros [heq|F];[inversion heq;clear heq;subst|];tauto.
  Qed.

  Lemma intersect_right S1 S2 : system_homomorphism (intersect S1 S2) S2 snd.
  Proof.
    split.
    - intros a (x,y) I;unfold intersect in I;simpl in I.
      apply in_flat_map in I as ((a',x')&I1&I).
      apply in_flat_map in I as ((b,y')&I2&I).
      revert I;simpl;unfold_eqX;simpl;[|tauto].
      intros [heq|F];[inversion heq;clear heq;subst|];tauto.
    - intros a (x1,y1) (x2,y2) I;unfold intersect in I;simpl in I.
      apply in_flat_map in I as (((a',x1'),x2')&I1&I).
      apply in_flat_map in I as (((b,y1'),y2')&I2&I).
      revert I;simpl;unfold_eqX;simpl;[|tauto].
      intros [heq|F];[inversion heq;clear heq;subst|];tauto.
  Qed.

  Lemma intersect_univ {Q : Set} (S : system Q X) S1 S2 ϕ1 ϕ2 :
    system_homomorphism S S1 ϕ1 -> system_homomorphism S S2 ϕ2 ->
    system_homomorphism S (intersect S1 S2) (fun q => (ϕ1 q,ϕ2 q)).
  Proof.
    intros (h1__cst&h1__var) (h2__cst&h2__var);split;unfold intersect;simpl.
    - intros a x I.
      apply in_flat_map;exists (a,ϕ1 x);split.
      + apply h1__cst,I.
      + apply in_flat_map;exists (a,ϕ2 x);split.
        * apply h2__cst,I.
        * simpl;simpl_eqX;now left.
    - intros a x y I.
      apply in_flat_map;exists (a,ϕ1 x,ϕ1 y);split.
      + apply h1__var,I.
      + apply in_flat_map;exists (a,ϕ2 x,ϕ2 y);split.
        * apply h2__var,I.
        * simpl;simpl_eqX;now left.
  Qed.
      
      
    
  
End intersect.
(* begin hide *)                        
Section simulation.
  Context {Q1 : Set}{decQ1: decidable_set Q1 }.
  Context {Q2 : Set}{decQ2: decidable_set Q2 }.
  Context {X : Set}{decX: decidable_set X }.

  Context {A : NFA Q1 X} {A' : DFA Q2 X} {stA' : list Q2}.

  Parameter A'_reachable : Reachables A' stA'.

  Definition Join : list language -> language :=
    fun L (w : list X) => exists p, p ∈ L /\ p w.

  Fixpoint explore p q n :=
    match n with
    | 0 => Some []
    | S n => if inb p (fst A) && (negb (fst (A' q)))
            then None
            else fold_right (fun Tr acc =>
                               match acc with
                               | None => None
                               | Some l =>
                                 if (fst(fst Tr))=?= p
                                 then
                                   match explore (snd Tr) (snd (A' q) (snd(fst Tr))) n with
                                   | None => None
                                   | Some l' => Some (l++l')
                                   end           
                                 else Some l
                               end)
                            (Some [(p,q)])
                            (snd A)
    end.

  Lemma explore_None p q n :
    explore p q n = None -> exists u, ⎢u⎥ < n /\ langNFA A p u /\ ~ langDFA A' q u.
  Proof.
    revert p q;induction n;simpl;[discriminate|].
    intros p q.
    case_eq (inb p (fst A) && negb (fst (A' q))).
    - rewrite andb_true_iff,inb_spec,negb_true_iff,<- not_true_iff_false.
      intros (I&N) _.
      exists [];split;[|split].
      + simpl;lia.
      + exists p;split;simpl;tauto.
      + intros h;apply N,h.
    - intros _.
      remember (snd A) as L;assert (Incl : L ⊆ snd A) by (rewrite HeqL;reflexivity);clear HeqL.
      induction L as [|((p1&x)&q1) l];simpl;[discriminate|].
      case_eq (fold_right
                 (fun (Tr : Q1 * X * Q1) (acc : option (list (Q1 * Q2))) =>
                    match acc with
                    | Some l0 =>
                      if fst (fst Tr) =?= p
                      then
                        match explore (snd Tr) (snd (A' q) (snd (fst Tr))) n with
                        | Some l' => Some (l0 ++ l')
                        | None => None
                        end
                      else Some l0
                    | None => None
                    end) (Some [(p, q)]) l).
      + intros L _.
        unfold_eqX;[|discriminate].
        case_eq (explore q1 (snd (A' q) x) n);[intros;discriminate|].
        intros I _.
        apply IHn in I as (u&Len&Iu&Nu).
        exists (x::u);split;[|split].
        * simpl;lia.
        * destruct Iu as (f&P&If).
          exists f;split;[|assumption].
          exists q1;split;[|assumption].
          apply Incl;now left.
        * intros I;apply Nu,I.
      + intros E _;apply IHl in E as (u&Len&Iu&Nu).
        * exists u;tauto.
        * intros t It;apply Incl;now right.
  Qed.

  Lemma explore_Some p q l n :
    explore p q n = Some l -> forall u, ⎢u⎥ < n -> langNFA A p u -> langDFA A' q u. 
  Proof.
    revert p q l;induction n;simpl;intros p q l E u Len (f&P&If);[lia|].
    revert E;case_eq (inb p (fst A) && negb (fst (A' q)));[discriminate|].
    rewrite <- not_true_iff_false, andb_true_iff,inb_spec,negb_true_iff.
    intros Hyp Heq.
    destruct u as [|x u].
    - rewrite <- P in *;simpl.
      unfold langDFA;simpl.
      destruct (fst (A' q));[reflexivity|exfalso;apply Hyp;split;tauto].
    - destruct P as (p2&Tr&P);simpl in Len.
      case_eq (explore p2 (snd (A' q) x) n).
      + intros L EL.
        apply (IHn p2 (snd (A' q) x) L).
        * assumption.
        * lia.
        * exists f;tauto.
      + intro N;exfalso.
        cut (fold_right
               (fun (Tr : Q1 * X * Q1) (acc : option (list (Q1 * Q2))) =>
                  match acc with
                  | Some l =>
                    if fst (fst Tr) =?= p
                    then
                      match explore (snd Tr) (snd (A' q) (snd (fst Tr))) n with
                      | Some l' => Some (l ++ l')
                      | None => None
                      end
                    else Some l
                  | None => None
                  end) (Some [(p, q)]) (snd A) = None).
        * intro E;rewrite E in Heq;discriminate.
        * revert Tr N;clear.
          induction (snd A) as [|((p'&a)&q') L];[simpl;tauto|].
          intros [E|I].
          -- inversion E;clear E;subst;simpl;simpl_eqX.
             clear;intro E.
             destruct (fold_right _ _);[rewrite E|];reflexivity.
          -- simpl;simpl_eqX.
             intros E.
             apply (IHL I) in E as ->;reflexivity.
  Qed.

  Fixpoint witness l :=
    match l with
    | [] => False
    | [(p1,q1)] => p1 ∈ (fst A) /\  fst (A' q1) = false
    | (p1,q1)::l =>
      witness l
      /\ match l with
        | (p2,q2)::_ => exists x, (p1,x,p2) ∈ snd A /\ q2 = snd (A' q1) x
        | [] => p1 ∈ (fst A) /\  fst (A' q1) = false
        end
    end.

  Lemma witness_spec p q n :
    (exists l, ⎢l⎥ = n /\ witness ((p,q)::l)) <-> (exists u, ⎢u⎥ = n /\ langNFA A p u /\ ~ langDFA A' q u).
  Proof.
    split.
    - intros (l&<-&W);revert p q W;induction l as [|(p1,q1)[|(p2,q2) l]].
      + intros p1 q1;simpl.
        intros (I1&I2);exists [];split;[|split].
        * reflexivity.
        * exists p1;split;[reflexivity|apply I1].
        * intros E;rewrite E in I2;discriminate.
      + intros p q;simpl;intros ((I1&I2)&x&Tr&->).
        exists [x];split;[|split].
        * reflexivity.
        * exists p1;split;[|assumption].
          exists p1;split;simpl;tauto.
        * unfold langDFA;simpl;rewrite I2;discriminate.
      + intros p q W.
        destruct (IHl p1 q1) as (u&Len&Iu&Nu).
        * simpl in *;tauto.
        * destruct W as (W&x&Tr&->).
          exists (x::u);split;[|split].
          -- simpl;rewrite Len;simpl;reflexivity.
          -- destruct Iu as (f&P&If).
             exists f;split;[|assumption].
             exists p1;split;tauto.
          -- intro hyp;apply Nu,hyp.
    - intros (u&<-&(f&P&If)&N).
      revert p q P N;induction u as [|x u];intros p q.
      + intros <- N;exists []; apply not_true_iff_false in N;simpl in *;tauto.
      + intros (p'&Tr&P) N.
        destruct (IHu p' (snd (A' q) x)) as (l&Len&W).
        * assumption.
        * intro e;apply N,e.
        * exists ((p',snd (A' q) x)::l).
          split;[simpl;lia|].
          destruct l as [|? l].
          -- destruct W as (W&E).
             split;[split|].
             ++ assumption.
             ++ apply E.
             ++ exists x;tauto.
          -- destruct W as (W&E).
             split;[split|].
             ++ assumption.
             ++ apply E.
             ++ exists x;tauto.
  Qed.

  Lemma witness_app l1 c l2 : witness (l1++c::l2) -> witness (c::l2).
  Proof.
    induction l1 as [|(p,q) [|x l]];simpl;tauto. Qed.

  Lemma witness_dup l1 l2 l3 p q : witness (l1++(p,q)::l2++(p,q)::l3) -> witness (l1++(p,q)::l3).
  Proof.
    induction l1 as [|(p1,q1) l1].
    - repeat rewrite app_nil_l.
      replace (cons (p,q)) with (app[(p,q)]) by reflexivity.
      rewrite <- app_ass.
      apply witness_app.
    - destruct l1 as [|(p',q')l1];intros (W&E);
      apply IHl1 in W;(split;[assumption|]);simpl in *;assumption.
  Qed.

  Lemma witness_incl p q l : witness ((p,q)::l) -> q ∈ stA' ->
                             (p,q)::l ⊆ pairs (fst A++statesNFA A) stA'.
  Proof.
    revert p q;induction l as [|(p',q') l];intros p q. 
    - simpl.
      intros (Ip&_) I.
      intros ? [<-|F];[|simpl in F;tauto].
      apply pairs_spec;split;[simpl_In;tauto|assumption].
    - intros (W&(x&Tr&->)) I.
      rewrite (IHl _ _ W).
      + intros ? [<-|I'];[|apply I'].
        apply pairs_spec.
        split;[|assumption].
        simpl_In;right;unfold statesNFA;simpl_In;right;apply in_flat_map;exists (p,x,p');simpl;tauto.
      + apply A'_reachable,I.
  Qed.

  Lemma witness_nodup p q l : witness ((p,q)::l) -> exists l', NoDup ((p,q)::l') /\ witness ((p,q)::l').
  Proof.
    revert p q;induction l as [|(p',q')l];intros p q.
    - intros E;exists [];split;[apply NoDup_cons;simpl;[tauto|apply NoDup_nil]|assumption].
    - intros (W&x&Tr&->).
      destruct (IHl _ _ W) as (l'&nd&W').
      case_in (p,q) ((p', snd (A' q) x) :: l').
      + apply in_split in I as (l1&l2&E).
        destruct l1;inversion E;clear E;subst.
        * rewrite H1 in *.
          exists l2;tauto.
        * exists l2;split.
          -- apply NoDup_cons_iff in nd as (_&nd).
             apply NoDup_app_inv in nd as (_&nd).
             apply nd.
          -- rewrite <- app_nil_l.
             apply witness_dup with (l2:=(p', snd (A' q) x) :: l1).
             split;[assumption|exists x;tauto].
      + exists((p', snd (A' q) x) :: l');split.
        * apply NoDup_cons;assumption.
        * split;[assumption|].
          exists x;tauto.
  Qed.
    
  Lemma bounded_diff p q u :
    langNFA A p u -> ~ langDFA A' q u -> q ∈ stA' ->
    (exists u, ⎢u⎥ <= ⎢fst A++statesNFA A⎥ * ⎢stA'⎥ /\ langNFA A p u /\ ~ langDFA A' q u).
  Proof.
    intros Iu Nu Iq.
    cut (exists l, ⎢l⎥ <= ⎢fst A++ statesNFA A ⎥ * ⎢ stA' ⎥  /\ witness ((p,q)::l)).
    - intros (l&Len&W).
      cut (exists u, ⎢u⎥ = ⎢l⎥ /\ langNFA A p u /\ ~ langDFA A' q u);
        [intros (v&Lv&Iv&Nv);exists v;rewrite Lv;tauto|].
      apply witness_spec;exists l;tauto.
    - cut (exists l, NoDup ((p,q)::l) /\ witness ((p, q) :: l)).
      + intros (l&nd&W).
        exists l;split;[|assumption].
        apply witness_incl in W;[|assumption].
        apply NoDup_incl_length in W;[|assumption].
        simpl in W.
        etransitivity;[|etransitivity;[apply W|]];[lia|].
        clear.
        induction (fst A++statesNFA A);simpl;[lia|].
        simpl_list.
        lia.
      + cut (exists l, ⎢l⎥ = ⎢u⎥ /\ witness ((p, q) :: l));[|apply witness_spec;exists u;tauto].
        intros (l&_&W).
        eapply witness_nodup;eauto.
  Qed.
    
  Lemma explore_spec p q :
    q ∈ stA' -> explore p q (S (⎢fst A++statesNFA A⎥ * ⎢stA'⎥)) = None
               <-> (exists u, langNFA A p u /\ ~ langDFA A' q u).
  Proof.
    intro I;split.
    - intro E; apply explore_None in E as (u&_&Iu);exists u;apply Iu.
    - intros (u&Iu&Nu).
      case_eq ( explore p q (S (⎢ fst A ++ statesNFA A ⎥ * ⎢ stA' ⎥)));[|reflexivity].
      intros l El;exfalso.
      pose proof (explore_Some El) as E.
      destruct (bounded_diff Iu Nu I) as (v&Len&Iv&Nv).
      apply Nv,E;[|assumption].
      lia.
  Qed.

End simulation.
(* end hide *)