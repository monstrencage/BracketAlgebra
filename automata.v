Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra language regexp.
Require Import Bool.

Section automata.

  Section def.
    Context {Q : Set}{decQ: decidable_set Q }.
    Context {X : Set}{decX: decidable_set X }.

    Definition NFA Q X := ((list Q) * list (Q * X * Q))%type.

    Fixpoint pathNFA (A : NFA Q X) p w q :=
      match w with
      | [] => p = q
      | a::w => exists q', (p,a,q') ∈ snd A /\ pathNFA A q' w q
      end.

    Definition langNFA A p : language :=
      fun w => exists q, pathNFA A p w q /\ q ∈ fst A.
    
    Definition DFA Q X := Q -> bool * (X -> Q).
    
    Fixpoint iter_auto (A : DFA Q X) q u :=
      match u with
      | [] => q
      | a::u => iter_auto A (snd (A q) a) u
      end.

    Definition langDFA A q : language := fun u => fst (A (iter_auto A q u)) = true.
    
    Definition Reachables (A : DFA Q X) R := forall q a, q ∈ R -> snd (A q) a ∈ R.

    Lemma Reachables_spec A R : Reachables A R <-> forall q u,  q ∈ R -> iter_auto A q u ∈ R.
    Proof.
      split.
      - intros h q u;revert q;induction u;intros q Iq;simpl;[assumption|].
        apply IHu,h,Iq.
      - intros h q a I.
        apply (h q [a]) in I;simpl in I;apply I.
    Qed.

    Definition determinise (A : NFA Q X) : DFA (list Q) X :=
      fun l => ((existsb (fun q => inb q (fst A)) l),
             (fun x => {{flat_map (fun tr => match tr with
                                     | (p,y,q)=> if inb p l && x=?=y then [q] else []
                                       end) (snd A)}})).

    Definition statesNFA (A : NFA Q X) := {{fst A ++ flat_map (fun tr => [fst (fst tr);snd tr]) (snd A)}}.

    Lemma statesNFA_spec A q :
      q ∈ statesNFA A <-> q ∈ fst A \/ exists tr, tr ∈ snd A /\ (q = fst(fst tr) \/ q = snd tr).
    Proof.
      unfold statesNFA;simpl_In.
      rewrite in_flat_map;simpl;firstorder.
    Qed.
    
    Lemma statesNFA_path A p w q : pathNFA A p w q -> w = [] \/ (p ∈ statesNFA A /\ q ∈ statesNFA A).
    Proof.
      repeat rewrite statesNFA_spec.
      intros P;cut (w = [] \/ (exists tr : Q * X * Q, tr ∈ snd A /\ (p = fst (fst tr) \/ p = snd tr)) /\
                    (exists tr : Q * X * Q, tr ∈ snd A /\ (q = fst (fst tr) \/ q = snd tr)));[tauto|].
      revert p q P;induction w as [|a w];simpl;[tauto|].
      intros p q (q'&I&IH);right.
      destruct (IHw _ _ IH) as [->|(Iq'&Iq)];clear IHw;[split;[|rewrite IH in *]|split;[|assumption]];
        eexists;(split;[eassumption|]);simpl;tauto.
    Qed.

    Lemma pathNFA_app A p u v q : pathNFA A p (u++v) q <-> exists r, pathNFA A p u r /\ pathNFA A r v q.
    Proof.
      revert p;induction u;intro p;simpl.
      - firstorder (subst;assumption).
      - setoid_rewrite IHu;clear IHu.
        firstorder.
    Qed.
    Lemma pathNFA_last A p u x q : pathNFA A p (u++[x]) q <-> exists r, pathNFA A p u r /\ (r,x,q)∈(snd A).
    Proof.
      rewrite pathNFA_app;simpl;firstorder (subst;assumption).
    Qed.

  End def.
  Context {Q : Set}{decQ: decidable_set Q }.
  Context {X : Set}{decX: decidable_set X }.
  
  Lemma determinise_lang A (q : Q) : langNFA A q ≃ langDFA (determinise A) [q].
  Proof.
    cut (forall w l q, q ∈ iter_auto (determinise A) l w <-> exists p, p ∈ l /\ pathNFA A p w q).
    - intros h w;unfold langNFA,langDFA.
      unfold determinise;simpl;rewrite existsb_exists.
      setoid_rewrite inb_spec.
      setoid_rewrite h;simpl;clear h.
      firstorder (subst;eauto).
    - clear q;intro w;induction w;intros l q;simpl.
      + firstorder (subst;eauto).
      + rewrite IHw;clear IHw.
        setoid_rewrite In_undup.
        setoid_rewrite in_flat_map;split.
        * intros (p&(((p'&x')&q')&I1&I2)&h).
          case_in p' l;simpl in *;[|tauto].
          destruct_eqX a x';simpl in *;[subst|tauto].
          destruct I2 as [<-|F];[|tauto].
          exists p';split;[assumption|].
          exists q';tauto.
        * intros (p&I&q'&I'&P).
          exists q';split;[|assumption].
          exists (p,a,q');simpl_beq.
          case_in p l;simpl in *;[tauto|].
          tauto.
  Qed.
      
  Lemma determinise_Reachables (A : NFA Q X) :
    Reachables (determinise A) (flat_map shuffles (subsets (statesNFA A))).
  Proof.
    intros L a.
    repeat rewrite all_subsets_nodup by apply NoDup_undup.
    intros (N&I);unfold determinise;simpl;split.
    - apply NoDup_undup.
    - intro q;simpl_In;rewrite in_flat_map;intros (((p&b)&q')&Tr&Iq).
      case_in p L;[|simpl in *;tauto].
      destruct_eqX a b;simpl in *;[subst|tauto].
      destruct Iq as [->|F];[|tauto].
      apply statesNFA_spec;right;eexists;split;[eassumption|].
      tauto.
  Qed.

  Definition NFA_of_regexp (e : @regexp X) : NFA regexp X :=
    ((filter (fun e => ϵ e =?= e_un) (stateSpace e)),
     flat_map (fun f =>
                 flat_map
                   (fun a =>
                      map (fun g => (f,a,g))
                          (δA a f)
                   )
                   (Var e)
              )
              (stateSpace e)).

  Lemma stateSpace_statesNFA e : statesNFA (NFA_of_regexp e) ⊆ stateSpace e.
  Proof.
    intros q;rewrite statesNFA_spec;unfold NFA_of_regexp;simpl;simpl_In.
    intros [(Iq&_)|(tr&Tr&E)];[tauto|].
    apply in_flat_map in Tr as (f&If&Tr).
    apply in_flat_map in Tr as (a&_&Tr).
    apply in_map_iff in Tr as (g&<-&Ig).
    simpl in E;destruct E as [-> | ->];[assumption|].
    eapply stateSpace_trans;[apply If|].
    apply δA_stateSpace in Ig;apply Ig.
  Qed.
    
  
  Lemma NFA_of_regexp_langNFA e f :
    f ∈ (stateSpace e) -> ⟦f⟧ ≃ langNFA (NFA_of_regexp e) f.
  Proof.
    intros If w;case_eq (inclb w (Var e)).
    - rewrite inclb_correct;intro Lw.
      cut (forall f, f ∈ stateSpace e -> ⟦ f ⟧ w <->
                                   exists g, pathNFA (NFA_of_regexp e) f w g /\ g ∈ fst (NFA_of_regexp e)).
      + intro h;apply h,If.
      + clear f If;intros f If;revert f If;induction w;intros f If;simpl.
        * setoid_rewrite filter_In.
          setoid_rewrite eqX_correct.
          setoid_rewrite ϵ_spec.
          firstorder subst;tauto.
        * rewrite Antimirov_lang.
          split.
          -- intros (g&Ig&Iw).
             apply IHw in Iw as (F&P&A).
             ++ exists F;split;[|assumption].
                exists g;split;[|assumption].
                unfold NFA_of_regexp;simpl.
                apply in_flat_map;exists f;split;[assumption|].
                apply in_flat_map;exists a;split.
                ** apply Lw;now left.
                ** apply in_map_iff;exists g;split;[reflexivity|assumption].
             ++ rewrite <- Lw;intro;simpl;tauto.
             ++ apply stateSpace_trans in If;apply If.
                apply δA_stateSpace in Ig;apply Ig.
          -- intros (g1&((g2&I1&P)&A)).
             apply in_flat_map in I1 as (h1&I1&I2).
             apply in_flat_map in I2 as (b&Ib&I2).
             apply in_map_iff in I2 as (h2&E&I2).
             inversion E;subst;clear E.
             exists g2;split;[tauto|].
             apply IHw.
             ++ rewrite <- Lw;intro;simpl;tauto.
             ++ apply stateSpace_trans in If;apply If.
                apply δA_stateSpace in I2;apply I2.
             ++ exists g1;split;[tauto|apply A].
    - rewrite <- not_true_iff_false,(inclb_correct w (Var e)).
      intro F;split.
      + intro Iw;apply Var_spec in Iw;rewrite (stateSpace_Var If) in Iw;tauto.
      + intros (g&P&_);exfalso;apply F;clear F If.
        cut (exists h, pathNFA (NFA_of_regexp e) h w g);[|exists f;assumption].
        clear f P;intros (f&P);revert g f P;induction w;intros f g P.
        * apply incl_nil.
        * destruct P as (h&Tr&P).
          apply IHw in P as ->.
          unfold NFA_of_regexp in Tr;simpl in Tr.
          apply in_flat_map in Tr as (?&_&Tr).
          apply in_flat_map in Tr as (?&I'&Tr).
          apply in_map_iff in Tr as (?&E&_);inversion E;subst.
          intros b [<-|Ib];assumption.
  Qed.

  Lemma NFA_of_regexp_spec e : ⟦e⟧ ≃ langNFA (NFA_of_regexp e) e.
  Proof. apply NFA_of_regexp_langNFA,stateSpace_refl. Qed.

  
  Lemma pathNFA_stateSpace e e' f g u :
    e' ∈ stateSpace e -> pathNFA (NFA_of_regexp e') f u g -> pathNFA (NFA_of_regexp e) f u g.
  Proof.
    intro I;revert f;induction u;intros f;simpl;[tauto|].
    intros (f'&If'&P).
    exists f';split;[|apply IHu,P].
    clear IHu P.
    pose proof I as V.
    apply stateSpace_Var in V.
    apply stateSpace_trans in I as <-.
    apply in_flat_map in If' as (?&If&I).
    rewrite V in I.
    apply in_flat_map in I as (?&Ia&I).
    apply in_map_iff in I as (?&E&If').
    inversion E;subst.
    apply in_flat_map;exists f;split;[assumption|].
    apply in_flat_map;exists a;split;[assumption|].
    apply in_map_iff;exists f';tauto.
  Qed.
    
  Fixpoint pathRestr (A : NFA Q X) states p w q :=
    match w with
    | [] => p=q
    | a::w => exists q', (w = [] \/ q' ∈ states) /\ (p,a,q') ∈ snd A /\ pathRestr A states q' w q
    end.

  Lemma pathRestr_pathNFA A p q w : pathNFA A p w q <-> pathRestr A (statesNFA A) p w q.
  Proof.
    revert p;induction w as [|a [|b w]];simpl.
    - tauto.
    - intros p;setoid_rewrite <- IHw;clear IHw.
      simpl;firstorder (subst;auto).
    - intros p;setoid_rewrite <- IHw;clear IHw.
      setoid_rewrite statesNFA_spec;firstorder.
  Qed.

  Lemma pathRestr_app A S p q r u v :
    q ∈ S -> pathRestr A S p u q -> pathRestr A S q v r -> pathRestr A S p (u++v) r.
  Proof.
    intros Iq P1 P; revert p P1;induction u as [|a[|b u]];intro p;simpl.
    - intros ->;tauto.
    - intros (p'&Ip'&Tr&E).
      pose proof E as IH;apply IHu in IH;clear IHu;subst;simpl in *.
      exists q;firstorder.
    - intros (p'&Ip'&Tr&P').
      apply IHu in P';clear IHu.
      destruct Ip' as [F|Ip'];[discriminate|].
      exists p';firstorder.
  Qed.

  Lemma pathRestr_incl A S1 S2 p q w : S1 ⊆ S2 -> pathRestr A S1 p w q -> pathRestr A S2 p w q.
  Proof.
    intros L;revert p;induction w as [|a w];intros p P.
    - apply P.
    - destruct P as (p'&Ip'&Tr&P).
      exists p';repeat split.
      + destruct Ip' as [->|Ip'].
        * left;reflexivity.
        * right;apply L,Ip'.
      + assumption.
      + apply IHw,P.
  Qed.

  Lemma pathRestr_split A S p q r u :
    pathRestr A S p u q ->
    (pathRestr A (S∖r) p u q)
    \/(exists w1 w2 w3, u = w1 ++ w2 ++ w3
                  /\ pathRestr A (S∖r) p w1 r
                  /\ pathRestr A S r w2 r
                  /\ pathRestr A (S∖r) r w3 q).
  Proof.
    revert p;induction u;intros p;simpl.
    - tauto.
    - intros (p'&Ip'&Tr&P').
      destruct Ip' as [->|Ip'].
      + rewrite P' in *;left;exists q;repeat split;tauto.
      + apply IHu in P' as [P'|(w1&w2&w3&->&P1&P2&P3)].
        * destruct_eqX p' r;subst.
          -- right;exists [a],[],u;simpl;repeat split.
             ++ exists r;tauto.
             ++ assumption.
          -- left;exists p';repeat split;try assumption.
             right;apply rm_In;split;[assumption|].
             intros ->;tauto.
        * right;destruct_eqX p' r;subst.
          -- exists [a],(w1++w2),w3;repeat split.
             ++ simpl;rewrite app_ass;reflexivity.
             ++ exists r;repeat split;tauto.
             ++ apply (pathRestr_app Ip').
                ** eapply pathRestr_incl,P1.
                   intro x;rewrite rm_In;tauto.
                ** assumption.
             ++ assumption.
          -- exists (a::w1),w2,w3;repeat split;try assumption.
             exists p';repeat split;try assumption.
             right;apply rm_In;split;[assumption|].
             intros ->;tauto.
  Qed.
      
  Lemma regexpPath (A : NFA Q X) p q : exists e, forall w, ⟦e⟧ w <-> pathNFA A p w q.
  Proof.
    setoid_rewrite pathRestr_pathNFA;revert p q.
    assert (nd: NoDup (statesNFA A)) by apply NoDup_undup.
    induction (statesNFA A) as [|q0 st];intros p q.
    - set (trans := fun p q =>
                      (if p=?=q then un else zero) 
                        ∪ Σ (map (fun tr => if fst (fst tr) =?= p && snd tr =?= q
                                         then ⟪snd(fst tr)⟫ else zero)
                                 (snd A))).
      exists (trans p q).
      intros [|a [|b w]];simpl;split.
      + destruct_eqX p q;subst;[tauto|].
        intros [F|F];exfalso.
        * apply F.
        * apply Σ_lang in F as (e&Ie&Iw).
          apply in_map_iff in Ie as (((p1,a),q1)&Ea&_).
          simpl in Ea.
          destruct_eqX p1 p;[destruct_eqX q1 q|];simpl in Ea;subst.
          -- simpl in Iw;discriminate.
          -- apply Iw.
          -- apply Iw.
      + intros ->;simpl_beq;left;reflexivity.
      + intros [F|Ia];[destruct_eqX p q;[discriminate|exfalso;apply F]|].
        apply Σ_lang in Ia as (e&Ie&Iw).
        apply in_map_iff in Ie as (((p1,b),q1)&Ea&Tr);simpl in Ea.
        destruct_eqX p1 p;[destruct_eqX q1 q|];simpl in Ea;subst.
        * inversion Iw;subst.
          exists q;tauto.
        * exfalso;apply Iw.
        * exfalso;apply Iw.
      + intros (q'&_&Tr&->).
        right;apply Σ_lang;exists ⟪a⟫;split;[|reflexivity].
        apply in_map_iff;exists (p,a,q);split;[|assumption].
        simpl;repeat simpl_beq;simpl;reflexivity.
      + intros [F|Ia];[destruct_eqX p q;[discriminate|exfalso;apply F]|exfalso].
        apply Σ_lang in Ia as (e&Ie&Iw).
        apply in_map_iff in Ie as (((p1,c),q1)&Ea&Tr);simpl in Ea.
        destruct_eqX p1 p;[destruct_eqX q1 q|];simpl in Ea;subst.
        * simpl in Iw;discriminate.
        * apply Iw.
        * apply Iw.
      + intros (q'&[F|F]&_).
        * discriminate.
        * tauto.
    - apply NoDup_cons_iff in nd as (Iq0&nd).
      destruct (IHst nd p q) as (e1&E1).
      destruct (IHst nd p q0) as (e2&E2).
      destruct (IHst nd q0 q0) as (e3&E3).
      destruct (IHst nd q0 q) as (e4&E4).
      clear IHst nd.
      exists (e1∪(e2·e3⋆·e4)).
      intros w;split.
      + intros [Iw|(w0&w3&->&(w1&w2&->&I1&I2)&I3)].
        * eapply pathRestr_incl, E1,Iw.
          intro;simpl;tauto.
        * assert (I: q0∈(q0::st)) by now left.
          repeat apply (pathRestr_app I).
          -- eapply pathRestr_incl, E2,I1.
             intro;simpl;tauto.
          -- clear E1 E2 E4 I1 I3 w1 w3 e1 e2 e4 p q.
             destruct I2 as (n&Iw).
             revert w2 Iw;induction n;intro w.
             ++ intros ->;reflexivity.
             ++ intros (w1&w2&->&I1&I2).
                apply E3 in I1;apply IHn in I2.
                apply (pathRestr_app I).
                ** eapply pathRestr_incl, I1.
                   intro;simpl;tauto.
                ** assumption.
          -- eapply pathRestr_incl, E4,I3.
             intro;simpl;tauto.
      + intro P;apply pathRestr_split with (r:= q0) in P.
        revert P;simpl;simpl_beq;simpl;rewrite rm_notin by assumption.
        intros [P|(w1&w2&w3&->&P1&P2&P3)].
        * left;apply E1;assumption. 
        * right;exists (w1++w2),w3;repeat split.
          -- rewrite app_ass;reflexivity.
          -- exists w1,w2;repeat split.
             ++ apply E2,P1.
             ++ clear w1 w3 P1 P3 p q E1 E2 E4.
                induction w2 using len_induction;simpl in *.
                ** exists 0;reflexivity.
                ** destruct P2 as (p'&h&Tr&P).
                   destruct_eqX p' q0;subst.
                   --- apply H in P as (n&P);[clear H|reflexivity].
                       exists (S n),[a],w2;repeat split;try assumption.
                       apply E3;exists q0;repeat split;try tauto.
                   --- apply pathRestr_split with (r:=q0) in P.
                       revert P;simpl;simpl_beq;simpl;rewrite rm_notin by assumption.
                       intros [P|(u1&u2&u3&->&P1&P2&P3)].
                       +++ exists 1,(a::w2),[];rewrite app_nil_r;repeat split.
                           apply E3;exists p';repeat split;try tauto.
                           destruct h as [->|[->|h]];tauto.
                       +++ assert (I: q0∈(q0::st)) by now left.
                           eapply pathRestr_incl,(pathRestr_app I P2) in P3;
                             [clear P2 I|intro;simpl;tauto].
                           apply H in P3 as (n&P3);[|repeat rewrite app_length;lia].
                           exists (S n),(a::u1),(u2++u3);repeat split;try assumption.
                           apply E3;exists p';repeat split;try assumption.
                           destruct h as [h|[->|h]];try tauto.
                           apply app_eq_nil in h as (->&_);tauto.
          -- apply E4,P3.
  Qed.

  CoInductive bissim (A: DFA Q X) : relation Q :=
  | transition p q : fst (A p) = fst (A q) -> (forall a, bissim A (snd (A p) a) (snd (A q) a)) ->
                     bissim A p q.

  Lemma bissim_lang A p q :
    bissim A p q <-> langDFA A p ≃ langDFA A q.
  Proof.
    split.
    - intros B w;revert p q B.
      induction w as [|a w].
      + intros p q B;inversion B;unfold langDFA;simpl;apply eq_iff_eq_true,H.
      + intros p q B;unfold langDFA;inversion B;simpl.
        apply IHw,H0.
    - revert p q;cofix ch;intros p q L;apply transition.
      + apply eq_true_iff_eq;apply (L []).
      + intros a;apply (ch (snd (A p) a) (snd (A q) a));intro w.
        apply (L(a::w)).
  Qed.
  
  Global Instance bissim_equiv A : Equivalence (bissim A).
  Proof.
    split;intro;setoid_rewrite bissim_lang;intros.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
  Qed.
  
End automata.

Section kleeneTheorem.
  Context {X : Set}{decX: decidable_set X }.

  Definition regular (L : @language X) := exists e, ⟦e⟧ ≃ L.
  Definition rational (L : @language X) :=
    exists Q : Set, exists d : decidable_set Q, (exists A (q : Q), langNFA A q ≃ L).

  Theorem KleeneTheorem (L : @language X) : regular L <-> rational L.
  Proof.
    split.
    - intros (e & E).
      exists (@regexp X),decidable_regexp,(NFA_of_regexp e),e.
      rewrite <- E,NFA_of_regexp_spec;reflexivity.
    - intros (Q&decQ&A&q&E).
      unfold regular;setoid_rewrite <- E;clear L E;unfold langNFA.
      induction (fst A) as [|f fn].
      + exists zero;intro w;split;intro F;exfalso.
        * apply F.
        * destruct F as (?&_&F);apply F.
      + destruct IHfn as (e&E).
        destruct (regexpPath A q f) as (e'&E').
        exists (e'∪e);intro w;split.
        * intros [I|I].
          -- apply E' in I;exists f;simpl;tauto.
          -- apply E in I as (f'&I&If');exists f';simpl;tauto.
        * intros (f'&P&[<-|If']).
          -- left;apply E',P.
          -- right;apply E;exists f';tauto.
  Qed.
End kleeneTheorem.
