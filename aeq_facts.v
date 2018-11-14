(** * RIS.aeq_facts : lemmas about α-equivalence and the equivalence transducer. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export transducer subword.
Section s.
  Context {atom X: Set}{𝐀 : Atom atom} {𝐗 : Alphabet 𝐀 X}.

  Global Instance subword_filter (A : Set) (f : A -> bool) :
    Proper (subword ==> subword) (filter f).
  Proof.
    intros u v;revert u;induction v as [|b v];intros [|a u];simpl;try tauto.
    - intros _;apply subword_nil.
    - intros [(->&I)|I];apply IHv in I.
      + destruct (f b);rewrite I;reflexivity.
      + simpl in I;rewrite I.
        destruct (f b);simpl;[|reflexivity].
        destruct (f:>v);[tauto|].
        right;reflexivity.
  Qed.

  Lemma subword_incl (A : Set) (u v : list A) : u ⊑ v -> u ⊆ v.
  Proof.
    revert u;induction v as [|b v];intros [|a u];simpl.
    - intros _;reflexivity.
    - tauto.
    - intros _;apply incl_nil.
    - intros [(<-&I)|I];apply IHv in I;rewrite I.
      + reflexivity.
      + apply incl_tl;reflexivity.
  Qed.

  Global Instance subword_map (A B: Set) (f: A->B) :
    Proper (subword ==> subword) (map f).
  Proof.
    intros u v;revert u;induction v as [|b v];intros [|a u];simpl;try tauto.
    intros [(->&I)|I];apply IHv in I;rewrite I.
    - left;split;reflexivity.
    - right;reflexivity.
  Qed.
  Global Instance subword_app (A: Set) :
    Proper (subword ==> subword ==> subword) (@app A).
  Proof.
    intros u v;revert u;induction v as [|b v];intros [|a u] I1 w1 w2 I2.
    - apply I2.
    - exfalso;apply I1.
    - rewrite app_nil_l,I2.
      etransitivity;[|apply subword_cons].
      rewrite <- app_nil_l at 1;apply IHv;[apply subword_nil|reflexivity].
    - simpl;destruct I1 as [(->&I)|I];apply (IHv _ I) in I2 as ->.
      + left;split;reflexivity.
      + right;reflexivity.
  Qed.
  
  Lemma absent_subword s a b s' : s ⊑ s' -> absent s' a b -> absent s a b.
  Proof.
    intros S (A1&A2);split;intros I.
    - eapply subword_map,subword_incl in S.
      apply A1,S,I.
    - eapply subword_map,subword_incl in S.
      apply A2,S,I.
  Qed.

  Lemma subword_dec_app (A:Set) (u v w :list A) : u ⊑ v++w -> exists u1 u2, u = u1++u2 /\ u1 ⊑ v /\ u2 ⊑ w.
  Proof.
    revert u;induction v as [|a v];intros u;simpl.
    - intros S;exists [],u;repeat split;assumption.
    - destruct u as [|b u];simpl.
      + intros _;exists [],[];repeat split;apply subword_nil.
      + intros [(->&S)|S].
        * apply IHv in S as (u1&u2&->&S1&S2).
          exists (a::u1),u2;split;[reflexivity|tauto].
        * apply IHv in S as (u1&u2&E&S1&S2).
          destruct u1 as [|x u1].
          -- simpl in *;subst.
             exists [],(b::u);simpl;tauto.
          -- inversion E;subst;clear E.
             exists (x::u1),u2;tauto.
  Qed.
  
  Lemma stack_binding_subword u v s1 s2 :
    (s1 ⊣ u | v ⤅ s2) ->
    exists s3 s4, s2 = s3++s4 /\ s4 ⊑ s1
             /\ (forall a, nb a (prj1 s4) = nb a (prj1 s1) - d_binding (𝗙 a u)
                     /\ nb a (prj1 s3) = c_binding (𝗙 a u)
                     /\ nb a (prj2 s4) = nb a (prj2 s1) - d_binding (𝗙 a v)
                     /\ nb a (prj2 s3) = c_binding (𝗙 a v)
                     /\ d_binding (𝗙 a u) - nb a (prj1 s1) = d_binding (𝗙 a v) - nb a (prj2 s1)).
  Proof.
    revert v s2;induction u as [|l u] using rev_induction;intros v' s2 P.
    - inversion P;subst;clear P.
      exists [],s2;simpl.
      split;[reflexivity|].
      split;[reflexivity|].
      intro;simpl.
      replace (d_binding (𝗙 a [])) with 0 by reflexivity;simpl_nat;tauto.
    - apply path_letter in P as (v&l'&s'&->&P&hs).
      apply IHu in P as (s3&s4&->&Sb&ha);clear IHu.
      destruct l as [a|a|x],l' as [b|b|y];unfold step in hs;try tauto.
      + subst.
        exists ((a,b)::s3),s4;simpl.
        split;[reflexivity|split;[assumption|]].
        intro c;simpl_binding.
        destruct (ha c) as (->&<-&->&<-&Ea);revert Ea;clear;intro.
        repeat split.
        * unfold_eqX;simpl;simpl_binding;lia.
        * unfold_eqX;simpl;simpl_binding;lia.
        * unfold_eqX;simpl;simpl_binding;lia.
        * unfold_eqX;simpl;simpl_binding;lia.
        * unfold_eqX;simpl;simpl_binding;lia.
      + destruct hs as ([(->&A)|(t1&t2&E&A)]&->).
        * rewrite (rmfst_absent A).
          destruct A as (A1&A2).
          rewrite map_app in A1,A2;simpl_In in *.
          apply Decidable.not_or in A1 as (e1&e2).
          apply Decidable.not_or in A2 as (e3&e4).
          rewrite nb_not_In in e1,e2,e3,e4.
          exists s3,s4;simpl.
          split;[reflexivity|split;[assumption|]].
          intro c;simpl_binding.
          pose proof (ha c) as (f1&f2&f3&f4&f5);clear ha Sb.
          repeat split.
          -- unfold_eqX;simpl;lia.
          -- unfold_eqX;simpl;simpl_binding;lia.
          -- unfold_eqX;simpl;lia.
          -- unfold_eqX;simpl;simpl_binding;lia.
          -- unfold_eqX;simpl;simpl_binding;[|lia].
             rewrite e1 in *;rewrite e2 in *;rewrite e3 in *;rewrite e4 in *.
             rewrite <- f2,<-f4.
             lia.
        * rewrite E, (rmfst_present _ A).
          levi E;subst;clear E.
          -- exists t1,t2.
             split;[reflexivity|].
             split.
             ++ clear ha A.
                destruct s1;[exfalso;apply Sb|destruct Sb as [(_&<-) | <-]].
                ** apply subword_cons.
                ** etransitivity;[|apply subword_cons].
                   apply subword_cons.
             ++ intros c;simpl_binding.
                destruct A as (A1&A2).
                rewrite nb_not_In in A1,A2.
                pose proof (ha c) as (f1&f2&f3&f4&f5);clear ha Sb.
                repeat split.
                ** revert f1;simpl;unfold_eqX;simpl.
                   --- rewrite <- f2,A1;clear;lia.
                   --- lia.
                ** simpl;unfold_eqX;simpl;simpl_binding.
                   --- rewrite <- f2,A1;clear;lia.
                   --- lia.
                ** revert f3;simpl;unfold_eqX;simpl.
                   --- rewrite <- f4,A2;clear;lia.
                   --- lia.
                ** simpl;unfold_eqX;simpl;simpl_binding.
                   --- rewrite <- f4,A2;clear;lia.
                   --- lia.
                ** revert f1 f3;simpl;unfold_eqX;simpl;subst.
                   --- rewrite A1 in *;rewrite A2 in *;clear t1 A1 A2.
                       rewrite <- f2,<-f4.
                       lia.
                   --- rewrite A1 in *.
                       rewrite <- f2.
                       lia.
                   --- rewrite A2 in *.
                       rewrite <-f4.
                       lia.
                   --- lia.
          -- inversion E1;subst;clear E1.
             exists (t1++w),s4;split;[rewrite app_ass;reflexivity|].
             split;[assumption|].
             intros c;simpl_binding.
             destruct A as (A1&A2).
             rewrite nb_not_In in A1,A2.
             pose proof (ha c) as (f1&f2&f3&f4&f5);clear ha Sb.
             rewrite map_app,filter_app,app_length in f2, f4;simpl in *.
             repeat rewrite map_app,filter_app,app_length.
             repeat split.
             ++ revert f2;simpl;simpl_binding;unfold_eqX;simpl.
                ** intros <-;rewrite A1;simpl;lia.
                ** lia.
             ++ revert f2;simpl;simpl_binding;unfold_eqX;simpl.
                ** intros <-;rewrite A1;simpl;lia.
                ** simpl_binding;lia.
             ++ revert f4;simpl;simpl_binding;unfold_eqX;simpl.
                ** intros <-;rewrite A2;simpl;lia.
                ** lia.
             ++ revert f4;simpl;simpl_binding;unfold_eqX;simpl.
                ** intros <-;rewrite A2;simpl;lia.
                ** simpl_binding;lia.
             ++ revert f2 f4;simpl;simpl_binding;unfold_eqX;simpl.
                ** rewrite A1,A2;subst;simpl.
                   intros <- <-;lia.
                ** rewrite A1;simpl;intros <-;lia.
                ** rewrite A2;simpl;intros E' <-;lia.
                ** lia.
          -- remember (a0::w) as t1;rewrite app_comm_cons,<-Heqt1 in Sb,ha;clear a0 w Heqt1.
             exists s3,(t1++t2);split;[rewrite app_ass;reflexivity|].
             split;[rewrite <- Sb;apply subword_app;
                    [reflexivity|apply subword_cons]|].
             intros c;simpl_binding.
             destruct A as (A1&A2).
             rewrite nb_not_In in A1,A2.
             pose proof (ha c) as (f1&f2&f3&f4&f5);clear ha Sb.
             simpl in f1,f3.
             rewrite map_app,filter_app,app_length in f1, f3,A1,A2;simpl in *.
             repeat rewrite map_app,filter_app,app_length.
             repeat split.
             ++ revert f1;simpl;simpl_binding;unfold_eqX;simpl.
                ** rewrite <- f2;replace (nb a (prj1 s3)) with 0 by lia;lia.
                ** lia.
             ++ revert f1;simpl;simpl_binding;unfold_eqX;simpl.
                ** lia.
                ** simpl_binding;lia.
             ++ revert f3;simpl;simpl_binding;unfold_eqX;simpl.
                ** rewrite <- f4;replace (nb b (prj2 s3)) with 0 by lia;lia.
                ** lia.
             ++ revert f3;simpl;simpl_binding;unfold_eqX;simpl.
                ** lia.
                ** simpl_binding;lia.
             ++ revert f1 f3;simpl;simpl_binding;unfold_eqX;simpl.
                ** replace (nb b (prj2 s3)) with 0 in * by lia.
                   replace (nb b (prj2 t1)) with 0 in * by lia.
                   replace (nb b (prj1 s3)) with 0 in * by lia.
                   replace (nb b (prj1 t1)) with 0 in * by lia.
                   rewrite <- f2,<-f4;revert f5;clear;lia.
                ** replace (nb b (prj2 s3)) with 0 in * by lia.
                   replace (nb b (prj2 t1)) with 0 in * by lia.
                   replace (nb a (prj1 s3)) with 0 in * by lia.
                   replace (nb a (prj1 t1)) with 0 in * by lia.
                   rewrite <- f2;revert f5;clear;lia.
                ** replace (nb b (prj2 s3)) with 0 in * by lia.
                   replace (nb b (prj2 t1)) with 0 in * by lia.
                   replace (nb a (prj1 s3)) with 0 in * by lia.
                   replace (nb a (prj1 t1)) with 0 in * by lia.
                   rewrite <- f4;revert f5;clear;lia.
                ** revert f5;clear ;lia.
      + destruct hs as (->&_).
        exists s3,s4;split;[reflexivity|split;[assumption|]].
        intro a;destruct (ha a) as (e1&e2&e3&e4&e5);clear ha Sb.
        simpl_binding;simpl_nat;tauto.
  Qed.


  Lemma exists_var_binding u a n :
    𝗙 a u = (0,true,n) -> exists u1 u2 x, u = u1++var x::u2 /\ a #α u1 /\ a ∈ ⌊x⌋.
  Proof.
    intro h;assert(Eβ: exists n,𝗙 a u = (0,true,n)) by (exists n;apply h);clear n h.
    induction u as [|l u] using rev_induction;destruct Eβ as (n&Eβ);revert Eβ;simpl_binding.
    - intro h;exfalso;discriminate.
    - destruct l as [b|b|x];simpl.
      + intro;destruct IHu as (u1&u2&x&->&F&I).
        * revert Eβ;clear;unfold_eqX;subst.
          -- destruct (𝗙 b u) as ((?&?)&?).
             unfold prod_binding;simpl.
             destruct n1;simpl;intro E;inversion E;subst.
             ++ rewrite orb_false_r in *;subst.
                eauto.
             ++ eauto.
          -- rewrite prod_unit_r;eauto.
        * exists u1,(u2++[open b]),x.
          rewrite app_ass;tauto.
      + intro;destruct IHu as (u1&u2&x&->&F&I).
        * revert Eβ;clear;unfold_eqX;subst.
          -- destruct (𝗙 b u) as ((?&?)&?).
             unfold prod_binding;simpl.
             destruct n1 as [|[]];simpl;intro E;inversion E;subst.
             ++ rewrite orb_false_r in *;subst.
                eauto.
             ++ eauto.
          -- rewrite prod_unit_r;eauto.
        * exists u1,(u2++[close b]),x.
          rewrite app_ass;tauto.
      + case_in a ⌊x⌋.
        * remember (𝗙 a u) as β;destruct β as ((?&?)&[]);unfold prod_binding;simpl.
          -- intros E;inversion E;subst;clear E H1.
             destruct b.
             ++ destruct IHu as (u1&u2&y&->&F&I').
                ** eauto.
                ** exists u1,(u2++[var x]),y;rewrite app_ass;tauto.
             ++ exists u,[],x;simpl.
                unfold fresh__α;rewrite <- Heqβ.
                tauto.
          -- intros E;inversion E;subst;clear E.
             destruct IHu as (u1&u2&y&->&F&I').
             ++ eauto.
             ++ exists u1,(u2++[var x]),y;rewrite app_ass;tauto.
        * rewrite prod_unit_r;intro E;destruct IHu as (u1&u2&y&->&F&I').
          -- eauto.
          -- exists u1,(u2++[var x]),y;rewrite app_ass;tauto.
  Qed.

  Lemma decompose_app (A:Set) (u1 u2 v : list A) :
    ⎢u1++u2⎥ = ⎢v⎥ -> exists v1 v2, ⎢u1⎥ = ⎢v1⎥ /\ v = v1++v2.
  Proof.
    intro Len;exists (firstn ⎢u1⎥ v),(skipn ⎢u1⎥ v).
    split;[|symmetry;apply firstn_skipn].
    symmetry;apply firstn_length_le.
    solve_length.
  Qed.
  Lemma scope_binding u a n :
    𝗙 a u = (0,false,S n) -> exists u1 u2, u = u1++open a::u2 /\ a #α u1 /\ a ◁ u2.
  Proof.
    intro h;assert(Eβ: exists n,𝗙 a u = (0,false,S n)) by (exists n;apply h);clear n h.
    induction u as [|l u] using rev_induction;destruct Eβ as (n&Eβ);revert Eβ;simpl_binding.
    - intro h;exfalso;discriminate.
    - destruct l as [b|b|x];simpl.
      + unfold_eqX;subst.
        * remember (𝗙 b u) as β;destruct β as ((?&?)&[]);unfold prod_binding;simpl.
          -- rewrite orb_false_r.
             intro E;inversion E;subst;clear E.
             exists u,[];split;[reflexivity|].
             split;[|reflexivity].
             symmetry;assumption.
          -- intro E;inversion E;subst;clear E.
             destruct IHu as (u1&u2&->&F&I).
             ++ eauto.
             ++ exists u1,(u2++[open b]);rewrite app_ass.
                split;[reflexivity|].
                split;[assumption|].
                unfold close_balanced;simpl_binding;rewrite I;reflexivity.
        * rewrite prod_unit_r.
          intro;destruct IHu as (u1&u2&->&F&I).
          -- eauto.
          -- exists u1,(u2++[open b]);rewrite app_ass.
             split;[reflexivity|].
             split;[assumption|].
             unfold close_balanced;simpl_binding;rewrite I;reflexivity.
      + unfold_eqX;subst.
        * remember (𝗙 b u) as β;destruct β as ((?&?)&?);unfold prod_binding;simpl.
          unfold prod_binding;simpl.
          destruct n1 as [|[]];simpl;intro E;inversion E;subst.
          destruct IHu as (u1&u2&->&F&I);[eauto|].
          exists u1,(u2++[close b]);rewrite app_ass.
          split;[reflexivity|].
          split;[assumption|].
          revert Heqβ;unfold close_balanced;simpl_binding;rewrite I;unfold_eqX;simpl.
          rewrite F,prod_unit_l.
          unfold prod_binding;simpl.
          destruct (𝗙 b u2) as ((?&?)&[]);simpl;[|reflexivity].
          destruct n0 as [|[]];simpl;discriminate.
        * rewrite prod_unit_r.
          intro;destruct IHu as (u1&u2&->&F&I).
          -- eauto.
          -- exists u1,(u2++[close b]);rewrite app_ass.
             split;[reflexivity|].
             split;[assumption|].
             unfold close_balanced;simpl_binding;rewrite I;reflexivity.
      + case_in a ⌊x⌋.
        * remember (𝗙 a u) as β;destruct β as ((?&?)&[]);unfold prod_binding;simpl.
          -- rewrite orb_true_r;discriminate.
          -- intros E;inversion E;subst;clear E.
             destruct IHu as (u1&u2&->&F&I').
             ++ eauto.
             ++ exists u1,(u2++[var x]);rewrite app_ass.
                split;[reflexivity|].
                split;[assumption|].
                unfold close_balanced;simpl_binding;rewrite I';reflexivity.
        * rewrite prod_unit_r;intro E;destruct IHu as (u1&u2&->&F&I').
          -- eauto.
          -- exists u1,(u2++[var x]);rewrite app_ass.
             split;[reflexivity|].
             split;[assumption|].
             unfold close_balanced;simpl_binding;rewrite I';reflexivity. 
  Qed.

  
  
  Lemma path_init_pair u v a b s :
    a <> b -> ([(a,b)] ⊣ u | v ⤅ s) ->
    (a ◁ u /\ b ◁ v /\ exists s', s = s'++[(a,b)])
    \/ (exists u1 u2 v1 v2,
          u = u1++close a::u2
          /\ v = v1++close b::v2
          /\ a ⋄ u1
          /\ b ⋄ v1
          /\ ⎢u1⎥ = ⎢v1⎥
          /\ exists n, 𝗙 b u1 = (0,false,n)).
  Proof.
    intros N P.
    pose proof (stack_binding_subword P) as (s1&s2&->&Sb&ha).
    destruct s2 as [|(x,y)[|? s2]].
    - right.
      clear Sb.
      destruct (ha a) as (Ea&_).
      revert Ea;simpl;simpl_beq;simpl;case_eq (d_binding (𝗙 a u));[discriminate|intros n En _].
      destruct (@αfresh_open_split _ _ _ _ u a) as (u1&u2&->&B);
        [unfold close_balanced;rewrite En;discriminate|].
      destruct (decompose_app (path_length_word P)) as (v1&v'&Len&->).
      apply path_decompose_app in P as (s2&P1&P');[|assumption].
      inversion P' as [|s3 h1 v2 h3 l h5 h6 hs P2];subst;clear P' P2.
      unfold step in hs;destruct l as [c|c|y];try tauto.
      exists u1,u2,v1,v2;cut (c = b /\ b ⋄ v1 /\ (exists n0 : nat, 𝗙 b u1 = (0, false, n0)));
        [intros (->&h);tauto|].
      clear En.
      destruct hs as ([(->&A)|(t1&t2&->&A)]&->).
      + exfalso.
        destruct (stack_binding_both P1 a) as (Ea&_).
        revert Ea;simpl.
        destruct B as (->&->);simpl;simpl_beq;simpl.
        destruct A as (A&_);apply nb_not_In in A as ->;discriminate.
      + pose proof (stack_binding_subword P1) as (s1'&s2'&E&Sb&ha').
        destruct s2' as [|(x,y)[|? s2']].
        * exfalso.
          destruct (ha' a) as (Ea&_).
          revert Ea;simpl.
          destruct B as (_&->);simpl;simpl_beq;simpl;discriminate.
        * destruct Sb as [(E'&_)|F];[|exfalso;apply F].
          inversion E';subst;clear E'.
          destruct (nil_or_last t2) as [->|(z&t2'&->)].
          -- apply app_inj_tail in E as (<-&E).
             inversion E;subst;clear E.
             split;[reflexivity|].
             cut (b ⋄ v1).
             ++ intro B';split;[assumption|].
                exists (nb b (prj1 t1)).
                pose proof (ha' b) as (E1&E2&_&_&E3).
                destruct (stack_binding_both P1 b) as (Eb&_).
                revert Eb E1 E2 E3.
                rewrite map_app,filter_app,app_length;simpl.
                remember  (𝗙 b u1)  as β.
                destruct β as ((n'&k)&m);simpl;simpl_binding.
                simpl_eqX;simpl;simpl_nat.
                intros <- _ _ ->;f_equal.
                pose proof (ha' b) as (_&_&E&_).
                revert E;simpl;simpl_beq;simpl.
                destruct (d_binding(𝗙 b v1));[|discriminate].
                simpl;intros _;f_equal.
                destruct k;[exfalso|reflexivity].
                symmetry in Heqβ.
                destruct (exists_var_binding Heqβ) as (w1&w2&x&->&F&Ia).
                destruct (decompose_app Len) as (w1'&w'&Len'&->).
                apply path_decompose_app in P1 as (s2&P1&P2);[|assumption].
                inversion P2 as [|s3 h1 w2' h3 l h5 h6 hs P3];subst;clear P2 P3.
                unfold step in hs;destruct l as [c|c|y];try tauto.
                destruct hs as (->&p&->&h).
                destruct (h b Ia) as [(Ea&A')|(r1&r2&->&A')].
                --- clear ha ha'.
                    pose proof (stack_binding_subword P1) as (s1'&s2'&E&Sb&ha).
                    destruct s2' as [|(?,?)[|? s2']].
                    +++ rewrite app_nil_r in E;subst.
                        pose proof (ha b) as (h1&h2&h3&h4&h5).
                        rewrite F in *;simpl in *;revert h1 h2 h3 h4 h5;simpl_eqX;simpl.
                        destruct A' as (A1&A2);apply nb_not_In in A1 as ->;apply nb_not_In in A2 as ->.
                        remember  (𝗙 b w1')  as β.
                        destruct β as (([|[]]&k)&m);simpl;simpl_binding;try discriminate.
                        intros _ _ _ <- _.
                        destruct B' as (B1&B2);revert B1 B2;simpl_binding.
                        rewrite <- Heqβ0;simpl;lia.
                    +++ destruct Sb as [(E'&_)|F'];[|exfalso;apply F'].
                        inversion E';subst;clear E'.
                        destruct A' as (_&A');apply A';rewrite map_app;simpl_In;simpl;tauto.
                    +++ revert Sb;clear;simpl;tauto.
                --- clear ha ha'.
                    pose proof (stack_binding_subword P1) as (s1'&s2'&E&Sb&ha).
                    destruct s2' as [|(?,?)[|? s2']].
                    +++ rewrite app_nil_r in E;subst.
                        pose proof (ha b) as (h1&h2&h3&h4&h5).
                        rewrite F in *;simpl in *;revert h1 h2 h3 h4 h5;simpl_eqX;simpl.
                        repeat rewrite map_app,filter_app,app_length;simpl;simpl_beq;simpl.
                        destruct A' as (A1&A2);apply nb_not_In in A1 as ->;discriminate.
                    +++ destruct Sb as [(E'&_)|F'];[|exfalso;apply F'].
                        inversion E';subst;clear E'.
                        destruct (nil_or_last r2) as [->|(z&r2'&->)].
                        *** apply app_inj_tail in E as (_&E);inversion E;subst;apply N;reflexivity.
                        *** rewrite app_comm_cons,<-app_ass in E.
                            apply app_inj_tail in E as (<-&->). 
                            pose proof (ha b) as (h1&h2&h3&h4&h5).
                            rewrite F in *;simpl in *;revert h1 h2 h3 h4 h5;simpl_eqX;simpl.
                            repeat rewrite map_app,filter_app,app_length;simpl;simpl_beq;simpl.
                            destruct A' as (A'&_);apply nb_not_In in A' as ->;discriminate.
                    +++ revert Sb;clear;simpl;tauto.
             ++ destruct A as (_&A);destruct (ha' b) as (_&_&E1&E2).
                split.
                --- revert A E2;clear.
                    intro A;apply nb_not_In in A as ->;lia.
                --- revert E1;clear;simpl;simpl_eqX;simpl.
                    destruct (d_binding (𝗙 b v1));lia.
          -- exfalso.
             rewrite app_comm_cons,<-app_ass in E.
             apply app_inj_tail in E as (<-&->).
             destruct (stack_binding_both P1 a) as (Ea&_).
             revert Ea;simpl.
             destruct B as (->&->);simpl;simpl_beq;simpl.
             repeat (rewrite map_app,filter_app,app_length;simpl;simpl_beq;simpl).
             destruct A as (A&_);apply nb_not_In in A as ->;lia.
        * exfalso;simpl in Sb;revert Sb;clear;tauto.
    - left.
      destruct Sb as [(E&_)|F];[inversion E;subst;clear E|exfalso;apply F].
      split;[|split;[|eauto]];unfold close_balanced.
      + destruct (ha a) as (E&_).
        revert E;simpl;simpl_eqX;simpl.
        destruct (d_binding (𝗙 a u));lia.
      + destruct (ha b) as (_&_&E&_).
        revert E;simpl;simpl_eqX;simpl.
        destruct (d_binding (𝗙 b v));lia.
    - exfalso;simpl in Sb;tauto.
  Qed.

  Lemma path_init_refl_pair u v s c :
    ([(c,c)] ⊣ u | v ⤅ s) ->
    [] ⊣ u | v ⤅ s \/ (exists s', s = s'++[(c,c)] /\ [] ⊣ u | v ⤅ s').
  Proof.
    revert s v;induction u as [|l u] using rev_induction;intros s v' P.
    - inversion P;subst.
      right;exists [];split;[reflexivity|auto].
    - apply path_letter in P as (v&l'&s'&->&P&hs).
      destruct l,l';unfold step in hs;try tauto.
      + subst;apply IHu in P as [P|(s&->&P)].
        * left;eapply path_app;[eassumption|].
          eapply pathl;[reflexivity|auto].
        * right;exists ((a,a0)::s);split;[reflexivity|].
          eapply path_app;[eassumption|].
          eapply pathl;[reflexivity|auto].
      + destruct hs as ([(->&A)|(s1&s2&->&A)]&->).
        * rewrite (rmfst_absent A).
          apply IHu in P as [P|(s&->&P)].
          -- left;eapply path_app;[eassumption|].
             eapply pathl;[split|auto].
             ++ left;tauto.
             ++ rewrite (rmfst_absent A);reflexivity.
          -- right;exists s;split;[reflexivity|].
             eapply path_app;[eassumption|].
             destruct A as (A1&A2);rewrite map_app in A1,A2;simpl_In in *;simpl in *.
             eapply pathl;[split|auto].
             ++ left;repeat split;tauto.
             ++ symmetry;apply rmfst_absent;split;tauto.
        * rewrite (rmfst_present _ A).
          apply IHu in P as [P|(s&E&P)].
          -- left;eapply path_app;[eassumption|].
             eapply pathl;[split|auto].
             ++ right;exists s1,s2;tauto.
             ++ symmetry;apply rmfst_present;assumption.
          -- destruct (nil_or_last s2) as [->|(x&s2'&->)].
             ++ apply app_inj_tail in E as (->&Es);inversion Es;subst;clear Es.
                rewrite app_nil_r.
                left;eapply path_app;[eassumption|].
                eapply pathl;[split|auto].
                ** left;tauto.
                ** rewrite (rmfst_absent A);reflexivity.
             ++ rewrite app_comm_cons,<-app_ass in E.
                apply app_inj_tail in E as (<-&->).
                right;exists (s1++s2');rewrite app_ass;split;[reflexivity|].
                eapply path_app;[eassumption|].
                eapply pathl;[split|auto].
                ** right;exists s1,s2';tauto.
                ** rewrite (rmfst_present _ A);reflexivity.
      + destruct hs as (->&hyp).
        apply IHu in P as [P|(s&->&P)].
        * left;eapply path_app;[eassumption|].
          eapply pathl;[|auto].
          split;[reflexivity|].
          apply hyp.
        * right;exists s;split;[reflexivity|].
          eapply path_app;[eassumption|].
          eapply pathl;[|auto].
          split;[reflexivity|].
          destruct hyp as (p&->&hyp);exists p;split;[reflexivity|].
          intros a Ia;pose proof (hyp a Ia) as [(E&A)|(s1&s2&E&A)].
          -- left;split;[assumption|].
             destruct A as (A1&A2);rewrite map_app in A1,A2;simpl_In in *;simpl in *.
             split;tauto.
          -- destruct (nil_or_last s2) as [->|(?&s2'&->)].
             ++ apply app_inj_tail in E as (->&Es);inversion Es;subst;clear Es.
                repeat rewrite <- H1 in *;left;split;[reflexivity|tauto].
             ++ rewrite app_comm_cons,<-app_ass in E.
                apply app_inj_tail in E as (->&<-).
                right;exists s1,s2';tauto.
  Qed.                     

  Lemma find_matching_close a u n :
    n < d_binding (𝗙 a u) -> exists u1 u2, u = u1++close a::u2 /\ d_binding (𝗙 a u1) = n /\ a ▷ u1.
  Proof.
    revert n;induction u as [|[b|b|x]u];simpl;intro n.
    - replace (d_binding (𝗙 a [])) with 0 by reflexivity; lia.
    - simpl_binding;unfold_eqX;simpl;subst.
      + case_eq (d_binding (𝗙 b u));[lia|].
        intros m E;simpl;simpl_nat;intro L.
        destruct (IHu (S n)) as (u1&u2&->&En&B).
        * lia.
        * exists (open b::u1),u2.
          split;[reflexivity|].
          unfold open_balanced; simpl_binding;simpl.
          split;[lia|].
          rewrite B,En;lia.
      + simpl_nat;intro L.
        destruct (IHu n) as (u1&u2&->&En&B).
        * lia.
        * exists (open b::u1),u2.
          split;[reflexivity|].
          unfold open_balanced; simpl_binding;simpl.
          split;[lia|].
          rewrite B;lia.
    - simpl_binding;unfold_eqX;simpl;subst.
      + simpl_nat.
        destruct n.
        * intros _;exists [],u.
          split;[reflexivity|].
          split;reflexivity.
        * intro L;destruct (IHu n) as (u1&u2&->&En&B);[lia|].
          exists (close b::u1),u2.
          split;[reflexivity|].
          unfold open_balanced; simpl_binding;simpl.
          split;[lia|].
          rewrite B;lia.
      + simpl_nat;intro L.
        destruct (IHu n) as (u1&u2&->&En&B).
        * lia.
        * exists (close b::u1),u2.
          split;[reflexivity|].
          unfold open_balanced; simpl_binding;simpl.
          split;[lia|].
          rewrite B;lia.
    -  simpl_binding;simpl;simpl_nat.
       intro L;apply IHu in L as (u1&u2&->&En&B).
       exists (var x::u1),u2.
       split;[reflexivity|].
       unfold open_balanced; simpl_binding;simpl.
       split;[lia|].
       rewrite B;lia.
  Qed. 

  Lemma subword_not_In (A:Set)(x:A) l m n : l ⊑(m++x::n) -> ~ x ∈ l -> l ⊑ m++n.
  Proof.
    revert l;induction m;intros [|y l];simpl.
    - intros _ _;apply subword_nil.
    - intros [(->&S)|S].
      + tauto.
      + tauto.
    - tauto.
    - intros [(->&S)|S] nI.
      + left;split;[reflexivity|].
        apply IHm;tauto.
      + right;apply IHm;simpl;tauto.
  Qed.
  
  Lemma aeq_first_letter_open u v a b :
    a<>b -> open a::u ≡ open b::v ->
    exists u1 u2, u = u1++close a::u2
             /\ a ⋄ u1
             /\ ((b #α u1 /\ [(a,b)]∙u1++close b::u2 ≡ v)
                \/ exists w1 w2 w3 w4, u1 = w1 ++ open b::w2
                                 /\ u2 = w3 ++ close b::w4
                                 /\ b #α w1
                                 /\ b ⋄ (w2++w3)
                                 /\ forall c, c # u ->
                                        [(a,b)]∙w1++open c::[(a,b);(b,c)]∙w2
                                               ++close b::[(b,c)]∙w3++close c::w4 ≡ v).
  Proof.
    intros N E.
    pose proof E as P;apply completeness in P as (s&P'&Ac).
    inversion P' as [|s' ? ? ? ? s2 s3 hs P];subst.
    unfold step in hs;subst.
    destruct (path_init_pair N P) as [(_&_&s'&->)|(u1&u2&v1&v2&->&->&B1&B2&Len&hN)].
    - exfalso.
      case_in (a,b) (s'++[(a,b)]).
      + rewrite Accepting_refl in Ac;apply Ac in I;tauto.
      + apply I;simpl_In;tauto.
    - exists u1,u2;split;[reflexivity|].
      split;[assumption|].
      destruct hN as ([]&hN).
      + left;split.
        * apply hN.
        * cut ( open b::[(a, b)] ∙ u1 ++ close b :: u2 ≡ open b:: v1 ++ close b :: v2).
          -- generalize ([(a, b)] ∙ u1 ++ close b :: u2).
             generalize ( v1 ++ close b :: v2).
             clear;intros v u P.
             apply completeness in P as (s&P&Ac).
             inversion P as [|s' ? ? ? ? s2 s3 hs P'];subst;clear P.
             unfold step in hs;subst.
             apply path_init_refl_pair in P' as [P|(s'&->&P)];apply completeness.
             ++ exists s;tauto.
             ++ exists s';split;[assumption|].
                rewrite map_app,map_app in Ac;simpl in Ac.
                apply app_inj_tail in Ac as (E&_);assumption.
          -- rewrite <- E.
             replace (cons(close b)) with (app[close b]) by reflexivity.
             replace (cons(close a)) with (app[close a]) by reflexivity.
             repeat rewrite app_comm_cons,<-app_ass.
             apply αequiv_app_right;simpl.
             symmetry;apply αα.
             ++ apply hN.
             ++ apply B1.
      + right.
        destruct (scope_binding  hN) as (w1&w2&->&F&B).
        rewrite app_ass in P.
        destruct (@find_matching_close b u2 (c_binding (𝗙 b w2))) as (w3&w4&->&B3&B4).
        -- destruct (decompose_app Len) as (w1'&v'&Len'&->).
           rewrite app_ass in P; apply path_decompose_app in P as (s'&P1&P);[|tauto].
           inversion P as [|? ? ? ? l ? ? hs P2];subst;clear P.
           destruct v' as [|? w2'];simpl in *;inversion H1;subst;
             [unfold step in hs;tauto|clear H1].
           destruct l0 as [c|c|x];unfold step in hs;try tauto;subst.
           apply path_decompose_app in P2 as (s''&P2&P'');[|solve_length].
           inversion P'' as [|? ? v' ? l ? ? hs P3];subst;clear P'' P' E.
           unfold step in hs.
           destruct hs as ([(->&_)|(t1&t2&->&A)]&->);[tauto|].
           rewrite (rmfst_present _ A) in P3.
           clear Len Len'.
           assert (P4:[(a,b)] ⊣ w1 ++ open b :: w2 | w1' ++ open c :: w2' ⤅  t1 ++ (a, b) :: t2)
             by (eapply path_app;[eauto|eapply pathl;[|eauto]];reflexivity).
           pose proof (stack_binding_subword P4) as (?&?&E0&S0&h0).
           destruct x0 as [|? []];[| |exfalso;revert S0;clear;simpl;tauto].
           ++ pose proof (h0 a) as (E1&E2&_).
              revert B1 E1;clear;simpl;simpl_eqX.
              intros (_&->);discriminate.
           ++ destruct (nil_or_last t2) as [->|(q&t2'&->)];[|exfalso].
              ** rewrite app_nil_r in *.
                 destruct S0 as [(->&_)|S0];[|exfalso;apply S0].
                 apply app_inj_tail in E0 as (<-&_).
                 destruct (h0 b) as (E1&E0&E3&E4&E5);clear h0.
                 revert E3 E4 E5.
                 destruct B2 as (C2&D2);rewrite C2 in *;rewrite D2 in *;simpl;simpl_eqX;simpl.
                 simpl_nat;intros _ A2 EE.
                 rewrite EE in *;clear E1 EE.
                 rewrite hN in E0;simpl in *.
                 assert (B':c_binding (𝗙 b w2) = n)
                   by (revert hN;simpl_binding;rewrite F,prod_unit_l;
                       revert B;unfold close_balanced;destruct (𝗙 b w2) as ((?&?)&?);simpl;
                       unfold d_binding;simpl;intros ->;unfold prod_binding;simpl;simpl_nat;
                       intro E;inversion E;lia).
                 pose proof (stack_binding_both P1 b) as (E4&E5).
                 revert E4 E5;simpl;simpl_eqX;simpl;rewrite F;simpl;intros E4 E5.
                 assert (N' : b<>c);[|assert (Bn : ~ b ◁ (w2++close a::u2))].
                 --- intros <-;clear P4.
                     revert C2 D2;simpl_binding;simpl.
                     case_eq (d_binding (𝗙 b w2'));simpl;[lia|intros k D2'].
                     simpl;simpl_nat.
                     intros X1 X2.
                     assert (c_binding (𝗙 b w2') = 0 /\ d_binding (𝗙 b w1') = 0
                             /\ c_binding (𝗙 b w1') = k) as (C2'&D1'&C1')
                         by lia;clear X1 X2.
                     rewrite D1',C1' in E5.
                     apply stack_binding_subword in P2 as (k1&k2&E&S2&h2).
                     destruct (nil_or_last k2) as [->|(q&k2'&->)].
                     +++ rewrite app_nil_r in *;subst.
                         destruct (h2 b) as (E&_).
                         revert E;simpl;simpl_eqX;simpl.
                         rewrite B;clear;discriminate.
                     +++ rewrite <- app_ass in E;apply app_inj_tail in E as (->&<-).
                         destruct (h2 b) as (EE1&EE2&EE3&EE4&EE5);revert A2 E0 EE1 EE2 EE3 EE4 EE5.
                         repeat rewrite map_app,filter_app,app_length;simpl;simpl_eqX;simpl.
                         rewrite B,B';simpl_nat.
                         rewrite E4,E5,C2',D2';simpl.
                         destruct k2'.
                         *** discriminate.
                         *** destruct S2 as [(->&S2)|S2].
                             ---- simpl;simpl_eqX;simpl;clear;intro FF;exfalso;revert FF;lia.
                             ---- cut (nb b (prj1 (p::k2'++[(a,b)]))=0).
                                  ++++ rewrite app_comm_cons.
                                       repeat rewrite map_app,filter_app,app_length.
                                       replace (nb b (prj1 [(a, b)])) with 0
                                         by (simpl;simpl_eqX;reflexivity).
                                       simpl_nat;intros ->;discriminate.
                                  ++++ symmetry;apply Le.le_n_0_eq;rewrite <- E4.
                                       apply subword_leq_length,subword_filter,subword_map,S2.
                 --- intro Bn.
                     assert (P5 : (b, c) :: s' ⊣ w2++close a::u2 | w2'++close b::v2 ⤅ s)
                       by (eapply path_app;[eauto|];eapply pathl;[|eauto];
                           split;[|rewrite (rmfst_present _ A),app_nil_r;reflexivity];
                           right;exists t1,[];tauto).
                     apply stack_binding_subword in P5 as (k1&k2&->&S4&h).
                     pose proof (h b) as (E1&E2&_&_&E3).
                     revert E1 E2 E3.
                     rewrite Bn;simpl;simpl_eqX;simpl.
                     destruct k2;[discriminate|].
                     destruct S4 as [(->&S4)|S4].
                     +++ exfalso;apply N';revert Ac;clear;rewrite map_app,map_app;simpl.
                         intro E;apply length_app in E as (_&E);[|solve_length].
                         inversion E;reflexivity.
                     +++ replace (nb b (prj1 (p::k2))) with 0.
                         *** discriminate.
                         *** apply Le.le_n_0_eq;rewrite <- E4.
                             apply subword_leq_length,subword_filter,subword_map,S4.
                 --- revert Bn;unfold close_balanced.
                     simpl_binding;simpl;simpl_nat.
                     rewrite B;simpl;lia.
              ** destruct S0 as [(->&_)|S0];[|exfalso;apply S0].
                 rewrite app_comm_cons,<-app_ass in E0;apply app_inj_tail in E0 as (<-&->).
                 pose proof (h0 a) as (_&E1&_).
                 revert B1 E1;clear;simpl;simpl_eqX.
                 intros (->&_).
                 rewrite map_app,filter_app,app_length;simpl;simpl_beq;simpl;lia.
        -- exists w1,w2,w3,w4.
           repeat (split;[tauto|]).
           split.
           ++ unfold balanced;simpl_binding.
              rewrite B3,B4,B;lia.
           ++ intros c Ic.
              cut ( open b::[(a, b)] ∙ w1 ++ open c::[(a,b);(b,c)]∙w2++ close b :: [(b,c)]∙w3++close c::w4 ≡ open b:: v1 ++ close b :: v2).
              ** generalize ([(a, b)] ∙ w1 ++ open c::[(a,b);(b,c)]∙w2++ close b :: [(b,c)]∙w3++close c::w4).
                 generalize (v1 ++ close b :: v2).
                 clear;intros v u P.
                 apply completeness in P as (s&P&Ac).
                 inversion P as [|s' ? ? ? ? s2 s3 hs P'];subst;clear P.
                 unfold step in hs;subst.
                 apply path_init_refl_pair in P' as [P|(s'&->&P)];apply completeness.
                 --- exists s;tauto.
                 --- exists s';split;[assumption|].
                     rewrite map_app,map_app in Ac;simpl in Ac.
                     apply app_inj_tail in Ac as (E&_);assumption.
              ** rewrite <- E.
                 repeat rewrite app_comm_cons.
                 replace (cons(close c)) with (app[close c]) by reflexivity.
                 replace (cons(close b)) with (app[close b]) by reflexivity.
                 repeat rewrite <- app_ass.
                 apply αequiv_app_right.
                 assert (a <> c /\ b <>c) as (N1&N2)
                     by (repeat rewrite support_list_app in Ic||rewrite support_list_cons in Ic;
                         simpl in Ic;simpl_In in Ic;split;intros ->;revert Ic;clear;tauto).
                 transitivity (((((open a :: w1) ++ open c :: [(b, c)] ∙ w2)
                                   ++ [close a]) ++ [(b, c)] ∙ w3) ++ [close c]).
                 --- apply αequiv_app_right.
                     apply αequiv_app_right.
                     simpl.
                     etransitivity;[|symmetry;apply αα with (b0:=b)].
                     +++ rewrite (act_lists_app _ w1 _),(act_lists_cons _ (open c) _);simpl.
                         rewrite action_compose;simpl.
                         unfold act at 4;simpl.
                         unfold act at 4;simpl.
                         simpl_eqX.
                         reflexivity.
                     +++ unfold fresh__α;simpl_binding.
                         rewrite F,prod_unit_l,prod_unit_l.
                         etransitivity;[apply 𝗙_perm|].
                         simpl;unfold act;simpl;simpl_eqX.
                         apply αfresh_support.
                         repeat rewrite support_list_app in Ic||rewrite support_list_cons in Ic.
                         simpl in Ic;simpl_In in Ic;revert Ic;clear;tauto.
                     +++ revert B1;unfold balanced;simpl_binding.
                         simpl.
                         replace (𝗙 a ([(b, c)] ∙ w2)) with (𝗙 a w2);[lia|].
                         etransitivity;[|symmetry;apply 𝗙_perm].
                         simpl;unfold act;simpl;simpl_eqX;reflexivity.
                 --- repeat rewrite app_ass.
                     apply αequiv_app_left.
                     repeat rewrite <- app_ass.
                     etransitivity;[|simpl;symmetry;apply αα with (b0:=c)].
                     +++ rewrite (act_lists_app _ w2 _),(act_lists_cons _ (close a) _);simpl.
                         unfold act at 4;simpl.
                         unfold act at 4;simpl.
                         simpl_eqX.
                         repeat rewrite app_ass;simpl;reflexivity.
                     +++ apply αfresh_support.
                         repeat rewrite support_list_app in Ic||rewrite support_list_cons in Ic.
                         rewrite (support_list_app w2),support_list_cons;simpl;simpl_In.
                         simpl in Ic;simpl_In in Ic;revert Ic;clear;tauto.
                     +++ unfold balanced;simpl_binding.
                         simpl.
                         rewrite B,B3,B4;split;lia.
  Qed.

  Lemma aeq_first_letter u v l m :
    l::u ≡ m::v -> (l=m /\ u ≡ v) \/ (exists a b, a<>b /\ l=open a /\ m=open b).
  Proof.
    intros E;apply completeness in E as (s&P&Ac).
    inversion P as [|s' ? ? ? ? ? ? hs P'];subst.
    destruct l,m;unfold step in hs;try tauto.
    - subst;destruct_eqX a a0;subst.
      + left;split;[reflexivity|].
        apply completeness.
        apply path_init_refl_pair in P' as [P'|(s'&->&P')].
        * exists s;tauto.
        * exists s';split;[tauto|].
          rewrite map_app,map_app in Ac;apply app_inj_tail in Ac;tauto.
      + right;exists a,a0;tauto.
    - left;destruct hs as ([(->&_)|(s1&s2&F&_)]&->).
      + simpl in *.
        split;[reflexivity|].
        apply completeness;exists s;tauto.
      + simpl_words.
    - left;destruct hs as (->&p&->&h).
      split;[|apply completeness;exists s;tauto].
      f_equal;symmetry;apply action_invariant,map_eq_id.
      intros a Ia.
      eapply paired_Accepting;[|apply h,Ia].
      reflexivity.
  Qed.
End s.