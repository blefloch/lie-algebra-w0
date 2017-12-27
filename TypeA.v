Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Load our files*)
Require Import Tools.
Require Import ListExtras.
Require Import Zvec.
Require Import SimpleLieAlgebras.
Require Import Data.
Require Import TypeAll.
Open Scope nat_scope.

(*TODOs for this file :
  - Perhaps use something like the following.
    Variable g : lie_algebra.
    Variable HgAtype : lie_algebra_type g = lie_A_type.
    Variable lambda : list Z.
    Variable Hrad : lie_is_radical_revwt_alg g lambda = true.
*)

Ltac tac_nth_split m lambda a l1 l2 H3 H5 H12 H13 H14 :=
  (
    simpl tl in *;
    simpl in H5;
    simpl_length in H3;
    assert (m < length lambda) as H12;
    [simpl_length ; omega |] ;
    destruct (nth_split lambda a H12) as [l1 [l2 [H13 H14]]] ;
    rewrite H13 in *
  ).

Section A123.
  Ltac show_mixed_by_ideal g lambda mu :=
    match goal with
      | [Hg : g = _ |- _]
        =>
        (right;
         refine (mixed_by_ideal g lambda mu _ _ _) ;
         [
           refine (mixed_by_hand g mu _) ;
           rewrite Hg ;
           simpl ; trivial
         |
           tac_length
         |
         rewrite Hg ;
           unfold Zvec_short_sub, lie_is_radical_revwt_alg ;
           simpl ;
           unfold Zvec_nondecb ;
           simpl_extra ;
           omega
        ])
    end.
  Ltac show_exceptional g i m :=
    match goal with
      | [Hg : g = _ |- _]
        =>
        (
          left;
          exists i, m;
          rewrite Hg;
          unfold is_exceptional_multiplier;
          split;
          [
            assert (m <? 0 = false)%Z as H4;
            [apply Z.ltb_nlt; omega|];
            rewrite H4;
            destruct (m =? 0)%Z ; firstorder
          |
            set (t := lie_radical_fundamental_revwt_alg _ _);
            compute in t;
            unfold t;
            simpl_extra ;
            firstorder
          ]
        )
    end.
  Theorem thm_main_A1 :
    forall g lambda Hn,
      g = (lie_A (exist (fun n : nat => n > 0) 1 Hn))
      -> lie_is_radical_revwt_alg g lambda = true
      -> (Is_exceptional_revwt_alg g lambda) \/ (Is_mixed_revwt_alg g lambda).
  Proof.
    intros g lambda Hn Hg H.
    rewrite Hg in H.
    unfold lie_is_radical_revwt_alg in H.
    simpl in H.
    unfold Zvec_nondecb in H.
    autorewrite with rewritesome in H.
    destruct lambda as [|a [|b [|]]] ; simpl in H ; try omega.
    simpl_extra in H.
    (*All representations of A1 are exceptional.*)
    show_exceptional g 1 b.
  Qed.
  Theorem thm_main_A2 :
    forall g lambda Hn,
      g = (lie_A (exist (fun n : nat => n > 0) 2 Hn))
      -> lie_is_radical_revwt_alg g lambda = true
      -> (Is_exceptional_revwt_alg g lambda) \/ (Is_mixed_revwt_alg g lambda).
  Proof.
    intros g lambda Hn Hg H.
    rewrite Hg in H.
    unfold lie_is_radical_revwt_alg in H.
    simpl in H.
    unfold Zvec_nondecb in H.
    simpl_extra in H.
    destruct lambda as [|a [|b [|c [|]]]] ; simpl in H ; try omega.
    simpl_extra in H.
    destruct H as [_ [[Hab Hbc] Hsum]].
    destruct (Z_le_lt_eq_dec _ _ Hab).
    - destruct (Z_le_lt_eq_dec _ _ Hbc).
      + (*a<b<c implies (a,b,c) dominates (-1,0,1), mixed "by hand"*)
        show_mixed_by_ideal g (a::b::c::nil) (-1::0::1::nil)%Z.
      + (*a<b=c implies (a,b,c) = c (-2,1,1) exceptional.*)
        show_exceptional g 2 c.
    - (*a=b<=c implies (a,b,c) = -a (-1,-1,2) exceptional.*)
      show_exceptional g 1 (-a)%Z.
  Qed.
  Theorem thm_main_A3 :
    forall g lambda Hn,
      g = (lie_A (exist (fun n : nat => n > 0) 3 Hn))
      -> lie_is_radical_revwt_alg g lambda = true
      -> (Is_exceptional_revwt_alg g lambda) \/ (Is_mixed_revwt_alg g lambda).
  Proof.
    intros g lambda Hn Hg H.
    rewrite Hg in H.
    unfold lie_is_radical_revwt_alg in H.
    simpl in H.
    unfold Zvec_nondecb in H.
    simpl_extra in H.
    destruct lambda as [|a [|b [|c [|d [|]]]]] ; simpl in H ; try omega.
    simpl_extra in H.
    destruct H as [_ [[Hab [Hbc Hcd]] Hsum]].
    destruct (Z_le_lt_eq_dec _ _ Hab).
    - (*a<b*)
      destruct (Z_le_lt_eq_dec _ _ Hcd).
      + (*a<b/\c<d implies (a,b,c,d) dominates (-1,0,0,1), mixed*)
        show_mixed_by_ideal g (a::b::c::d::nil) (-1::0::0::1::nil)%Z.
      + (*a<b/\c=d implies a<=b-2 by parity*)
        assert (a <= b - 1)%Z as Hab1. omega.
        assert (a <= b - 2)%Z as Hab2. destruct (Z_le_lt_eq_dec _ _ Hab1) ; omega.
        destruct (Z_le_lt_eq_dec _ _ Hbc).
        {
          (*a<b<c=d implies (a,b,c,d) dominates (-2,0,1,1), mixed*)
          show_mixed_by_ideal g (a::b::c::d::nil) (-2::0::1::1::nil)%Z.
        }
        {
          (*a<b=c=d implies (a,b,c,d) = b (-3,1,1,1) exceptional*)
          show_exceptional g 3 d.
        }
    - (*a=b*)
      destruct (Z_le_lt_eq_dec _ _ Hbc).
      + (*a=b<c*)
        destruct (Z_le_lt_eq_dec _ _ Hcd).
        * (*a=b<c<d implies (a,b,c,d) dominates (-1,-1,0,2), mixed*)
          show_mixed_by_ideal g (a::b::c::d::nil) (-1::-1::0::2::nil)%Z.
        * (*a=b<c=d implies (a,b,c,d)=d(-1,-1,1,1) exceptional*)
          show_exceptional g 2 d.
      + (*a=b=c<=d implies (a,b,c,d)=-a(-1,-1,-1,3) exceptional*)
        show_exceptional g 1 (-a)%Z.
  Qed.
End A123.

Section branchof.
  Fixpoint getpred (lambda mu : list Z) :=
    match lambda with
      | nil => nil
      | a :: lambda' =>
        match mu with
          | nil => nil
          | b :: mu' =>
            if (a <? b)%Z then (b - 1)%Z :: mu' else b :: getpred lambda' mu'
        end
    end.
  Fixpoint getnthpred (lambda mu : list Z) (n : nat) :=
    match n with
      | 0 => mu
      | S n' => getpred lambda (getnthpred lambda mu n')
    end.
  Definition branchof (lambda : list Z) :=
    let mu := tl (tl lambda) in
    getnthpred lambda mu (Z.abs_nat (total mu)).
  Theorem thm_A_pred_length0 :
    forall lambda0 mu0, length (getpred lambda0 mu0) <= length mu0.
  Proof.
    intros lambda0 mu0.
    generalize lambda0 as lambda1.
    induction mu0 ; destruct lambda1 as [|z lambda1] ; simpl ; firstorder.
    destruct (z <? a)%Z ; simpl ; firstorder.
  Qed.
  Theorem thm_A_pred_length1 :
    forall lambda0 mu0,
      length mu0 <= length lambda0
      -> length (getpred lambda0 mu0) = length mu0.
  Proof.
    intros lambda0 mu0.
    generalize lambda0 as lambda1.
    induction mu0 ; destruct lambda1 as [|z lambda1] ; simpl ; firstorder.
    destruct (z <? a)%Z ; simpl ; firstorder.
  Qed.
  Theorem thm_A_pred_leb :
    forall lambda mu,
      Zvec_short_allb Z.leb (getpred lambda mu) mu = true.
  Proof.
    intros lambda mu.
    generalize lambda as lambda1.
    induction mu ; destruct lambda1 ; simpl ; firstorder.
    destruct (z <? a)%Z ; simpl_extra ; firstorder.
    apply thm_Zvec_leb_refl.
  Qed.
  Theorem thm_A_pred_leb2 :
    forall lambda mu,
      Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb lambda (getpred lambda mu) = true.
  Proof.
    induction lambda.
    - simpl ; firstorder.
    - destruct mu.
      + simpl ; firstorder.
      + simpl.
        intros H.
        simpl_destruct H as [H H0].
        destruct (Z_le_lt_eq_dec _ _ H) as [H1|H1].
        * pose (H2 := H1).
          rewrite Zlt_is_lt_bool in H2.
          rewrite H2.
          rewrite H0.
          simpl_extra.
          omega.
        * rewrite H1.
          rewrite (Z.ltb_irrefl z).
          rewrite (Z.leb_refl z).
          firstorder.
  Qed.
  Theorem thm_A_pred_tot :
    forall lambda0 mu0,
      Zvec_short_allb Z.leb lambda0 mu0 = true
      -> length mu0 <= length lambda0
      -> Zvec_short_allb Z.eqb lambda0 mu0 = false
      -> total (getpred lambda0 mu0) = (total mu0 - 1)%Z.
  Proof.
    intros lambda0 mu0.
    generalize lambda0 as lambda1.
    induction mu0 ; destruct lambda1 ; simpl ;
    try (intros H1 H2 H3 ; contradiction (diff_true_false H3)).
    intros H1 H3 H4.
    simpl_destruct H1 as [H1 H2].
    destruct (Z_le_lt_eq_dec _ _ H1) as [H5|H5].
    - rewrite Zlt_is_lt_bool in H5.
      rewrite H5.
      simpl.
      omega.
    - rewrite H5.
      rewrite (Z.ltb_irrefl a).
      simpl.
      rewrite H5 in H4.
      rewrite (Z.eqb_refl a) in H4.
      simpl in H4.
      assert (forall b c, a + b = a + c - 1 <-> b = c - 1)%Z as Hsum.
      { firstorder ; omega. }
      rewrite Hsum.
      apply le_S_n in H3.
      exact (IHmu0 lambda1 H2 H3 H4).
  Qed.
  Theorem thm_A_get_hd_leb :
    (forall lambda mu n,
       lambda <> nil
       -> mu <> nil
       -> hd 0 lambda <= hd 0 mu
       -> hd 0 lambda <= hd 0 (getnthpred lambda mu n))%Z.
  Proof.
    destruct lambda, mu ; simpl ; intros ; firstorder.
    induction n.
    - simpl ; trivial.
    - simpl.
      destruct (getnthpred (z :: lambda) (z0 :: mu) n).
      + assumption.
      + simpl in IHn.
        destruct (Z_le_lt_eq_dec _ _ IHn) as [H2|H2].
        * pose (H3 := H2).
          rewrite <- Z.ltb_lt in H3.
          rewrite H3.
          simpl.
          omega.
        * rewrite <- H2.
          rewrite (Z.ltb_irrefl z).
          simpl.
          omega.
  Qed.
  Theorem thm_A_get_repeat_nil :
    forall lambda n, getnthpred lambda nil n = nil.
  Proof.
    induction n.
    - simpl ; trivial.
    - simpl. rewrite IHn.
      destruct lambda ; simpl ; firstorder.
  Qed.
  Theorem thm_A_get_repeat_leb :
    forall n lambda mu,
      Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb lambda (getnthpred lambda mu n) = true.
  Proof.
    induction n.
    - simpl ; trivial.
    - intros lambda mu H.
      simpl.
      refine (thm_A_pred_leb2 _ _ _).
      exact (IHn _ _ H).
  Qed.
  Theorem thm_branchof_leb :
    forall lambda,
      Zvec_nondecb lambda = true
      -> Zvec_short_allb Z.leb lambda (branchof lambda) = true.
  Proof.
    unfold Zvec_nondecb, branchof.
    intros lambda H.
    destruct lambda as [|a lambda].
    - simpl ; trivial.
    - simpl tl in H.
      pose (H0 := thm_Zvec_nondecb_cons a lambda H).
      simpl tl.
      refine (thm_A_get_repeat_leb _ _ _ _).
      refine (thm_Zvec_leb_trans32 _ _ _ _ H H0).
      destruct lambda ; simpl ; omega.
  Qed.
  Theorem thm_A_get_repeat_length0 :
    forall lambda mu n,
      length mu <= length lambda
      -> length (getnthpred lambda mu n) <= length lambda.
  Proof.
    intros lambda mu n H.
    induction n.
    - simpl ; trivial.
    - simpl.
      pose (H0 := thm_A_pred_length0 lambda (getnthpred lambda mu n)).
      exact (le_trans _ _ _ H0 IHn).
  Qed.
  Theorem thm_A_get_repeat_length1 :
    forall lambda mu n,
      length mu <= length lambda
      -> length (getnthpred lambda mu n) = length mu.
  Proof.
    intros lambda mu n H.
    induction n.
    - simpl ; trivial.
    - simpl.
      pose (H0 := thm_A_pred_length1 lambda (getnthpred lambda mu n)).
      rewrite IHn in H0.
      firstorder.
  Qed.
  Theorem thm_branchof_total :
    forall lambda,
      (lie_is_radical_revwt_type lie_A_type lambda) = true
      -> (total (branchof lambda) = 0)%Z.
  Proof.
    intros lambda Hrad.
    destruct lambda as [|a [|b lambda2]] ; simpl ; trivial.    
    unfold lie_is_radical_revwt_type in Hrad.
    simpl_destruct Hrad as [Hinc Htot].
    unfold branchof, tl.
    assert (total lambda2 >= 0)%Z.
    {
      pose (H := thm_Zvec_nondecb_total_app (a::b::nil) lambda2).
      unfold app in H.
      firstorder.
    }
    set (n := Z.abs_nat (total lambda2)).
    assert (Z.of_nat n = total lambda2)%Z as H0.
    {
      unfold n.
      rewrite (Zabs2Nat.id_abs (total lambda2)).
      rewrite Z.ge_le_iff in H.
      exact (Z.abs_eq _ H).
    }
    assert (forall m,
              Z.of_nat m <= total lambda2
              -> total (getnthpred (a :: b :: lambda2) lambda2 m)
                 = total lambda2 - Z.of_nat m)%Z as H1.
    {
      set (lambda := (a::b::lambda2)).
      induction m.
      - simpl ; firstorder.
      - intros H1.
        rewrite thm_Z_of_nat_S in H1.
        assert (Z.of_nat m <= total lambda2)%Z as Htmp.
        { omega. }
        pose (H2 := IHm Htmp). clearbody H2. clear Htmp IHm.
        cut (total (getnthpred lambda lambda2 (S m))
             = total (getnthpred lambda lambda2 m) - 1)%Z.
        {
          intros H4.
          rewrite H4.
          rewrite thm_Z_of_nat_S.
          omega.
        }
        assert (Zvec_short_allb
                  Z.leb lambda (getnthpred lambda lambda2 m) = true) as H3.
        {
          exact (thm_A_get_repeat_leb m lambda lambda2
                               (thm_Zvec_nondecb_fact3 a b lambda2 Hinc)).
        }
        assert (length (getnthpred lambda lambda2 m) <= length lambda) as H4.
        {
          assert (length lambda2 <= length lambda) as H5.
          { simpl. firstorder. }
          exact (thm_A_get_repeat_length0 lambda lambda2 m H5).
        }
        refine (thm_A_pred_tot lambda (getnthpred lambda lambda2 m) H3 H4 _).
        rewrite <- not_true_iff_false.
        intros H5.
        pose (H6 := thm_Zvec_leb_eqb_tot lambda (getnthpred lambda lambda2 m) H4 H3).
        rewrite H6 in H5.
        rewrite H2 in H5.
        pose (H7 := thm_Zvec_nondecb_partialsum
                      lambda (length (getnthpred lambda lambda2 m)) Hinc Htot).
        rewrite <- H5 in H7.
        omega.
    }
    pose (H2 := H1 n).
    rewrite H0 in H2.
    firstorder.
  Qed.
  Theorem thm_branchof_length :
    forall lambda,
      length (branchof lambda) = length lambda - 2.
  Proof.
    destruct lambda as [|a [|b lambda2]] ; simpl ; firstorder.
    unfold branchof, tl.
    rewrite Nat.sub_0_r.
    refine (thm_A_get_repeat_length1 (a::b::lambda2) lambda2 _ _).
    simpl.
    firstorder.
  Qed.
  Theorem thm_A_get_repeat_S :
    forall lambda mu m,
      getnthpred lambda mu (S m)
      = getpred lambda (getnthpred lambda mu m).
  Proof.
    trivial.
  Qed.
  Theorem thm_A_pred_nondecb :
    forall lambda mu,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb mu = true
      -> Zvec_nondecb (getpred lambda mu) = true.
  Proof.
    intros lambda.
    induction lambda as [|x lambda].
    - trivial.
    - destruct mu as [|z mu].
      + simpl. trivial.
      + simpl.
        destruct_bool (x <? z)%Z Hxz.
        {
          intros _.
          destruct mu as [|z0 [|z1 mu]] ; unfold Zvec_nondecb ; simpl_extra.
          - trivial.
          - omega.
          - intros Hzz.
            destruct Hzz as [Hzz0 Hzz].
            split.
            + omega.
            + assumption.
        }
        {
          intros Hlambda Hmu.
          pose (Hlambda0 := thm_Zvec_nondecb_cons _ _ Hlambda).
          pose (Hmu0 := thm_Zvec_nondecb_cons _ _ Hmu).
          generalize (IHlambda mu Hlambda0 Hmu0).
          destruct lambda as [|x0 lambda].
          - trivial.
          - destruct mu as [|z0 mu].
            + trivial.
            + simpl.
              destruct (Sumbool.sumbool_of_bool (x0 <? z0)%Z) as [Hx0z0|Hx0z0] ;
                rewrite Hx0z0.
              {
                refine (thm_Zvec_nondecb_join2 _ _ _ _).
                pose (Hxx0 := thm_Zvec_nondecb_01_geq _ _ _ Hlambda).
                rewrite <- Zlt_is_lt_bool in Hx0z0.
                rewrite Z.ltb_ge in Hxz.
                omega.
              }
              {
                refine (thm_Zvec_nondecb_join2 _ _ _ _).
                exact (thm_Zvec_nondecb_01_geq _ _ _ Hmu).
              }
        }
  Qed.
  Theorem thm_branchof_nondecb :
    forall lambda,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb (branchof lambda) = true.
  Proof.
    destruct lambda as [|a [|b lambda2]].
    - firstorder.
    - firstorder.
    - unfold branchof, tl.
      set (n := Z.abs_nat (total lambda2)).
      intros H.
      generalize n as p.
      induction p.
      + simpl.
        exact (thm_Zvec_nondecb_cons _ _ (thm_Zvec_nondecb_cons _ _ H)).
      + rewrite thm_A_get_repeat_S.
        refine (thm_A_pred_nondecb _ _ H IHp).
  Qed.
  Theorem thm_An_branching_fact1 :
    forall lambda,
      lie_is_radical_revwt_type lie_A_type lambda = true
      -> length lambda >= 2
      -> Is_known_w0_branching_A_revwt lambda (branchof lambda).
  Proof.
    intros lambda Hrad Hlength.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b, tl.
    rewrite thm_branchof_length.
    destruct lambda as [|a [|b lambda]] ; simpl in Hlength ; try omega.
    autorewrite with rewritesome.
    firstorder.
    - simpl ; rewrite Nat.sub_0_r ; trivial.
    - simpl_extra.
      firstorder.
      + refine (thm_branchof_nondecb _ _).
        unfold lie_is_radical_revwt_type in Hrad.
        autorewrite with rewritesome in Hrad.
        firstorder.
      + refine (thm_branchof_total _ Hrad).
    - refine (thm_branchof_leb (a::b::lambda) _).
      unfold lie_is_radical_revwt_type in Hrad.
      autorewrite with rewritesome in Hrad.
      firstorder.
    - unfold branchof, tl.
      set (n := Z.abs_nat (total lambda)).
      generalize n as n0.
      induction n0.
      + apply thm_Zvec_leb_refl.
      + rewrite thm_A_get_repeat_S.
        refine (thm_Zvec_leb_trans12 _ _ _ _ _ IHn0).
        * exact (thm_A_pred_length0 _ _).
        * exact (thm_A_pred_leb _ _).
  Qed.
End branchof.

Section exceptional_structure.
  Theorem thm_A_zero_exceptional :
    forall g,
      lie_algebra_type g = lie_A_type
      -> Is_exceptional_revwt_alg g (repeat 0%Z (lie_embedding_dim g)).
  Proof.
    intros g Hgtype.
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    exists 1, 0%Z.
    unfold is_exceptional_multiplier, lie_radical_fundamental_revwt_alg.
    simpl.
    rewrite thm_Zvec_mul_0.
    destruct (n <? 1) ;
      simpl_length ; firstorder.
    assert (n - 0 + 1 = 1 + n) as H0.
    { omega. }
    rewrite H0.
    simpl.
    trivial.
  Qed.
  Theorem thm_A_exceptional_repeat2 :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           Is_exceptional_revwt_alg g lambda
           -> exists a b p q,
                (a <= b)%Z /\ lambda = repeat a p ++ repeat b q.
  Proof.
    intros g Hgtype lambda [i [m [H H0]]].
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    unfold lie_radical_fundamental_revwt_alg, lie_rank, lie_embedding_dim in H0.
    unfold Zvec_mul in H0.
    destruct ((i =? 0) || (n <? i)).
    - rewrite map_repeat, Zmult_0_r in H0.
      rewrite H0.
      autorewrite with rewritelength.
      rewrite repeat_plus.
      exists 0%Z, 0%Z, 1, n.
      pose (H1 := Z.le_refl 0%Z).
      firstorder.
    - rewrite map_app, map_repeat, map_repeat in H0.
      set (a := (m * _)%Z) in H0.
      set (b := (m * _)%Z) in H0.
      set (p := S n - i) in H0.
      set (q := i) in H0.
      exists a, b, p, q.
      split.
      + unfold a, b.
        pose (H0m := thm_exceptional_multiplier_nonneg _ _ _ H).
        refine (Zmult_le_compat_l _ _ _ _ H0m).
        refine (Z_div_le _ _ _ (thm_gcd_nat1 i n) _).
        refine (Z.le_trans _ 0%Z _ _ _) ; omega.
      + assumption.
  Qed.
  Theorem thm_A_exceptional_total :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           Is_exceptional_revwt_alg g lambda
           -> total lambda = 0%Z.
  Proof.
    intros g Hgtype lambda [i [m [H H0]]].
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    rewrite H0.
    rewrite thm_total_mul.
    unfold lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank.
    destruct_bool (n <? i) Hni.
    - rewrite orb_true_r.
      simpl.
      rewrite thm_total_repeat, Zmult_0_r, Zmult_0_r.
      trivial.
    - destruct_bool (i =? 0) Hi.
      + rewrite orb_true_l.
        simpl.
        rewrite thm_total_repeat, Zmult_0_r, Zmult_0_r.
        trivial.
      + assert (forall x y : list Z, (if false || false then x else y) = y) as H1.
        { trivial. }
        rewrite H1.
        rewrite thm_total_app.
        rewrite thm_total_repeat.
        rewrite thm_total_repeat.
        rewrite Nat.ltb_ge in Hni.
        assert (i <= S n) as H2.
        { omega. }
        rewrite (Nat2Z.inj_sub (S n) i H2).
        rewrite thm_Z_of_nat_S.
        pose (Hd := thm_gcd_nat1 i n).
        set (d := Z.gcd (Z.of_nat i) (1 + Z.of_nat n)) in *.
        assert (d <> 0%Z) as Hdneq.
        { clear -Hd. omega. }
        assert (d | Z.of_nat i)%Z as [i_d Hid].
        { apply Z.gcd_divide_l. }
        assert (d | 1 + Z.of_nat n)%Z as [Sn_d HSnd].
        { apply Z.gcd_divide_r. }
        rewrite Hid, HSnd, <- Z.mul_sub_distr_r, Zopp_mult_distr_l.
        rewrite (Z.div_mul _ _ Hdneq), (Z.div_mul _ _ Hdneq).
        rewrite Z.mul_sub_distr_r, Z.mul_sub_distr_r, Z.mul_sub_distr_l.
        rewrite Z.add_sub_assoc.
        rewrite <- Zopp_mult_distr_r, <- Zopp_mult_distr_r.
        rewrite Z.mul_shuffle0, (Z.mul_comm Sn_d), Z.mul_shuffle0.
        assert (forall m n, n = 0 -> (m * n = 0))%Z as H3.
        { intros m0 n0 H7. rewrite H7, Zmult_0_r. trivial. }
        apply H3.
        omega.
  Qed.
  Theorem thm_A_exceptional_radical :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           Is_exceptional_revwt_alg g lambda
           -> lie_is_radical_revwt_type lie_A_type lambda = true.
  Proof.
    intros g Hgtype lambda Hexc.
    destruct (thm_A_exceptional_repeat2 g Hgtype lambda Hexc)
      as [a [b [p [q [Hab Hlambda]]]]].
    pose (Htot := thm_A_exceptional_total g Hgtype lambda Hexc).
    unfold lie_is_radical_revwt_type.
    rewrite Htot.
    rewrite Hlambda.
    autorewrite with rewritesome.
    rewrite thm_Zvec_nondecb_app_iff.
    repeat try split.
    - exact (thm_Zvec_nondecb_repeat a p).
    - exact (thm_Zvec_nondecb_repeat b q).
    - destruct q ; simpl ; trivial.
      rewrite last_repeat.
      destruct (p =? 0) ; omega.
  Qed.
  Theorem thm_A_exceptional_structure :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           Is_exceptional_revwt_alg g lambda
           -> lambda = repeat 0%Z (length lambda)
              \/ (exists a b p q,
                    (a < 0)%Z
                    /\ (0 < b)%Z
                    /\ 0 < p
                    /\ 0 < q
                    /\ (Z.of_nat q * b)%Z = (- (Z.of_nat p * a))%Z
                    /\ lambda = repeat a p ++ repeat b q).
  Proof.
    intros g Hgtype lambda Hexc.
    destruct (thm_A_exceptional_repeat2 g Hgtype lambda Hexc)
      as [a [b [p [q [Hab Hlambda]]]]].
    pose (Htot := thm_A_exceptional_total g Hgtype lambda Hexc).
    rewrite Hlambda, thm_total_app,
      thm_total_repeat, thm_total_repeat in Htot.
    assert (0 <= Z.of_nat p)%Z as Hp.
    { clear. omega. }
    assert (0 <= Z.of_nat q)%Z as Hq.
    { clear. omega. }
    pose (Hpapb := Zmult_le_compat_l a b (Z.of_nat p) Hab Hp).
    pose (Hqaqb := Zmult_le_compat_l a b (Z.of_nat q) Hab Hq).
    pose (Ha := Zplus_le_compat_l _ _ (Z.of_nat p * a) Hqaqb).
    pose (Hb := Zplus_le_compat_r _ _ (Z.of_nat q * b) Hpapb).
    rewrite Htot, <- Z.mul_add_distr_r in Ha, Hb.
    assert (
        ((a < 0)%Z /\ (0 < b)%Z /\ 0 < p /\ 0 < q)
        \/ (lambda = repeat 0 (p + q))%Z) as H.
    {
      destruct (Z_le_lt_eq_dec _ _ Hp) as [H0ltp|H0].
      destruct (Z_le_lt_eq_dec _ _ Hq) as [H0ltq|H0].
      all : try (rewrite thm_0_eq_Z_of_nat in H0 ;
                 rewrite <- H0 in * ;
                 right ;
                 simpl in * ;
                 try rewrite Nat.add_0_r, Z.add_0_r, app_nil_r in *).
      all : try (rewrite (thm_repeat_mul_0 _ _ Htot) in Hlambda ; assumption).
      assert (0 < Z.of_nat p + Z.of_nat q)%Z as H0ltpq.
      { clear -H0ltp H0ltq. omega. }
      rewrite (thm_mul_nonpos_cancel_l  _ a H0ltpq) in Ha.
      rewrite (Z.mul_nonneg_cancel_l _ b H0ltpq) in Hb.
      destruct (Z_le_lt_eq_dec _ _ Ha) as [Halt0|Ha0].
      destruct (Z_le_lt_eq_dec _ _ Hb) as [H0ltb|H0b].
      rewrite thm_0_lt_Z_of_nat in *.
      left ; repeat (try split ; try assumption).
      all : try rewrite <- H0b in *.
      all : try rewrite Ha0 in *.
      all : rewrite Z.mul_0_r in Htot.
      all : try rewrite Z.add_0_l in Htot.
      all : try rewrite Z.add_0_r in Htot.
      all : rewrite (thm_repeat_mul_0 _ _ Htot), <- repeat_plus in Hlambda.
      all : right ; assumption.
    }
    destruct H as [[H1 [H2 [H3 H4]]]|H].
    - right.
      exists a, b, p, q.
      repeat try split ; try assumption.
      clear -Htot. omega.
    - left.
      rewrite H.
      autorewrite with rewritelength.
      trivial.
  Qed.
End exceptional_structure.

Section exceptional_from_bounds.
  Theorem thm_A_exceptional_from_bounds1 :
    forall g lambda a,
      lie_algebra_type g = lie_A_type
      -> lie_is_radical_revwt_type lie_A_type lambda = true
      -> length lambda = lie_embedding_dim g
      -> (a < 0)%Z
      -> nth 0 lambda a = a
      -> a = nth (length lambda - 2) lambda a
      -> Is_exceptional_revwt_alg g lambda.
  Proof.
    intros g lambda a Hgtype Hrad Hlength Ha Hnth0 Hnth1.
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    unfold lie_is_radical_revwt_type in Hrad.
    simpl_destruct Hrad as [Hinc Htot].
    simpl in Hlength.
    exists 1, (-a)%Z.
    unfold is_exceptional_multiplier, lie_radical_fundamental_revwt_alg.
    unfold lie_rank, lie_embedding_dim, plus.
    assert (((1 =? 0) || (n <? 1)) = false) as H0.
    { simpl. rewrite Nat.ltb_nlt. omega. }
    rewrite H0.
    split.
    + clear - Ha Hn.
      assert (~(-a < 0)%Z) as Ha1 ; [omega|].
      assert (~(-a = 0)%Z) as Ha2 ; [omega|].
      rewrite <- Z.ltb_nlt in Ha1.
      rewrite <- Z.eqb_neq in Ha2.
      rewrite Ha1, Ha2.
      rewrite orb_true_r, orb_true_l.
      trivial.
    + rewrite <- thm_Z_of_nat_S.
      set (t := Z.gcd _ _) in * ; compute in t ; unfold t in * ; clear t.
      rewrite Zdiv_1_r, Zdiv_1_r, thm_S_minus_1.
      unfold Zvec_mul.
      rewrite map_app, map_repeat.
      rewrite Z.mul_opp_comm.
      set (t := (- - Z.of_nat 1)%Z) in * ; compute in t ; unfold t in * ; clear t.
      rewrite Z.mul_1_r.
      unfold repeat at 2, map.
      assert (n <= length lambda) as Hlength2.
      { clear - Hlength. omega. }
      assert (firstn n lambda = repeat a n) as Hhd.
      {
        assert (hd a (firstn n lambda) = a) as Hfirstnhd.
        {
          rewrite hd_firstn, <- nth_0.
          destruct n ; [clear -Hn ; omega|assumption].
        }
        assert (a = last (firstn n lambda) a) as Hfirstnlast.
        {
          rewrite Hlength, Nat.sub_succ in Hnth1.
          rewrite last_firstn ; [|assumption].
          destruct n ; [trivial|assumption].
        }
        rewrite (thm_Zvec_nondecb_hd_last_eq
                   _ _ (thm_Zvec_nondecb_firstn n lambda Hinc) Hfirstnhd Hfirstnlast).
        simpl_length.
        rewrite (min_l _ _ Hlength2).
        trivial.
      }
      pose (Hlambdaval := eq_sym (firstn_skipn n lambda)).
      rewrite Hhd in Hlambdaval.
      assert (length (skipn n lambda) = 1) as Hlength3.
      { simpl_length. omega. }
      destruct (skipn n lambda) as [|x [|]] ;
        try (clear -Hlength3 ; simpl in *; omega).
      simpl in *.
      assert (x = -a * Z.of_nat n)%Z as Hx.
      {
        rewrite Hlambdaval in Htot.
        simpl_total in Htot.
        clear -Htot.
        rewrite <- Zopp_mult_distr_l, Z.mul_comm.
        omega.
      }
      rewrite <- Hx, <- Hlambdaval.
      trivial.
  Qed.
  Theorem thm_A_exceptional_from_bounds2 :
    forall g lambda b,
      lie_algebra_type g = lie_A_type
      -> lie_is_radical_revwt_type lie_A_type lambda = true
      -> length lambda = lie_embedding_dim g
      -> (0 < b)%Z
      -> nth 1 lambda b = b
      -> b = nth (length lambda - 1) lambda b
      -> Is_exceptional_revwt_alg g lambda.
  Proof.
    intros g lambda b Hgtype Hrad Hlength Hb Hnth0 Hnth1.
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    unfold lie_is_radical_revwt_type in Hrad.
    simpl_destruct Hrad as [Hinc Htot].
    simpl in Hlength.
    exists n, b.
    unfold is_exceptional_multiplier, lie_radical_fundamental_revwt_alg.
    unfold lie_rank, lie_embedding_dim, plus.
    assert (((n =? 0) || (n <? n)) = false) as H0.
    {
      rewrite (Nat.ltb_irrefl n).
      destruct n ; firstorder ; omega.
    }
    rewrite H0.
    split.
    + clear - Hb Hn.
      assert (~(b < 0)%Z) as Ha1 ; [omega|].
      assert (~(b = 0)%Z) as Ha2 ; [omega|].
      rewrite <- Z.ltb_nlt in Ha1.
      rewrite <- Z.eqb_neq in Ha2.
      rewrite Ha1, Ha2, (Nat.eqb_refl n), orb_true_r.
      trivial.
    + rewrite Z.gcd_add_diag_r, Z.gcd_1_r, Z.div_1_r, Z.div_1_r.
      assert (S n - n = 1) as H1.
      { omega. }
      rewrite H1.
      simpl.
      unfold Zvec_mul.
      rewrite map_repeat, Z.mul_1_r.
      rewrite nth_last in Hnth1.
      destruct lambda as [|x lambda] ; [clear -Hlength ; simpl in * ; omega |].
      simpl_extra.
      simpl_extra in Hlength.
      assert (lambda = repeat b n) as Hval.
      {
        rewrite <- Hlength.
        refine (thm_Zvec_nondecb_hd_last_eq _ _ _ _ _).
        - exact (thm_Zvec_nondecb_cons _ _ Hinc).
        - simpl in Hnth0.
          rewrite nth_0 in Hnth0.
          assumption.
        - destruct lambda.
          + trivial.
          + simpl in *.
            assumption.
      }
      firstorder.
      rewrite Hval in Htot.
      simpl_total in Htot.
      rewrite Z.mul_comm, <- Zopp_mult_distr_l.
      omega.
  Qed.
End exceptional_from_bounds.

Section repeat2_branching.
  Theorem thm_repeat2_ntha :
    forall a b p q k lambda,
      2 <= k
      -> k < p
      -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
      -> nth k lambda a = a.
  Proof.
    intros a b p q k lambda Hk H H0.
    destruct k as [|[|k]] ; simpl; try omega.
    unfold Is_known_w0_branching_A_revwt,
      radical_branching_A_two_revwt_b, lie_is_radical_revwt_type in H0.
    autorewrite with rewritesome in H0.
    firstorder.
    destruct lambda as [|l0 [|l1 lambda]] ; simpl; trivial.
    destruct p as [|[|p]] ; simpl; try (clear -H ; omega).
    unfold repeat2 in H1.
    simpl tl in H1.
    assert (S (S p) = p + 2) as H7.
    { omega. }
    rewrite H7, repeat_plus, <- app_assoc in H1.
    simpl_extra in H2.
    firstorder.
    simpl in H0.
    autorewrite with rewritelength rewritesome in H0.
    generalize H1, H9.
    rewrite <- (firstn_skipn p lambda).
    set (lam1 := firstn p lambda).
    set (lam2 := skipn p lambda).
    assert (length lam1 = length (repeat a p)) as H14.
    {
      unfold lam1.
      autorewrite with rewritelength.
      clear -H0.
      simpl_length in H0.
      apply min_l.
      omega.
    }
    rewrite thm_Zvec_leb_app, thm_Zvec_leb_app ; firstorder.
    rewrite (thm_Zvec_leb_irrefl _ _ H14 H11 H10).
    rewrite app_nth1.
    - generalize k, p, a.
      induction k0 ; destruct p0 ; simpl ; trivial.
    - autorewrite with rewritelength.
      apply lt_S_n, lt_S_n in H.
      assumption.
  Qed.
  (*Revise the proof of thm_repeat2_ntha to look more like thm_repeat2_nthb.*)
  Theorem thm_repeat2_nthb :
    forall a b p q k lambda,
      2 + p <= k
      -> k < p + q
      -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
      -> nth k lambda b = b.
  Proof.
    unfold repeat2.
    intros.
    unfold Is_known_w0_branching_A_revwt,
      radical_branching_A_two_revwt_b, lie_is_radical_revwt_type in *.
    autorewrite with rewritesome in *.
    firstorder.
    assert (k - 2 < length (repeat a p ++ repeat b q)
            /\ k - 2 < length (tl (tl lambda))
            /\ k < length lambda
            /\ k < length (repeat a p ++ repeat b q))
      as [H8 [H9 [H10 H11]]].
    { autorewrite with rewritelength in *. omega. }
    pose (Hlower := thm_Zvec_leb_nth (k - 2) _ _ b b H8 H9 H2).
    pose (Hupper := thm_Zvec_leb_nth k _ _ b b H10 H11 H3).
    rewrite nth_tl_tl, nth_app_repeat2 in *.
    exact (Z.le_antisymm _ _ Hupper Hlower).
    all : clear -H H0 ; omega.
  Qed.
  Theorem thm_repeat2_nthc :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> 0 < p
      -> 0 < q
      -> 1 < p \/ 1 < q
      -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
      -> (nth 0 lambda a <= a
          /\ a <= nth (1 + p) lambda a
          /\ nth p lambda b <= b
          /\ b <= nth (1 + p + q) lambda b)%Z.
  Proof.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b.
    intros a b p q lambda Ha Hb Hp Hq Hpq Hbranch.
    simpl_destruct Hbranch as [[[[Hlength [Hincl _]] _] Hlm] Hml].
    repeat (destruct p ; [omega|]) ; repeat (destruct q ; [omega|]).
    repeat split.
    - destruct lambda.
      + firstorder.
      + clear -Hlm.
        simpl.
        simpl_extra in Hlm.
        firstorder.
    - simpl.
      destruct lambda as [|z [|z0 lambda]].
      + firstorder.
      + firstorder.
      + simpl.
        simpl tl in *.
        tac_nth_split p lambda a l1 l2 Hlength Ha H12 H13 H14.
        unfold repeat2 in Hml.
        rewrite repeat_S_app, thm_Zvec_leb_app in Hml ; [|tac_length].
        simpl_destruct Hml as [_ [H _]].
        rewrite <- H13.
        assumption.
    - tac_nth_split (S p) lambda b l1 l2 Hlength Ha H12 H13 H14.
      unfold repeat2 in Hlm.
      rewrite thm_Zvec_leb_app in Hlm ; [|tac_length].
      simpl_destruct Hlm as [_ [H _]].
      rewrite <- H13.
      assumption.
    - simpl.
      destruct lambda as [|z [|z0 lambda]].
      + firstorder.
      + firstorder.
      + simpl.
        simpl tl in *.
        tac_nth_split (p + S q) lambda b l1 l2 Hlength Ha H12 H13 H14.
        unfold repeat2 in Hml.
        rewrite <- (Nat.add_1_r q) in Hml at 1.
        rewrite repeat_plus, app_assoc, thm_Zvec_leb_app in Hml ; [|tac_length].
        simpl_destruct Hml as [_ H].
        rewrite <- H13.
        assumption.
  Qed.
  Theorem thm_repeat2_branching : (*Probably useless*)
    forall lambda a b p q,
      2 <= p
      -> 2 <= q
      -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
      -> exists l0 l1 l2 l3 l4 l5,
           lambda = l0::l1::(repeat a (p - 2))
                      ++ l2::l3::(repeat b (q - 2))
                      ++ l4::l5::nil.
  Proof.
    intros lambda a b p q Hp Hq H.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b in H.
    autorewrite with rewritesome in H.
    destruct H as [[[[Hlength Hradl] Hradm] Hlm] Hml].
    unfold repeat2 in Hlength.
    autorewrite with rewritelength in Hlength.
    assert (length lambda >= 6) as Hlength2.
    {
      rewrite Hlength.
      clear - Hp Hq Hlength. omega.
    }
    destruct lambda as [|l0 [|l1 lambda]] ; simpl in Hlength2 ; try omega.
    autorewrite with rewritelength rewritesome in Hlength.
    exists l0, l1.
    unfold repeat2 in Hlm, Hml.
    assert (p = 2 + (p - 2)) as Hp2.
    { clear -Hp. omega. }
    assert (p = (p - 2) + 2) as Hp3.
    { clear -Hp. omega. }
    rewrite Hp2 in Hlm.
    rewrite Hp3 in Hml.
    rewrite repeat_plus in Hlm, Hml.
    rewrite <- app_assoc in Hml.
    simpl_destruct Hlm as [_ [_ Hlm]].
    assert ((p - 2) <= length lambda) as Hp4.
    { clear -Hq Hlength. omega. }
    pose (Hlsplit := eq_sym (firstn_skipn (p - 2) lambda)).
    set (mu := firstn _ _) in *.
    set (nu := skipn _ _) in *.
    rewrite Hlsplit in *.
    assert (length mu = length (repeat a (p - 2))) as Hmulength.
    {
      unfold mu.
      autorewrite with rewritelength.
      rewrite Hlsplit.
      exact (Min.min_l _ _ Hp4).
    }
    rewrite (thm_Zvec_leb_app _ _ _ _ Hmulength) in Hlm.
    destruct Hlm as [Hlm1 Hlm2].
    simpl in Hml.
    rewrite (thm_Zvec_leb_app _ _ _ _ (eq_sym Hmulength)) in Hml.
    destruct Hml as [Hml1 Hml2].
    pose (Hmu := thm_Zvec_leb_irrefl _ _ Hmulength Hlm1 Hml1).
    clearbody Hmu.
    rewrite Hmu in *.
    simpl_length in Hlength.
    clearbody nu.
    clear Hlm1 Hml1 Hmulength mu Hmu Hp4 Hlsplit lambda.
    assert (length nu >= 2) as Hnu2.
    { omega. }
    destruct nu as [|l2 [|l3 nu]] ; simpl in Hnu2 ; try omega.
    clear Hnu2.
    exists l2, l3.
    assert (q = 2 + (q - 2)) as Hq2.
    { clear -Hq. omega. }
    assert (q = (q - 2) + 2) as Hq3.
    { clear -Hq. omega. }
    rewrite Hq2 in Hlm2.
    rewrite Hq3 in Hml2.
    rewrite repeat_plus in Hlm2, Hml2.
    simpl_destruct Hlm2 as [_ [_ Hlm2]].
    simpl_destruct Hml2 as [_ [_ Hml2]].
    simpl in Hlength.
    assert (q - 2 <= length nu) as Hq4.
    { clear - Hp Hq Hlength. omega. }
    pose (Hnsplit := eq_sym (firstn_skipn (q - 2) nu)).
    set (rho := firstn _ _) in *.
    set (sigma := skipn _ _) in *.
    rewrite Hnsplit in *.
    assert (length rho = length (repeat b (q - 2))) as Hrholength.
    {
      unfold rho.
      autorewrite with rewritelength.
      rewrite Hnsplit.
      exact (Min.min_l _ _ Hq4).
    }
    rewrite <- (app_nil_r (repeat b (q - 2))) in Hlm2.
    rewrite (thm_Zvec_leb_app _ _ _ _ Hrholength) in Hlm2.
    destruct Hlm2 as [Hlm1 Hlm2].
    rewrite (thm_Zvec_leb_app _ _ _ _ (eq_sym Hrholength)) in Hml2.
    destruct Hml2 as [Hml1 Hml2].
    pose (Hrho := thm_Zvec_leb_irrefl _ _ Hrholength Hlm1 Hml1).
    clearbody Hrho.
    rewrite Hrho in *.
    simpl_length in Hlength.
    simpl_length in Hlength2.
    clearbody sigma.
    clear Hlm1 Hml1 Hrholength rho Hrho Hq4 Hnsplit nu.
    assert (length sigma = 2) as Hsigma2.
    { clear - Hp Hq Hlength. omega. }
    destruct sigma as [|l4 [|l5 [|l6 sigma]]] ;
      simpl in Hsigma2 ; try (clear -Hsigma2; omega).
    exists l4, l5.
    trivial.
  Qed.
End repeat2_branching.

Section du_definition.
  (*duA stands for "down-up for A-type reversed weights"
    namely starting from repeat a p ++ repeat b q with a<=b,
    decrement one entry and increment another one,
    to keep total = 0, namely keep a (radical) weight.
    Various indices correspond to which entry is increased:
    1 means an entry in repeat a p, 2 in repeat b q.
    If there are not enough entries do nothing.*)
  Definition d1u1A (a b : Z) (p q : nat) :=
    match p with
      | 0 => repeat2 a b p q
      | 1 => repeat2 a b p q
      | S (S p'') => (a-1)%Z::(repeat a p'') ++ (a+1)%Z::(repeat b q)
    end.
  Definition d1u2A (a b : Z) (p q : nat) :=
    match p with
      | 0 => repeat2 a b p q
      | S p' => match q with
                  | 0 => repeat2 a b p q
                  | S q' => (a-1)%Z::(repeat a p')
                                 ++ (repeat b q') ++ (b+1)%Z::nil
                end
    end.
  Definition d2u1A (a b : Z) (p q : nat) :=
    match p with
      | 0 => repeat2 a b p q
      | S p' => match q with
                  | 0 => repeat2 a b p q
                  | S q' => (repeat a p')
                              ++ (a+1)%Z::(b-1)%Z::(repeat b q')
                end
    end.
  Definition d2u2A (a b : Z) (p q : nat) :=
    match q with
      | 0 => repeat2 a b p q
      | 1 => repeat2 a b p q
      | S (S q'') => repeat a p ++ (b-1)%Z::(repeat b q'') ++ (b+1)%Z::nil
    end.
End du_definition.

Section du_radical.
  Ltac tac_du_repeat :=
    repeat (simpl ;
            match goal with
              | [ |- _ /\ _] => split
              | [ |- Zvec_nondecb (_::_) = true]
                => refine (thm_Zvec_nondecb_join _ _ _ _)
              | [ |- Zvec_nondecb (_++_) = true]
                => rewrite thm_Zvec_nondecb_app_iff
              | [ |- Zvec_nondecb (repeat _ _) = true]
                => (rewrite thm_Zvec_nondecb_repeat ; trivial)
              | [ |- context[hd _ (repeat _ _)]]
                => try rewrite hd_repeat
              | [ |- context[hd _ (_++_)]]
                => try rewrite hd_app
              | [ |- context[last (repeat _ _)]]
                => try rewrite last_repeat
              | [ |- context[if ?p=?0 then _ else _]]
                => (destruct p ; simpl ; firstorder) (*Possibly dangerous loop?*)
              | [ |- context[match ?p with 0 => _ | S _ => _ end]]
                => (destruct p ; simpl ; firstorder)
              | [ Htot : context[total] |- context[total]]
                => (simpl_total ; simpl_total in Htot ; try omega)
              | [ |- _] => (simpl ; try omega ; firstorder)
            end).
  Ltac tac_du fn :=
    unfold lie_is_radical_revwt_type ;
    intros a b p q ;
    autorewrite with rewritesome ;
    intros Ha Hb [Hinc Htot] ;
    unfold fn, repeat2 in * ;
    tac_du_repeat.
  Theorem thm_d1u1A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (repeat2 a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d1u1A a b p q) = true.
  Proof.
    tac_du d1u1A.
  Qed.
  Theorem thm_d1u2A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (repeat2 a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d1u2A a b p q) = true.
  Proof.
    tac_du d1u2A.
    destruct q ; simpl.
    all : tac_du_repeat.
  Qed.
  Theorem thm_d2u1A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (repeat2 a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d2u1A a b p q) = true.
  Proof.
    tac_du d2u1A.
  Qed.
  Theorem thm_d2u2A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (repeat2 a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d2u2A a b p q) = true.
  Proof.
    tac_du d2u2A.
  Qed.
End du_radical.

Section du_branching.
  Ltac tac_du_intro p q :=
    intros ;
    repeat try (destruct p ; [omega|]) ;
    repeat try (destruct q ; [omega|]) ;
    unfold Is_known_w0_branching_A_revwt,
      radical_branching_A_two_revwt_b,
      lie_is_radical_revwt_type,
      d1u1A, d1u2A, d2u1A, d2u2A,
      repeat2 in * ;
    autorewrite with rewritesome in * ;
    firstorder.
  Theorem thm_d1u1A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> 1 < p
      -> 0 < q
      -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
      -> (nth 0 lambda a < a)%Z
      -> (a < nth (1 + p) lambda a)%Z
      -> Is_known_w0_branching_A_revwt lambda (d1u1A a b p q).
  Proof.
    tac_du_intro p q.
    - autorewrite with rewritelength in *.
      omega.
    - tac_nondecb.
    - simpl_total.
      simpl_total in H9.
      omega.
    - destruct lambda ; [trivial|].
      simpl in *.
      autorewrite with rewritesome in *.
      firstorder.
      refine (thm_Zvec_leb_trans32 _ _ _ _ H12 _).
      + simpl_length ; omega.
      + rewrite app_comm_cons, cons_repeat_app, <- app_assoc.
        simpl.
        rewrite thm_Zvec_leb_app.
        simpl.
        rewrite thm_Zvec_leb_refl, thm_Zvec_leb_refl.
        autorewrite with rewritesome.
        omega.
        trivial.
    - destruct lambda as [|z [|z0 lambda]] ;
      try (clear -H3 ; simpl in * ; progress firstorder).
      tac_nth_split (S p) lambda a l1 l2 H3 H5 H12 H13 H14.
      rewrite app_comm_cons, thm_Zvec_leb_app.
      rewrite repeat_S_app, thm_Zvec_leb_app in H6.
      firstorder.
      + clear -H6.
        destruct l1 ; simpl_extra ; simpl_extra in H6 ; firstorder.
      + simpl_extra.
        simpl_extra in H15.
        firstorder.
        rewrite H13.
        omega.
      + simpl_length.
        exact (eq_sym H14).
      + simpl_length.
        exact (eq_sym H14).
  Qed.
  Theorem thm_d1u2A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> 0 < p
      -> 0 < q
      -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
      -> (nth 0 lambda a < a)%Z
      -> (b < nth (1 + p + q) lambda b)%Z
      -> Is_known_w0_branching_A_revwt lambda (d1u2A a b p q).
  Proof.
    tac_du_intro p q.
    - autorewrite with rewritelength in *.
      simpl.
      omega.
    - tac_nondecb.
      destruct q.
      all : simpl.
      all : rewrite last_repeat.
      all : destruct p ; simpl ; omega.
    - simpl_total.
      simpl_total in H9.
      omega.
    - destruct lambda ; [trivial|].
      simpl in *.
      autorewrite with rewritesome in *.
      firstorder.
      refine (thm_Zvec_leb_trans32 _ _ _ _ H12 _).
      + simpl_length ; omega.
      + rewrite cons_repeat_app, thm_Zvec_leb_app, thm_Zvec_leb_app.
        rewrite thm_Zvec_leb_refl, thm_Zvec_leb_refl.
        all : trivial.
        simpl_extra.
        omega.
    - destruct lambda as [|z [|z0 lambda]] ;
      try (clear -H3 ; simpl in * ; progress firstorder).
      tac_nth_split (p + S q) lambda b l1 l2 H3 H5 H12 H13 H14.
      rewrite app_comm_cons, app_assoc, thm_Zvec_leb_app.
      simpl repeat in H6.
      rewrite (cons_repeat_app _ b q), app_assoc, thm_Zvec_leb_app in H6.
      firstorder.
      + clear -H6.
        destruct l1 ; simpl_extra ; simpl_extra in H6 ; firstorder.
      + simpl_extra.
        simpl_extra in H15.
        rewrite H13.
        omega.
      + simpl_length ; clear -H14 ; omega.
      + simpl_length ; clear -H14 ; omega.
  Qed.
  Theorem thm_d2u1A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (0 < p)%nat
      -> (0 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
      -> (nth p lambda b < b)%Z
      -> (a < nth (1 + p) lambda a)%Z
      -> Is_known_w0_branching_A_revwt lambda (d2u1A a b p q).
  Proof.
    tac_du_intro p q.
    - autorewrite with rewritelength in *.
      simpl.
      omega.
    - tac_nondecb.
    - simpl_total.
      simpl_total in H9.
      omega.
    - tac_nth_split p lambda a l1 l2 H3 H5 H12 H13 H14.
      rewrite thm_Zvec_leb_app.
      rewrite repeat_S_app, thm_Zvec_leb_app in H7.
      firstorder.
      all : try (rewrite H14 ; simpl_length ; trivial).
      simpl_extra.
      simpl_extra in H15.
      firstorder.
      destruct l2 ; [trivial|].
      simpl_extra.
      assert (S p - p = 1) as H17.
      { clear. omega. }
      rewrite app_nth2, H14, H17 in H4.
      all : try rewrite H14 in *.
      simpl in H4.
      simpl_extra in H16.
      all : firstorder.
    - rewrite repeat_S_app in H6.
      tac_nth_split p (tl (tl lambda)) a l1 l2 H3 H5 H12 H13 H14.
      rewrite thm_Zvec_leb_app ; [|rewrite H14 ; tac_length].
      rewrite thm_Zvec_leb_app in H6 ; [|rewrite H14 ; tac_length].
      firstorder.
      set (z := nth p (tl (tl lambda)) a) in *.
      assert (z = nth (S (S p)) lambda a) as H16.
      {
        unfold z.
        destruct lambda as [|x [|x0 lambda]].
        all : simpl in * ; firstorder.
      }
      rewrite H16, thm_Zvec_leb_cons in *.
      firstorder.
      refine (thm_Zvec_leb_trans32 _ _ _ _ _ H17).
      + autorewrite with rewritelength in *.
        rewrite H14 in *.
        pose (H18 := eq_refl (length (tl (tl lambda)))).
        rewrite H13 in H18 at 1.
        simpl_length in H18.
        omega.
      + simpl_extra.
        split ; [omega|apply thm_Zvec_leb_refl].
  Qed.
  Theorem thm_d2u2A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (0 < p)%nat
      -> (1 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
      -> (nth p lambda b < b)%Z
      -> (b < nth (1 + p + q) lambda b)%Z
      -> Is_known_w0_branching_A_revwt lambda (d2u2A a b p q).
  Proof.
    tac_du_intro p q.
    - autorewrite with rewritelength in *.
      simpl.
      omega.
    - tac_nondecb.
    - simpl_total.
      simpl_total in H9.
      omega.
    - tac_nth_split (S p) lambda b l1 l2 H3 H5 H12 H13 H14.
      rewrite thm_Zvec_leb_app ; [|rewrite H14 ; tac_length].
      rewrite thm_Zvec_leb_app in H7 ; [|rewrite H14 ; tac_length].
      firstorder.
      simpl_extra.
      simpl_extra in H15.
      firstorder.
      + rewrite H13 ; omega.
      + rewrite cons_repeat_app in H16.
        tac_nth_split q l2 b l3 l4 H3 H5 H17 H18 H19.
        rewrite thm_Zvec_leb_app ; [|rewrite H19 ; tac_length].
        rewrite thm_Zvec_leb_app in H16 ; [|rewrite H19 ; tac_length].
        firstorder.
        simpl_extra.
        simpl_extra in H20.
        firstorder.
    - destruct lambda as [|x [|x0 lambda]].
      all : simpl_length in H3.
      all : try (clear -H3 ; omega).
      simpl tl in *.
      tac_nth_split (2 + p + q) lambda b l1 l2 H3 H5 H12 H13 H14.
      rewrite app_comm_cons, app_assoc, thm_Zvec_leb_app ; [|rewrite H14 ; tac_length].
      assert (repeat b (S (S q)) = repeat b (S q) ++ b::nil) as Hbq.
      { simpl. rewrite cons_repeat_app. trivial. }
      rewrite Hbq, app_assoc, thm_Zvec_leb_app in H6 ; [|rewrite H14 ; tac_length].
      firstorder.
      + refine (thm_Zvec_leb_trans32 _ _ _ _ _ H6).
        * simpl_length. omega.
        * rewrite thm_Zvec_leb_app, thm_Zvec_leb_refl.
          simpl_extra.
          rewrite thm_Zvec_leb_refl.
          clear.
          all : firstorder.
      + simpl_extra.
        rewrite <- H13 in H5.
        clear -H5.
        rewrite plus_n_Sm, plus_n_Sm.
        omega.
  Qed.
End du_branching.

Section du_not_exceptional.
  Theorem thm_d1u1A_not_exceptional :
    forall a b p q g,
      lie_algebra_type g = lie_A_type
      -> (a < 0)%Z
      -> (0 < b)%Z
      -> 1 < p
      -> 0 < q
      -> ~ (Is_exceptional_revwt_alg g (d1u1A a b p q)).
  Proof.
    intros a b p q g Hgtype Ha Hb Hp Hq Hexc.
    destruct p as [|[|p]] ; try (clear -Hp ; omega).
    destruct q as [|q] ; try (clear -Hq ; omega).
    destruct (thm_A_exceptional_repeat2 g Hgtype _ Hexc)
      as [a0 [b0 [p0 [q0 [Ha0b0 H]]]]].
    clear g Hgtype Hexc.
    unfold d1u1A in H.
    simpl in H.
    rewrite <- (app_nil_l (b::_)) in H.
    destruct (repeat2_fact1 _ _ _ _ _ _ _ _ _ _ _ H) as [H0|H0] ; omega.
  Qed.
  Theorem thm_d1u2A_not_exceptional :
    forall a b p q g,
      lie_algebra_type g = lie_A_type
      -> (a < 0)%Z
      -> (0 < b)%Z
      -> 0 < p
      -> 0 < q
      -> 1 < p \/ 1 < q
      -> ~ (Is_exceptional_revwt_alg g (d1u2A a b p q)).
  Proof.
    intros a b p q g Hgtype Ha Hb Hp Hq Hpq Hexc.
    destruct p as [|p] ; try (clear -Hp ; omega).
    destruct q as [|q] ; try (clear -Hq ; omega).
    destruct (thm_A_exceptional_repeat2 g Hgtype _ Hexc)
      as [a0 [b0 [p0 [q0 [Ha0b0 H]]]]].
    clear g Hgtype Hexc.
    unfold d1u2A in H.
    destruct q.
    - destruct p.
      + firstorder.
      + simpl in H.
        rewrite <- (app_nil_l (a::_)) in H.
        destruct (repeat2_fact1 _ _ _ _ _ _ _ _ _ _ _ H) as [H0|H0] ; omega.
    - simpl in H.
      destruct (repeat2_fact1 _ _ _ _ _ _ _ _ _ _ _ H) as [H0|H0] ; omega.
  Qed.
  Theorem thm_d2u1A_not_exceptional_prelim :
    forall p q,
      (Z.of_nat q * 1)%Z = (- (Z.of_nat p * -1))%Z
      -> q = p.
  Proof.
    intros.
    rewrite Zopp_mult_distr_r in H.
    simpl (- -1)%Z in H.
    rewrite Z.mul_1_r, Z.mul_1_r in H.
    rewrite Nat2Z.inj_iff in H.
    assumption.
  Qed.
  Theorem thm_d2u1A_not_exceptional :
    forall a b p q g,
      lie_algebra_type g = lie_A_type
      -> (a < 0)%Z
      -> (0 < b)%Z
      -> 0 < p
      -> 0 < q
      -> 1 < p \/ 1 < q
      -> (Z.of_nat q * b = - (Z.of_nat p * a))%Z
      -> ~ (Is_exceptional_revwt_alg g (d2u1A a b p q)).
  Proof.
    intros a b p q g Hgtype Ha Hb Hp Hq Hpq Htot Hexc.
    destruct p as [|p] ; try (clear -Hp ; omega).
    destruct q as [|q] ; try (clear -Hq ; omega).
    destruct (thm_A_exceptional_repeat2 g Hgtype _ Hexc)
      as [a0 [b0 [p0 [q0 [Ha0b0 H]]]]].
    clear g Hgtype Hexc.
    unfold d2u1A in H.
    destruct q ; destruct p ; simpl in H.
    - firstorder.
    - rewrite <- (app_nil_l ((b-1)%Z::_)) in H.
      destruct (repeat2_fact1 _ _ _ _ _ _ _ _ _ _ _ H) as [H0|H0] ; [omega|].
      assert (a = -1 /\ b = 1)%Z as [H1 H2] ; [omega|].
      rewrite H1, H2 in Htot.
      pose (H3 := thm_d2u1A_not_exceptional_prelim _ _ Htot).
      clear -H3.
      omega.
    - rewrite <- (app_nil_l ((b-1)%Z::_)) in H.
      rewrite <- (app_nil_l (b%Z::_)) in H.
      destruct (repeat2_fact1 _ _ _ _ _ _ _ _ _ _ _ H) as [H0|H0] ; [|omega].
      assert (a = -1 /\ b = 1)%Z as [H1 H2] ; [omega|].
      rewrite H1, H2 in Htot.
      pose (H3 := thm_d2u1A_not_exceptional_prelim _ _ Htot).
      clear -H3.
      omega.
    - rewrite <- (app_nil_l (b%Z::_)) in H.
      rewrite (app_comm_cons nil _ (b-1)%Z) in H.
      destruct (repeat2_fact1 _ _ _ _ _ _ _ _ _ _ _ H) as [H0|H0] ; omega.
  Qed.
  Theorem thm_d2u2A_not_exceptional :
    forall a b p q g,
      lie_algebra_type g = lie_A_type
      -> (a < 0)%Z
      -> (0 < b)%Z
      -> 0 < p
      -> 1 < q
      -> ~ (Is_exceptional_revwt_alg g (d2u2A a b p q)).
  Proof.
    intros a b p q g Hgtype Ha Hb Hp Hq Hexc.
    destruct p as [|p] ; try (clear -Hp ; omega).
    destruct q as [|[|q]] ; try (clear -Hq ; omega).
    destruct (thm_A_exceptional_repeat2 g Hgtype _ Hexc)
      as [a0 [b0 [p0 [q0 [Ha0b0 H]]]]].
    clear g Hgtype Hexc.
    unfold d2u2A in H.
    simpl in H.
    destruct (repeat2_fact1 _ _ _ _ _ _ _ _ _ _ _ H) as [H0|H0] ; omega.
  Qed.
End du_not_exceptional.

Section du_main.
  Theorem thm_duA :
    forall g h,
      lie_algebra_type g = lie_A_type
      -> lie_algebra_type h = lie_A_type
      -> forall lambda,
           lie_is_radical_revwt_alg g lambda = true
           -> forall a b p q,
                (a < 0)%Z
                -> (0 < b)%Z
                -> 0 < p
                -> 0 < q
                -> 1 < p \/ 1 < q
                -> (Z.of_nat q * b = - (Z.of_nat p * a))%Z
                -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
                -> (exists mu,
                      Is_known_w0_branching_A_revwt lambda mu
                      /\ ~ (Is_exceptional_revwt_alg h mu))
                   \/ (nth 0 lambda a = a /\ nth p lambda b = b)
                   \/ (a = nth (1 + p) lambda a /\ b = nth (1 + p + q) lambda b)
                   \/ (1 = q /\ nth 0 lambda a = a /\ a = nth (1 + p) lambda a)
                   \/ (1 = p /\ nth p lambda b = b /\ b = nth (1 + p + q) lambda b).
  Proof.
    intros g h Hgtype Hhtype lambda Hrad a b p q Ha Hb Hp Hq Hpq Htot Hbranch.
    pose (H11 := fun Hp1 => thm_d1u1A a b p q lambda Ha Hb Hp1 Hq Hbranch).
    pose (H12 := thm_d1u2A a b p q lambda Ha Hb Hp Hq Hbranch).
    pose (H21 := thm_d2u1A a b p q lambda Ha Hb Hp Hq Hbranch).
    pose (H22 := fun Hq1 => thm_d2u2A a b p q lambda Ha Hb Hp Hq1 Hbranch).
    pose (H11notexc := fun Hp1 => thm_d1u1A_not_exceptional a b p q h Hhtype Ha Hb Hp1 Hq).
    pose (H12notexc := thm_d1u2A_not_exceptional a b p q h Hhtype Ha Hb Hp Hq Hpq).
    pose (H21notexc := thm_d2u1A_not_exceptional a b p q h Hhtype Ha Hb Hp Hq Hpq Htot).
    pose (H22notexc := thm_d2u2A_not_exceptional a b p q h Hhtype Ha Hb Hp).
    destruct (thm_repeat2_nthc a b p q lambda Ha Hb Hp Hq Hpq Hbranch)
      as [Hn0 [Hn1 [Hn2 Hn3]]].
    clearbody H11 H12 H21 H22 H11notexc H12notexc H21notexc H22notexc.
    destruct p as [|p] ; try (clear -Hp ; omega).
    destruct q as [|q] ; try (clear -Hq ; omega).
    destruct (Z_le_lt_eq_dec _ _ Hn0) as [Hn0lt|Hn0eq] ;
      destruct (Z_le_lt_eq_dec _ _ Hn1) as [Hn1lt|Hn1eq] ;
      destruct (Z_le_lt_eq_dec _ _ Hn2) as [Hn2lt|Hn2eq] ;
      destruct (Z_le_lt_eq_dec _ _ Hn3) as [Hn3lt|Hn3eq].
    all : try exact (or_introl (ex_intro _ _ (conj (H12 Hn0lt Hn3lt) H12notexc))).
    all : try exact (or_introl (ex_intro _ _ (conj (H21 Hn2lt Hn1lt) H21notexc))).
    all : try rewrite Hn0eq in *.
    all : try rewrite <- Hn1eq in *.
    all : try rewrite Hn2eq in *.
    all : try rewrite <- Hn3eq in *.
    all : try (clear ; tauto).
    - destruct p.
      + clear ; tauto.
      + exact (or_introl (ex_intro
                            _ _ (conj
                                   (H11 (thm_1_lt_SS p) Hn0lt Hn1lt)
                                   (H11notexc (thm_1_lt_SS p))))).
    - destruct q.
      + clear ; tauto.
      + exact (or_introl (ex_intro
                            _ _ (conj
                                   (H22 (thm_1_lt_SS q) Hn2lt Hn3lt)
                                   (H22notexc (thm_1_lt_SS q))))).
  Qed.
  Theorem thm_A_impossible_total:
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> 0 < p
      -> 0 < q
      -> Is_known_w0_branching_A_revwt lambda (repeat2 a b p q)
      -> (nth 0 lambda a = a /\ nth p lambda b = b)
         \/ (a = nth (1 + p) lambda a /\ b = nth (1 + p + q) lambda b)
      -> False.
  Proof.
    intros a b p q lambda Ha Hb Hp Hq Hbranch.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b, lie_is_radical_revwt_type in Hbranch.
    autorewrite with rewritesome in Hbranch.
    destruct Hbranch as [[[[Hlength [Hincl Htotl]] [_ Htotm]] _] _].
    intros [[H0 H1]|[H0 H1]].
    - assert (Zvec_short_allb Z.leb (repeat2 a b p (2 + q)) lambda = true) as H.
      {
        unfold repeat2 in *.
        assert (p <= length lambda) as Hlenp.
        { clear -Hlength. simpl_length in Hlength. omega. }
        pose (Hlsplit := eq_sym (firstn_skipn p lambda)).
        rewrite Hlsplit, thm_Zvec_leb_app.
        split.
        + assert (length (firstn p lambda) = p) as Htmplen.
          { simpl_length. exact (min_l _ _ Hlenp). }
          rewrite <- Htmplen at 1.
          refine (thm_Zvec_nondecb_hd_leb _ _ _ _).
          * exact (thm_Zvec_nondecb_firstn _ _ Hincl).
          * rewrite nth_0 in H0.
            rewrite hd_firstn, H0.
            destruct p ; simpl ; omega.
        + assert (length (skipn p lambda) = 2 + q) as Htmplen.
          { simpl_length in Hlength ; tac_length. }
          rewrite <- Htmplen at 1.
          refine (thm_Zvec_nondecb_hd_leb _ _ _ _).
          * exact (thm_Zvec_nondecb_skipn _ _ Hincl).
          * rewrite hd_skipn, H1 ; omega.
        + simpl_length.
          exact (eq_sym (min_l _ _ Hlenp)).
      }
      assert (length lambda = length (repeat2 a b p (2 + q))) as Hlen2.
      {
        unfold repeat2 in *.
        simpl_length in Hlength.
        tac_length.
      }
      pose (H2 := thm_Zvec_leb_total_same_length _ _ Hlen2 H).
      rewrite Htotl in H2.
      unfold repeat2 in H2, Htotm.
      simpl_total in H2.
      simpl_total in Htotm.
      clear - Ha Hb H2 Htotm.
      omega.
    - unfold repeat2 in *.
      simpl_length in Hlength.
      assert (2 + p <= length lambda) as Hlength2.
      { omega. }
      assert (length (firstn (2 + p) lambda) = 2 + p) as Hlength3.
      { autorewrite with rewritelength ; exact (min_l _ _ Hlength2). }
      assert (length (skipn (2 + p) lambda) = q) as Hlength4.
      { autorewrite with rewritelength ; omega. }
      pose (Hlambdaval := eq_sym (firstn_skipn (2 + p) lambda)).
      rewrite Hlambdaval in H0, H1, Hincl.
      rewrite app_nth1 in H0.
      rewrite app_nth2 in H1.
      all : try rewrite Hlength3 in *.
      all : try omega.
      destruct (thm_Zvec_nondecb_app _ _ Hincl) as [Hinchd Hinctl].
      assert (total (firstn (2 + p) lambda)
              <= total (repeat a (2 + p)))%Z as H3.
      {
        refine (thm_Zvec_leb_total_same_length _ _ _ _).
        - autorewrite with rewritelength.
          exact (eq_sym (min_l _ _ Hlength2)).
        - assert (1 + p = 2 + p - 1) as H2.
          { omega. }
          rewrite H2 in H0.
          rewrite <- Hlength3 in H0 at 1.
          rewrite nth_last, Z.eq_sym_iff in H0.
          rewrite <- Hlength3 at 2.
          exact (thm_Zvec_nondecb_last_leb2 _ _ H0 Hinchd).
      }
      assert (total (skipn (2 + p) lambda)
              <= total (repeat b q))%Z as H4.
      {
        refine (thm_Zvec_leb_total_same_length _ _ _ _).
        - autorewrite with rewritelength.
          omega.
        - assert (1 + p + q - (2 + p) = q - 1) as H2.
          { omega. }
          rewrite H2, <- Hlength4, nth_last, Z.eq_sym_iff in H1.
          rewrite <- Hlength4.
          exact (thm_Zvec_nondecb_last_leb2 _ _ H1 Hinctl).
      }
      rewrite Hlambdaval, thm_total_app in Htotl.
      pose (H5 := Z.add_le_mono _ _ _ _ H3 H4).
      rewrite Htotl in H5.
      simpl_total in Htotm.
      simpl_total in H5.
      clear -Htotm Ha H5.
      omega.
  Qed.
End du_main.

Section du_zero.
  Theorem thm_A_m101_branch :
    forall n lambda,
      Is_known_w0_branching_A_revwt lambda (repeat 0%Z (3 + n))
      -> lambda <> repeat 0%Z (5 + n)
      -> Is_known_w0_branching_A_revwt
           lambda ((-1)%Z :: repeat 0%Z (S n) ++ 1%Z :: nil).
  Proof.
    unfold Is_known_w0_branching_A_revwt,
    radical_branching_A_two_revwt_b, lie_is_radical_revwt_type.
    intros n lambda H H0.
    autorewrite with rewritesome in *.
    autorewrite with rewritelength in *.
    assert (length lambda = length (repeat 0%Z (5 + n))) as Hlen.
    { simpl in H. tac_length. }
    assert (length lambda <= length (repeat 0%Z (5 + n))) as Hlen2.
    { rewrite <- Hlen. omega. }
    firstorder.
    - tac_length.
    - tac_nondecb.
    - simpl_total. trivial.
    - destruct lambda as [|z lambda].
      + simpl. trivial.
      + simpl_extra.
        split.
        * simpl_extra in H2.
          destruct H2 as [H2 H7].
          destruct (Z_le_lt_eq_dec z 0%Z H2) as [H8|H8].
          { omega. }
          {
            rewrite H8 in *.
            elimtype False.
            refine (H0 (eq_sym _)).
            rewrite <- thm_Zvec_leb_eq_tot.
            - rewrite H6.
              simpl_total.
              trivial.
            - exact (eq_sym Hlen).
            - pose (H9 := thm_Zvec_nondecb_hd_leb (0%Z::lambda) 0%Z H5).
              rewrite Hlen in H9.
              autorewrite with rewritelength in H9.
              refine (H9 _).
              simpl.
              omega.
          }
        * simpl_destruct H2 as [Hz0 H2].
          refine (thm_Zvec_leb_trans32 _ _ _ _ H2 _).
          { tac_length. }
          {
            generalize n ; clear.
            induction n ; simpl ; trivial.
          }
    - destruct lambda as [|z [|z0 lambda]].
      + simpl. trivial.
      + simpl. trivial.
      + simpl tl in *.
        tac_nth_split (S (S n)) lambda 0%Z l1 l2 Hlen Hlen H12 H13 H14.
        rewrite app_comm_cons, thm_Zvec_leb_app ; [|clear -H14 ; tac_length].
        assert (repeat 0%Z (3 + n) = repeat 0%Z (2 + n) ++ 0%Z::nil) as H7.
        { rewrite <- cons_repeat_app. trivial. }
        rewrite H7, thm_Zvec_leb_app in H1 ; [|clear -H14 ; tac_length].
        destruct H1 as [H1a H1b].
        split.
        * refine (thm_Zvec_leb_trans32 _ _ _ _ _ H1a).
          { clear -H14 ; tac_length. }
          simpl.
          apply thm_Zvec_leb_refl.
        * simpl_extra.
          simpl_extra in H1b.
          destruct (Z_le_lt_eq_dec _ _ H1b)%Z as [H8|H8].
          { omega. }
          {
            rewrite <- H8 in *.
            elimtype False.
            set (lambda0 := z :: _) in *.
            refine (H0 _).
            rewrite <- thm_Zvec_leb_eq_tot.
            - rewrite H6.
              simpl_total.
              trivial.
            - rewrite H.
              clear.
              tac_length.
            - simpl_length in Hlen.
              assert (length l2 = 0) as H1.
              { clear -Hlen H14. omega. }
              destruct l2 ; simpl in H1 ; [| discriminate H1].
              unfold lambda0 in H5.
              rewrite app_comm_cons, app_comm_cons in H5.
              unfold lambda0.
              rewrite app_comm_cons, app_comm_cons.
              assert (5 + n = 1 + length (z::z0::l1)) as H9.
              { tac_length. }
              rewrite H9.
              exact (thm_Zvec_nondecb_last_leb _ _ H5).
          }
  Qed.
  Theorem thm_A_m101_notexc :
    forall n Hn,
      let h := lie_A (exist (fun n : nat => n > 0) (S (S n)) Hn) in
      let nu := (-1)%Z :: repeat 0%Z (S n) ++ 1%Z :: nil in
      lie_is_radical_revwt_alg h nu = true
      /\ ~ (Is_exceptional_revwt_alg h nu).
  Proof.
    intros.
    split.
    - unfold lie_is_radical_revwt_alg, h,
      lie_algebra_type, lie_is_radical_revwt_type.
      autorewrite with rewritesome.
      repeat split.
      + tac_length.
      + unfold nu ; tac_nondecb.
      + simpl_total.
        trivial.
    - intros Hnuexc.
      assert (lie_algebra_type h = lie_A_type) as Hhtype.
      { trivial. }
      destruct (thm_A_exceptional_repeat2 h Hhtype nu Hnuexc)
        as [a [b [p [q [Hab Hnu]]]]].
      unfold nu in Hnu.
      simpl in Hnu.
      rewrite <- (app_nil_l (0%Z::_)) in Hnu.
      pose (H := repeat2_fact1 _ _ _ _ _ _ _ _ _ _ _ Hnu).
      clear -H.
      omega.
  Qed.
End du_zero.

Section main.
  Theorem thm_main_A :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           lie_is_radical_revwt_alg g lambda = true
           -> (Is_exceptional_revwt_alg g lambda)
              \/ (Is_mixed_revwt_alg g lambda).
  Proof.
    intros g Hgtype.
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    generalize n, Hn. clear n Hn Hgtype.
    refine (nat_ind2 _ _ _ _).
    - intros Hn. contradiction (gt_irrefl 0 Hn).
    - intros Hn lambda.
      exact (thm_main_A1 _ lambda Hn (eq_refl _)).
    - intros n IHn Hn2 lambda.
      destruct n as [|[|n]].
      + exact (thm_main_A2 _ lambda Hn2 (eq_refl _)).
      + exact (thm_main_A3 _ lambda Hn2 (eq_refl _)).
      + intros Hrad.
        unfold lie_is_radical_revwt_alg, lie_algebra_type in Hrad.
        autorewrite with rewritesome in Hrad.
        destruct Hrad as [Hlength Hrad].
        simpl in Hlength.
        assert (length lambda >= 2) as Hl2.
        { rewrite Hlength. simpl. omega. }
        assert (S (S n) > 0) as Hn.
        { firstorder. }
        pose (h := lie_A (exist (fun n : nat => n > 0) (S (S n)) Hn)).
        assert (lie_algebra_type h = lie_A_type) as Hhtype.
        { simpl ; trivial. }
        pose (Hknownbranching := thm_An_branching_fact1 lambda Hrad Hl2).
        pose (H := Hknownbranching).
        set (mu := branchof lambda) in *.
        clearbody mu H Hknownbranching.
        unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b in H.
        simpl_destruct H as [[[[Hlenlm Hradl] Hradm] Hlm] Hml].
        assert (lie_is_radical_revwt_alg h mu = true) as Hradalgmu.
        {
          unfold lie_is_radical_revwt_alg.
          simpl_extra.
          split.
          omega.
          assumption.
        }
        pose (g := lie_A (exist (fun n : nat => n > 0) (S (S (S (S n)))) Hn2)).
        assert (lie_algebra_type g = lie_A_type) as Hgtype.
        { simpl ; trivial. }
        assert (lie_is_radical_revwt_alg g lambda = true) as Hradalglambda.
        {
          unfold lie_is_radical_revwt_alg.
          simpl_extra.
          split ; assumption.
        }
        destruct (IHn Hn mu Hradalgmu) as [Hmuexc|Hmumix].
        * destruct (thm_A_exceptional_structure h Hhtype mu Hmuexc)
            as [Hmuval0|[a [b [p [q [Ha [Hb [Hp [Hq [Htot Hmuval]]]]]]]]]].
          {
            destruct (list_eq_dec Z.eq_dec lambda (repeat 0%Z (5 + n)))
              as [Hlambdaval0|Hlambdaval].
            - left.
              rewrite Hlambdaval0.
              unfold Is_exceptional_revwt_alg.
              exists 1, 0%Z.
              rewrite thm_Zvec_mul_0.
              unfold lie_radical_fundamental_revwt_alg, is_exceptional_multiplier.
              simpl_length.
              rewrite plus_comm.
              tauto.
            - right.
              assert (length mu = 3 + n) as Hlenmu.
              { clear - Hlenlm Hlength. omega. }
              rewrite Hmuval0, Hlenmu in Hknownbranching.
              destruct (thm_A_m101_notexc n Hn) as [Hradalgnu Hnunotexc].
              set (nu := (-1::repeat 0%Z (S n) ++ 1::nil)%Z) in *.
              fold h in Hradalgnu, Hnunotexc, Hmuexc.
              destruct (IHn Hn nu Hradalgnu) as [Hnuexc|Hnumix].
              { contradiction (Hnunotexc Hnuexc). }
              refine (mixed_by_induction g lambda h nu _ _).
              all : unfold g, h, Is_known_w0_branching_revwt_alg, lie_algebra_type.
              all : repeat split.
              + exact Hnumix.
              + exact Hradalglambda.
              + exact Hradalgnu.
              + exact (thm_A_m101_branch n lambda Hknownbranching Hlambdaval).
          }
          {
            assert (length mu >= 3) as Hlenmu3.
            { clear - Hlength Hlenlm. omega. }
            assert (p + q >= 3) as Hpq3.
            {
              rewrite Hmuval in Hlenmu3.
              simpl_length in Hlenmu3.
              assumption.
            }
            assert (1 < p \/ 1 < q) as H1p1q.
            { clear -Hpq3. omega. }
            rewrite Hmuval in Hknownbranching.
            destruct (thm_duA g h Hgtype Hhtype
                              lambda Hradalglambda
                              a b p q Ha Hb Hp Hq
                              H1p1q Htot Hknownbranching)
                     as [[nu [Hnubr Hnunotexc]]|[H|[H|[H|H]]]].
            - right.
              assert (lie_is_radical_revwt_alg h nu = true) as Hradalgnu.
              {
                unfold lie_is_radical_revwt_alg.
                simpl_extra.
                unfold Is_known_w0_branching_A_revwt,
                radical_branching_A_two_revwt_b in Hnubr.
                simpl_destruct Hnubr as [[[[Hnulen Hradlam] Hradnu] Hln] Hnl].
                split.
                - clear - Hnulen Hlength ; omega.
                - assumption.
              }
              destruct (IHn Hn nu Hradalgnu) as [Hnuexc|Hnumix].
              { contradiction (Hnunotexc Hnuexc). }
              refine (mixed_by_induction g lambda h nu _ _).
              all : unfold g, h, Is_known_w0_branching_revwt_alg, lie_algebra_type.
              all : repeat split.
              + exact Hnumix.
              + exact Hradalglambda.
              + exact Hradalgnu.
              + exact Hnubr.
            - contradiction (thm_A_impossible_total
                               a b p q lambda Ha Hb Hp Hq
                               Hknownbranching (or_introl H)).
            - contradiction (thm_A_impossible_total
                               a b p q lambda Ha Hb Hp Hq
                               Hknownbranching (or_intror H)).
            - left.
              destruct H as [H1q [Hnth0 Hnth1]].
              rewrite <- H1q in *.
              assert (1 + p = length lambda - 2) as Hlength3.
              {
                rewrite Hmuval in Hlenlm.
                clear - Hlenlm.
                simpl_length in Hlenlm.
                omega.
              }
              rewrite Hlength3 in Hnth1.
              exact (thm_A_exceptional_from_bounds1
                       g lambda a Hgtype Hrad Hlength Ha Hnth0 Hnth1).
            - left.
              destruct H as [H1p [Hnth0 Hnth1]].
              rewrite <- H1p in *.
              assert (1 + 1 + q = length lambda - 1) as Hlength3.
              {
                rewrite Hmuval in Hlenlm.
                clear - Hlenlm.
                simpl_length in Hlenlm.
                omega.
              }
              rewrite Hlength3 in Hnth1.
              exact (thm_A_exceptional_from_bounds2
                       g lambda b Hgtype Hrad Hlength Hb Hnth0 Hnth1).
          }
        * assert (Is_known_w0_branching_revwt_alg g lambda h mu) as Hkb2.
          {
            unfold g, h, Is_known_w0_branching_revwt_alg, lie_algebra_type.
            repeat split ; assumption.
          }
          exact (or_intror (mixed_by_induction g lambda h mu Hmumix Hkb2)).
  Qed.
End main.
