Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Load our files*)
Require Import Rewriting.
Require Import ListExtras.
Require Import Zvec.
Require Import SimpleLieAlgebras.
Require Import Data.
Require Import TypeAll.
Open Scope nat_scope.

Section helpers.
  Definition nat_ind2
             (P : nat -> Prop)
             (f0 : P 0) (f1 : P 1)
             (fn : forall (n : nat), P n -> P (S (S n))) :=
    fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
      | 0 => f0
      | 1 => f1
      | S (S n0) => fn n0 (F n0)
    end.
End helpers.

Section theorems_for_A_type.
  Ltac show_mixed_by_ideal g lambda mu :=
    match goal with
      | [Hg : g = _ |- _]
        =>
        (right;
         refine (mixed_by_ideal g lambda mu _) ;
         split ;
         [
           refine (mixed_by_hand g mu _) ;
           rewrite Hg ;
           simpl ; trivial
         |
         rewrite Hg ;
           unfold Zvec_short_sub, lie_is_dominant_revwt_alg ;
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
  Local Fixpoint tmp_A_pred (lambda mu : list Z) :=
    match lambda with
      | nil => nil
      | a :: lambda' =>
        match mu with
          | nil => nil
          | b :: mu' =>
            if (a <? b)%Z then (b - 1)%Z :: mu' else b :: tmp_A_pred lambda' mu'
        end
    end.
  Local Fixpoint tmp_A_get_repeat (lambda mu : list Z) (n : nat) :=
    match n with
      | 0 => mu
      | S n' => tmp_A_pred lambda (tmp_A_get_repeat lambda mu n')
    end.
  Local Definition tmp_A_get (lambda : list Z) :=
    let mu := tl (tl lambda) in
    tmp_A_get_repeat lambda mu (Z.abs_nat (Zvec_total mu)).
  Theorem thm_A_pred_length0 :
    forall lambda0 mu0, length (tmp_A_pred lambda0 mu0) <= length mu0.
  Proof.
    intros lambda0 mu0.
    generalize lambda0 as lambda1.
    induction mu0 ; destruct lambda1 as [|z lambda1] ; simpl ; firstorder.
    destruct (z <? a)%Z ; simpl ; firstorder.
  Qed.
  Theorem thm_A_pred_length1 :
    forall lambda0 mu0,
      length mu0 <= length lambda0
      -> length (tmp_A_pred lambda0 mu0) = length mu0.
  Proof.
    intros lambda0 mu0.
    generalize lambda0 as lambda1.
    induction mu0 ; destruct lambda1 as [|z lambda1] ; simpl ; firstorder.
    destruct (z <? a)%Z ; simpl ; firstorder.
  Qed.
  Theorem thm_A_pred_leb :
    forall lambda mu,
      Zvec_short_allb Z.leb (tmp_A_pred lambda mu) mu = true.
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
      -> Zvec_short_allb Z.leb lambda (tmp_A_pred lambda mu) = true.
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
      -> Zvec_total (tmp_A_pred lambda0 mu0) = (Zvec_total mu0 - 1)%Z.
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
       -> hd 0 lambda <= hd 0 (tmp_A_get_repeat lambda mu n))%Z.
  Proof.
    destruct lambda, mu ; simpl ; intros ; firstorder.
    induction n.
    - simpl ; trivial.
    - simpl.
      destruct (tmp_A_get_repeat (z :: lambda) (z0 :: mu) n).
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
    forall lambda n, tmp_A_get_repeat lambda nil n = nil.
  Proof.
    induction n.
    - simpl ; trivial.
    - simpl. rewrite IHn.
      destruct lambda ; simpl ; firstorder.
  Qed.
  Theorem thm_A_get_repeat_leb :
    forall n lambda mu,
      Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb lambda (tmp_A_get_repeat lambda mu n) = true.
  Proof.
    induction n.
    - simpl ; trivial.
    - intros lambda mu H.
      simpl.
      refine (thm_A_pred_leb2 _ _ _).
      exact (IHn _ _ H).
  Qed.
  Theorem thm_A_get_leb :
    forall lambda,
      Zvec_nondecb lambda = true
      -> Zvec_short_allb Z.leb lambda (tmp_A_get lambda) = true.
  Proof.
    unfold Zvec_nondecb, tmp_A_get.
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
      -> length (tmp_A_get_repeat lambda mu n) <= length lambda.
  Proof.
    intros lambda mu n H.
    induction n.
    - simpl ; trivial.
    - simpl.
      pose (H0 := thm_A_pred_length0 lambda (tmp_A_get_repeat lambda mu n)).
      exact (le_trans _ _ _ H0 IHn).
  Qed.
  Theorem thm_A_get_repeat_length1 :
    forall lambda mu n,
      length mu <= length lambda
      -> length (tmp_A_get_repeat lambda mu n) = length mu.
  Proof.
    intros lambda mu n H.
    induction n.
    - simpl ; trivial.
    - simpl.
      pose (H0 := thm_A_pred_length1 lambda (tmp_A_get_repeat lambda mu n)).
      rewrite IHn in H0.
      firstorder.
  Qed.
  Theorem thm_A_get_total :
    forall lambda,
      (lie_is_radical_revwt_type lie_A_type lambda) = true
      -> (Zvec_total (tmp_A_get lambda) = 0)%Z.
  Proof.
    intros lambda Hrad.
    destruct lambda as [|a [|b lambda2]] ; simpl ; trivial.    
    unfold lie_is_radical_revwt_type in Hrad.
    simpl_destruct Hrad as [Hinc Htot].
    unfold tmp_A_get, tl.
    assert (Zvec_total lambda2 >= 0)%Z.
    {
      pose (H := thm_Zvec_nondecb_total_app (a::b::nil) lambda2).
      unfold app in H.
      firstorder.
    }
    set (n := Z.abs_nat (Zvec_total lambda2)).
    assert (Z.of_nat n = Zvec_total lambda2)%Z as H0.
    {
      unfold n.
      rewrite (Zabs2Nat.id_abs (Zvec_total lambda2)).
      rewrite Z.ge_le_iff in H.
      exact (Z.abs_eq _ H).
    }
    assert (forall m,
              Z.of_nat m <= Zvec_total lambda2
              -> Zvec_total (tmp_A_get_repeat (a :: b :: lambda2) lambda2 m)
                 = Zvec_total lambda2 - Z.of_nat m)%Z as H1.
    {
      set (lambda := (a::b::lambda2)).
      induction m.
      - simpl ; firstorder.
      - intros H1.
        rewrite thm_Z_of_nat_S in H1.
        assert (Z.of_nat m <= Zvec_total lambda2)%Z as Htmp.
        { omega. }
        pose (H2 := IHm Htmp). clearbody H2. clear Htmp IHm.
        cut (Zvec_total (tmp_A_get_repeat lambda lambda2 (S m))
             = Zvec_total (tmp_A_get_repeat lambda lambda2 m) - 1)%Z.
        {
          intros H4.
          rewrite H4.
          rewrite thm_Z_of_nat_S.
          omega.
        }
        assert (Zvec_short_allb
                  Z.leb lambda (tmp_A_get_repeat lambda lambda2 m) = true) as H3.
        {
          exact (thm_A_get_repeat_leb m lambda lambda2
                               (thm_Zvec_nondecb_fact3 a b lambda2 Hinc)).
        }
        assert (length (tmp_A_get_repeat lambda lambda2 m) <= length lambda) as H4.
        {
          assert (length lambda2 <= length lambda) as H5.
          { simpl. firstorder. }
          exact (thm_A_get_repeat_length0 lambda lambda2 m H5).
        }
        refine (thm_A_pred_tot lambda (tmp_A_get_repeat lambda lambda2 m) H3 H4 _).
        rewrite <- not_true_iff_false.
        intros H5.
        pose (H6 := thm_Zvec_leb_eqb_tot lambda (tmp_A_get_repeat lambda lambda2 m) H4 H3).
        rewrite H6 in H5.
        rewrite H2 in H5.
        pose (H7 := thm_Zvec_nondecb_partialsum
                      lambda (tmp_A_get_repeat lambda lambda2 m) Hinc Htot).
        rewrite <- H5 in H7.
        omega.
    }
    pose (H2 := H1 n).
    rewrite H0 in H2.
    firstorder.
  Qed.
  Theorem thm_A_get_length :
    forall lambda,
      length (tmp_A_get lambda) = length lambda - 2.
  Proof.
    destruct lambda as [|a [|b lambda2]] ; simpl ; firstorder.
    unfold tmp_A_get, tl.
    rewrite Nat.sub_0_r.
    refine (thm_A_get_repeat_length1 (a::b::lambda2) lambda2 _ _).
    simpl.
    firstorder.
  Qed.
  Theorem thm_A_get_repeat_S :
    forall lambda mu m,
      tmp_A_get_repeat lambda mu (S m)
      = tmp_A_pred lambda (tmp_A_get_repeat lambda mu m).
  Proof.
    trivial.
  Qed.
  Theorem thm_A_pred_nondecb :
    forall lambda mu,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb mu = true
      -> Zvec_nondecb (tmp_A_pred lambda mu) = true.
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
  Theorem thm_A_get_nondecb :
    forall lambda,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb (tmp_A_get lambda) = true.
  Proof.
    destruct lambda as [|a [|b lambda2]].
    - firstorder.
    - firstorder.
    - unfold tmp_A_get, tl.
      set (n := Z.abs_nat (Zvec_total lambda2)).
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
      -> Is_known_w0_branching_A_revwt lambda (tmp_A_get lambda).
  Proof.
    intros lambda Hrad Hlength.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b, tl.
    rewrite thm_A_get_length.
    destruct lambda as [|a [|b lambda]] ; simpl in Hlength ; try omega.
    autorewrite with rewritesome.
    firstorder.
    - simpl ; rewrite Nat.sub_0_r ; trivial.
    - simpl_extra.
      firstorder.
      + refine (thm_A_get_nondecb _ _).
        unfold lie_is_radical_revwt_type in Hrad.
        autorewrite with rewritesome in Hrad.
        firstorder.
      + refine (thm_A_get_total _ Hrad).
    - refine (thm_A_get_leb (a::b::lambda) _).
      unfold lie_is_radical_revwt_type in Hrad.
      autorewrite with rewritesome in Hrad.
      firstorder.
    - unfold tmp_A_get, tl.
      set (n := Z.abs_nat (Zvec_total lambda)).
      generalize n as n0.
      induction n0.
      + apply thm_Zvec_leb_refl.
      + rewrite thm_A_get_repeat_S.
        refine (thm_Zvec_leb_trans12 _ _ _ _ _ IHn0).
        * exact (thm_A_pred_length0 _ _).
        * exact (thm_A_pred_leb _ _).
  Qed.
  Theorem thm_A_radical_mrev :
    forall lambda,
      lie_is_radical_revwt_type lie_A_type lambda = true
      -> lie_is_radical_revwt_type
           lie_A_type (rev (map Z.opp lambda)) = true.
  Proof.
    unfold lie_is_radical_revwt_type.
    intros lambda.
    autorewrite with rewritesome.
    firstorder.
    - apply thm_Zvec_nondecb_mrev. assumption.
    - rewrite thm_Zvec_total_mrev. omega.
  Qed.
  Theorem thm_An_branching_fact2 :
    forall lambda mu,
      Is_known_w0_branching_A_revwt lambda mu
      -> Is_known_w0_branching_A_revwt
           (rev (map (Z.opp) lambda))
           (rev (map (Z.opp) mu)).
  Proof.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b.
    intros lambda mu.
    autorewrite with rewritesome.
    firstorder.
    - tac_length.
    - apply thm_A_radical_mrev. assumption.
    - apply thm_A_radical_mrev. assumption.
    - apply thm_Zvec_leb_mrev1. assumption. assumption.
    - apply thm_Zvec_leb_mrev2. assumption. assumption.
  Qed.
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
  Theorem thm_A_exceptional_twoval :
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
    - rewrite thm_repeat_map, Zmult_0_r in H0.
      rewrite H0.
      autorewrite with rewritelength.
      rewrite thm_repeat_plus.
      exists 0%Z, 0%Z, 1, n.
      pose (H1 := Z.le_refl 0%Z).
      firstorder.
    - rewrite map_app, thm_repeat_map, thm_repeat_map in H0.
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
           -> Zvec_total lambda = 0%Z.
  Proof.
    intros g Hgtype lambda [i [m [H H0]]].
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    rewrite H0.
    rewrite thm_Zvec_total_mul.
    unfold lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank.
    destruct_bool (n <? i) Hni.
    - rewrite orb_true_r.
      simpl.
      rewrite thm_Zvec_total_repeat, Zmult_0_r, Zmult_0_r.
      trivial.
    - destruct_bool (i =? 0) Hi.
      + rewrite orb_true_l.
        simpl.
        rewrite thm_Zvec_total_repeat, Zmult_0_r, Zmult_0_r.
        trivial.
      + assert (forall x y : list Z, (if false || false then x else y) = y) as H1.
        { trivial. }
        rewrite H1.
        rewrite thm_Zvec_total_app.
        rewrite thm_Zvec_total_repeat.
        rewrite thm_Zvec_total_repeat.
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
    destruct (thm_A_exceptional_twoval g Hgtype lambda Hexc)
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
      rewrite thm_last_repeat.
      destruct (p =? 0) ; omega.
  Qed.
  Theorem thm_A_exceptional_structure :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           Is_exceptional_revwt_alg g lambda
           -> lambda = repeat 0%Z (length lambda)
              \/ (exists a b p q,
                    a < 0
                    /\ 0 < b
                    /\ (0 < p)%nat
                    /\ (0 < q)%nat
                    /\ Z.of_nat q * b = - (Z.of_nat p * a)
                    /\ lambda = repeat a p ++ repeat b q)%Z.
  Proof.
    intros g Hgtype lambda Hexc.
    destruct (thm_A_exceptional_twoval g Hgtype lambda Hexc)
      as [a [b [p [q [Hab Hlambda]]]]].
    pose (Htot := thm_A_exceptional_total g Hgtype lambda Hexc).
    rewrite Hlambda, thm_Zvec_total_app,
      thm_Zvec_total_repeat, thm_Zvec_total_repeat in Htot.
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
      all : rewrite (thm_repeat_mul_0 _ _ Htot), <- thm_repeat_plus in Hlambda.
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
  Definition twovalA (a b : Z) (p q : nat) :=
    repeat a p ++ repeat b q.
  Theorem thm_twovalA_ntha :
    forall a b p q k lambda,
      2 <= k
      -> k < p
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
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
    unfold twovalA in H1.
    simpl tl in H1.
    assert (S (S p) = p + 2) as H7.
    { omega. }
    rewrite H7, thm_repeat_plus, <- app_assoc in H1.
    simpl_extra in H2.
    firstorder.
    simpl in H0.
    autorewrite with rewritelength rewritesome in H0.
    generalize H1, H9.
    rewrite (thm_hdn_tln Z p lambda) ; [| clear -H0 ; omega].
    set (lam1 := hdn p lambda).
    set (lam2 := tln p lambda).
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
    rewrite (thm_Zvec_leb_leb_eq _ _ H14 H11 H10).
    rewrite app_nth1.
    - generalize k, p, a.
      induction k0 ; destruct p0 ; simpl ; trivial.
    - autorewrite with rewritelength.
      apply lt_S_n, lt_S_n in H.
      assumption.
  Qed.
  (*Revise the proof of thm_twovalA_ntha to look more like thm_twovalA_nthb.*)
  Theorem thm_twovalA_nthb :
    forall a b p q k lambda,
      2 + p <= k
      -> k < p + q
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> nth k lambda b = b.
  Proof.
    unfold twovalA.
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
    rewrite thm_nth_tl_tl, thm_nth_app_repeat in *.
    exact (Z.le_antisymm _ _ Hupper Hlower).
    all : clear -H H0 ; omega.
  Qed.
  Theorem thm_twovalA_branching : (*Probably useless*)
    forall lambda a b p q,
      2 <= p
      -> 2 <= q
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> exists l0 l1 l2 l3 l4 l5,
           lambda = l0::l1::(repeat a (p - 2))
                      ++ l2::l3::(repeat b (q - 2))
                      ++ l4::l5::nil.
  Proof.
    intros lambda a b p q Hp Hq H.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b in H.
    autorewrite with rewritesome in H.
    destruct H as [[[[Hlength Hradl] Hradm] Hlm] Hml].
    unfold twovalA in Hlength.
    autorewrite with rewritelength in Hlength.
    assert (length lambda >= 6) as Hlength2.
    {
      rewrite Hlength.
      clear - Hp Hq Hlength. omega.
    }
    destruct lambda as [|l0 [|l1 lambda]] ; simpl in Hlength2 ; try omega.
    autorewrite with rewritelength rewritesome in Hlength.
    exists l0, l1.
    unfold twovalA in Hlm, Hml.
    assert (p = 2 + (p - 2)) as Hp2.
    { clear -Hp. omega. }
    assert (p = (p - 2) + 2) as Hp3.
    { clear -Hp. omega. }
    rewrite Hp2 in Hlm.
    rewrite Hp3 in Hml.
    rewrite thm_repeat_plus in Hlm, Hml.
    rewrite <- app_assoc in Hml.
    simpl_destruct Hlm as [_ [_ Hlm]].
    assert ((p - 2) <= length lambda) as Hp4.
    { clear -Hq Hlength. omega. }
    pose (Hlsplit := thm_hdn_tln _ _ _ Hp4).
    set (mu := hdn _ _) in *.
    set (nu := tln _ _) in *.
    rewrite Hlsplit in *.
    assert (length mu = length (repeat a (p - 2))) as Hmulength.
    {
      unfold mu.
      autorewrite with rewritelength.
      exact (Min.min_l _ _ Hp4).
    }
    rewrite (thm_Zvec_leb_app _ _ _ _ Hmulength) in Hlm.
    destruct Hlm as [Hlm1 Hlm2].
    simpl in Hml.
    rewrite (thm_Zvec_leb_app _ _ _ _ (eq_sym Hmulength)) in Hml.
    destruct Hml as [Hml1 Hml2].
    pose (Hmu := thm_Zvec_leb_leb_eq _ _ Hmulength Hlm1 Hml1).
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
    rewrite thm_repeat_plus in Hlm2, Hml2.
    simpl_destruct Hlm2 as [_ [_ Hlm2]].
    simpl_destruct Hml2 as [_ [_ Hml2]].
    simpl in Hlength.
    assert (q - 2 <= length nu) as Hq4.
    { clear - Hp Hq Hlength. omega. }
    pose (Hnsplit := thm_hdn_tln _ _ _ Hq4).
    set (rho := hdn _ _) in *.
    set (sigma := tln _ _) in *.
    rewrite Hnsplit in *.
    assert (length rho = length (repeat b (q - 2))) as Hrholength.
    {
      unfold rho.
      autorewrite with rewritelength.
      exact (Min.min_l _ _ Hq4).
    }
    rewrite (app_nil_end (repeat b (q - 2))) in Hlm2.
    rewrite (thm_Zvec_leb_app _ _ _ _ Hrholength) in Hlm2.
    destruct Hlm2 as [Hlm1 Hlm2].
    rewrite (thm_Zvec_leb_app _ _ _ _ (eq_sym Hrholength)) in Hml2.
    destruct Hml2 as [Hml1 Hml2].
    pose (Hrho := thm_Zvec_leb_leb_eq _ _ Hrholength Hlm1 Hml1).
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

  (*duA stands for "down-up for A-type reversed weights"
    namely starting from repeat a p ++ repeat b q with a<=b,
    decrement one entry and increment another one,
    to keep total = 0, namely keep a (radical) weight.
    Various indices correspond to which entry is increased:
    1 means an entry in repeat a p, 2 in repeat b q.
    If there are not enough entries do nothing.*)
  Definition d1u1A (a b : Z) (p q : nat) :=
    match p with
      | 0 => twovalA a b p q
      | 1 => twovalA a b p q
      | S (S p'') => (a-1)%Z::(repeat a p'') ++ (a+1)%Z::(repeat b q)
    end.
  Definition d1u2A (a b : Z) (p q : nat) :=
    match p with
      | 0 => twovalA a b p q
      | S p' => match q with
                  | 0 => twovalA a b p q
                  | S q' => (a-1)%Z::(repeat a p')
                                 ++ (repeat b q') ++ (b+1)%Z::nil
                end
    end.
  Definition d2u1A (a b : Z) (p q : nat) :=
    match p with
      | 0 => twovalA a b p q
      | S p' => match q with
                  | 0 => twovalA a b p q
                  | S q' => (repeat a p')
                              ++ (a+1)%Z::(b-1)%Z::(repeat b q')
                end
    end.
  Definition d2u2A (a b : Z) (p q : nat) :=
    match q with
      | 0 => twovalA a b p q
      | 1 => twovalA a b p q
      | S (S q'') => repeat a p ++ (b-1)%Z::(repeat b q'') ++ (b+1)%Z::nil
    end.
  Hint Rewrite
       thm_Zvec_total_app
       thm_Zvec_total_repeat
       thm_Z_of_nat_S
       Z.mul_add_distr_r
       Z.add_assoc
       Z.mul_1_l
       Z.mul_1_r
  : rewritetotal.
  Tactic Notation "simpl_total" :=
    repeat (simpl || autorewrite with rewritetotal).
  Tactic Notation "simpl_total" "in" hyp(H) :=
    repeat (simpl in H || autorewrite with rewritetotal in H).
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
                => try rewrite thm_hd_repeat
              | [ |- context[hd _ (_++_)]]
                => try rewrite thm_hd_app
              | [ |- context[last (repeat _ _)]]
                => try rewrite thm_last_repeat
              | [ |- context[if ?p=?0 then _ else _]]
                => (destruct p ; simpl ; firstorder) (*Possibly dangerous loop?*)
              | [ |- context[match ?p with 0 => _ | S _ => _ end]]
                => (destruct p ; simpl ; firstorder)
              | [ Htot : context[Zvec_total] |- context[Zvec_total]]
                => (simpl_total ; simpl_total in Htot ; try omega)
              | [ |- _] => (simpl ; try omega ; firstorder)
            end).
  Ltac tac_du fn :=
    unfold lie_is_radical_revwt_type ;
    intros a b p q ;
    autorewrite with rewritesome ;
    intros Ha Hb [Hinc Htot] ;
    unfold fn, twovalA in * ;
    tac_du_repeat.
  Theorem thm_d1u1A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (twovalA a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d1u1A a b p q) = true.
  Proof.
    tac_du d1u1A.
  Qed.
  Theorem thm_d1u2A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (twovalA a b p q) = true
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
      -> lie_is_radical_revwt_type lie_A_type (twovalA a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d2u1A a b p q) = true.
  Proof.
    tac_du d2u1A.
  Qed.
  Theorem thm_d2u2A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (twovalA a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d2u2A a b p q) = true.
  Proof.
    tac_du d2u2A.
  Qed.

  Theorem thm_d1u1A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (1 < p)%nat
      -> (0 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> Is_known_w0_branching_A_revwt lambda (d1u1A a b p q)
         \/ (nth 0 lambda a = a)
         \/ (nth (1 + p) lambda a = a).
  Proof.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b in *.
    intros.
    autorewrite with rewritesome in *.
    assert (lie_is_radical_revwt_type lie_A_type (d1u1A a b p q) = true) as H4.
    { apply thm_d1u1A_radical ; firstorder ; omega. }
    rewrite H4.
    autorewrite with rewritesome.
    destruct p as [|[|p]] ; try omega.
    firstorder.
    unfold twovalA in *.
    assert (nth 0 lambda a <= a)%Z as H9.
    {
      clear -H6.
      destruct lambda.
      - simpl ; omega.
      - unfold Zvec_short_allb in H6.
        simpl in *.
        autorewrite with rewritesome in *.
        firstorder.
    }
    destruct (Z_le_lt_eq_dec _ _ H9) as [Hhda|Hhda] ; [|firstorder].
    assert (a <= nth (3 + p) lambda a)%Z as H10.
    {
      clear - H3 H5.
      destruct lambda as [|x0 [|x1 lambda]] ; simpl ; try omega.
      simpl tl in *.
      assert (S p < length (repeat a (S (S p)) ++ repeat b q)
              /\ S p < length lambda) as [H1 H2].
      {
        autorewrite with rewritelength in *.
        firstorder.
      }
      pose (H6 := thm_Zvec_leb_nth (S p) _ lambda a a H1 H2 H5).
      clearbody H6.
      rewrite app_nth1, thm_nth_repeat1 in H6.
      exact H6.
      autorewrite with rewritelength.
      firstorder.
    }
    simpl add in *.
    destruct (Z_le_lt_eq_dec _ _ H10) as [Hap|Hap] ; [|firstorder].
    left.
    unfold d1u1A.
    repeat try split.
    - clear -H3.
      autorewrite with rewritelength in *.
      omega.
    - assumption.
    - destruct lambda ; [trivial|].
      simpl_extra.
      split.
      + clear -Hhda.
        simpl in Hhda.
        omega.
      + rewrite thm_repeat_fact1 in H6.
        simpl_destruct H6 as [_ H6].
        refine (thm_Zvec_leb_trans32 _ _ _ _ H6 _).
        autorewrite with rewritelength ; omega.
        rewrite thm_Zvec_leb_app.
        split.
        * apply thm_Zvec_leb_refl.
        * simpl_extra.
          split.
          omega.
          apply thm_Zvec_leb_refl.
        * trivial.
    - destruct lambda as [|z [|z0 lambda]]; trivial.
      simpl in H10, Hap.
      simpl tl in *.
      assert (S p < length lambda) as Hl.
      {
        clear -H3.
        simpl_length in H3.
        omega.
      }
      destruct (nth_split lambda a Hl) as [l1 [l2 [H11 H12]]].
      rewrite H11.
      rewrite H11 in H5, H6, H3, H9, H8, Hl, H10, Hhda.
      rewrite app_comm_cons.
      rewrite thm_repeat_fact1 in H5, H7.
      rewrite thm_Zvec_leb_app in *.
      firstorder.
      all : try solve [clear -H3 H12 ; autorewrite with rewritelength in *; omega].
      + refine (thm_Zvec_leb_trans32 _ _ _ _ _ H5).
        clear -H3 H12 ; autorewrite with rewritelength in *; omega.
        simpl.
        rewrite thm_Zvec_leb_refl.
        simpl_extra.
        omega.
      + simpl_extra.
        split.
        * omega.
        * clear -H13.
          simpl_extra in H13.
          firstorder.
  Qed.
  Theorem thm_d1u2A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (0 < p)%nat
      -> (0 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> Is_known_w0_branching_A_revwt lambda (d1u2A a b p q)
         \/ (nth 0 lambda a = a)
         \/ (nth (1 + p + q) lambda b = b).
  Proof.
    admit.
  Admitted.
  Theorem thm_d2u1A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (0 < p)%nat
      -> (0 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> Is_known_w0_branching_A_revwt lambda (d2u1A a b p q)
         \/ (nth p lambda b = b)
         \/ (nth (1 + p) lambda a = a).
  Proof.
    admit.
  Admitted.
  Theorem thm_d2u2A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (0 < p)%nat
      -> (1 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> Is_known_w0_branching_A_revwt lambda (d2u2A a b p q)
         \/ (nth p lambda b = b)
         \/ (nth (1 + p + q) lambda b = b).
  Proof.
    admit.
  Admitted.

  Theorem thm_d1u1A_not_exceptional :
    forall a b p q g,
      lie_algebra_type g = lie_A_type
      -> 1 < p
      -> ~ (Is_exceptional_revwt_alg g (d1u1A a b p q)).
  Proof.
    admit.
  Admitted.
  (*TODO: also do d1u2 etc.*)

  Theorem thm_duA :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           lie_is_radical_revwt_alg g lambda = true
           -> forall a b p q,
                (a < 0)%Z
                -> (0 < b)%Z
                -> 0 < p
                -> 0 < q
                -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
                -> (exists mu,
                      Is_known_w0_branching_A_revwt lambda mu
                      /\ ~ (Is_exceptional_revwt_alg g mu))
                   (* (Is_known_w0_branching_A_revwt lambda (d1u1A a b p q)
          /\ (2 <= p))
         \/ Is_known_w0_branching_A_revwt lambda (d1u2A a b p q)
         \/ Is_known_w0_branching_A_revwt lambda (d2u1A a b p q)
         \/ (Is_known_w0_branching_A_revwt lambda (d2u2A a b p q)
             /\ (2 <= q))*)
                   \/ (nth 0 lambda a = a /\ nth p lambda b = b)
                   \/ (nth (1 + p) lambda a = a /\ nth (1 + p + q) lambda b = b).
  Proof.
    admit.
  Admitted.
  Theorem thm_A_impossible_total: (*TODO: actually wrong: misses some cases*)
    forall a b p q lambda,
      lie_is_radical_revwt_type lie_A_type lambda = true
      -> (Z.of_nat p * a + Z.of_nat q * b = 0)%Z
      -> (nth 0 lambda a = a /\ nth p lambda b = b)
         \/ (nth (1 + p) lambda a = a /\ nth (1 + p + q) lambda b = b)
      -> False.
  Proof.
    admit.
  Admitted.

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
        unfold lie_is_radical_revwt_alg in Hrad.
        autorewrite with rewritesome in Hrad.
        destruct Hrad as [Hlength Hrad].
        simpl in Hlength.
        assert (length lambda >= 2) as Hl2.
        { rewrite Hlength. omega. }
        assert (S (S n) > 0) as Hn.
        { firstorder. }
        pose (Hmu := thm_An_branching_fact1 _ Hrad Hl2).
        set (mu := tmp_A_get lambda) in Hmu.
        unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b in Hmu.
        autorewrite with rewritesome in Hmu.
        destruct Hmu as [[[[Hlenlm Hradl] Hradm] Hllebm] Hmlebtltl].
        pose (g := lie_A (exist (fun n : nat => n > 0) (S (S (S (S n)))) Hn2)).
        pose (h := lie_A (exist (fun n : nat => n > 0) (S (S n)) Hn)).
        assert (lie_is_radical_revwt_alg h mu = true) as Hradmg.
        {
          unfold lie_is_radical_revwt_alg.
          simpl.
          rewrite Hlenlm in Hlength.
          autorewrite with rewritesome in Hlength.
          simpl in Hradm.
          rewrite Hradm.
          autorewrite with rewritesome.
          trivial.
        }
        destruct (IHn Hn mu Hradmg) as [H|H].
        {
          (*mu is exceptional*)
          simpl in H.
          destruct H as [i [m [H Hmu]]].
          unfold is_exceptional_multiplier in H.
          admit.
        }
        admit.
  Admitted.

End theorems_for_A_type.
