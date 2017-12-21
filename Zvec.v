Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Our files*)
Require Import Rewriting.
Require Import ListExtras.
Open Scope nat_scope.

(*TODO: look up split, combine*)
(*TODO: look up "fold"*)

Section functions.
  Fixpoint Zvec_total lambda :=
    match lambda with
      | nil => 0%Z
      | a::lambda' => (a + Zvec_total lambda')%Z
    end.
  Fixpoint Zvec_allb (testb : Z -> bool) lambda :=
    match lambda with
      | nil => true
      | a::lambda' => (testb a) && (Zvec_allb testb lambda')
    end.
  Fixpoint Zvec_short_allb (testb : Z -> Z -> bool) lambda mu :=
    match lambda with
      | nil => true
      | a::lambda' => match mu with
                        | nil => true
                        | b::mu' => (testb a b)
                                      && (Zvec_short_allb testb lambda' mu')
                      end
    end.
  Fixpoint Zvec_short_map_zip (f : Z -> Z -> Z) lambda mu :=
    match lambda with
      | nil => nil
      | a::lambda' => match mu with
                        | nil => nil
                        | b::mu' => (f a b)::(Zvec_short_map_zip f lambda' mu')
                      end
    end.
  Fixpoint Zvec_long_map_zip (f : Z -> Z -> Z) lambda mu :=
    match lambda with
      | nil => mu
      | a::lambda' => match mu with
                        | nil => lambda
                        | b::mu' => (f a b)::(Zvec_long_map_zip f lambda' mu')
                      end
    end.
  Definition Zvec_mul m := map (Z.mul m).
  Definition Zvec_short_sub := Zvec_short_map_zip Z.sub.
  Definition Zvec_short_max := Zvec_short_map_zip Z.max.
  Definition Zvec_long_min := Zvec_long_map_zip Z.min.
  Definition Zvec_nondecb lambda := Zvec_short_allb Z.leb lambda (tl lambda).
  Definition Zvec_nonincb lambda := Zvec_short_allb Z.leb (tl lambda) lambda.
  Definition Zvec_all_nonnegb := Zvec_allb (Z.leb 0).
End functions.

Section Zhelpers.
  Theorem thm_gcd_pos :
    forall m n, (m >= 0 -> n > 0 -> Z.gcd m n > 0)%Z.
  Proof.
    intros.
    destruct m ; destruct n.
    all : simpl.
    all : try apply Zgt_pos_0.
    trivial.
  Qed.
  Theorem thm_gcd_nat1 :
    forall i n, (Z.gcd (Z.of_nat i) (1 + Z.of_nat n) > 0)%Z.
  Proof.
    intros.
    apply thm_gcd_pos ; omega.
  Qed.
  Theorem thm_mul_nonpos_cancel_l :
    forall n m : Z, (0 < n)%Z -> (n * m <= 0)%Z <-> (m <= 0)%Z.
  Proof.
    intros.
    rewrite Z.opp_le_mono, <- Z.mul_opp_r.
    simpl.
    rewrite (Z.mul_nonneg_cancel_l _ _ H).
    omega.
  Qed.
  Theorem thm_repeat_mul_0 :
    forall a p, (Z.of_nat p * a = 0 -> repeat a p = repeat 0 p)%Z.
  Proof.
    intros a p H.
    rewrite Z.eq_mul_0 in H.
    destruct H as [H|H].
    - assert (p = 0) as H0.
      { omega. }
      rewrite H0.
      simpl.
      trivial.
    - rewrite H.
      trivial.
  Qed.
  Theorem thm_0_eq_Z_of_nat :
    forall n, 0%Z = Z.of_nat n <-> 0 = n.
  Proof.
    firstorder ; omega.
  Qed.
  Theorem thm_0_lt_Z_of_nat :
    forall n, (0 < Z.of_nat n)%Z <-> 0 < n.
  Proof.
    firstorder ; omega.
  Qed.
End Zhelpers.

Section theorems.
  Theorem thm_Zvec_leb_refl :
    forall mu, Zvec_short_allb Z.leb mu mu = true.
  Proof.
    induction mu ; simpl.
    - firstorder.
    - rewrite IHmu, Z.leb_refl ; firstorder.
  Qed.
  Theorem thm_Zvec_leb_trans12 :
    forall lambda mu nu,
      length lambda <= length mu
      -> Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb mu nu = true
      -> Zvec_short_allb Z.leb lambda nu = true.
  Proof.
    induction lambda.
    - intros mu nu Hlength Hlm Hmn.
      destruct nu.
      + destruct mu ; firstorder.
      + simpl in Hlength ; firstorder.
    - intros mu nu Hlength Hlm Hmn.
      destruct mu ; simpl in Hlength.
      + firstorder.
      + destruct nu.
        * firstorder.
        * simpl_destruct Hlm as [H1 Hlm].
          simpl_destruct Hmn as [H2 Hmn].
          pose (H3 := Z.le_trans _ _ _ H1 H2).
          rewrite Zle_is_le_bool in H3.
          simpl.
          firstorder.
  Qed.
  Theorem thm_Zvec_leb_trans32 :
    forall nu lambda mu,
      length nu <= length mu
      -> Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb mu nu = true
      -> Zvec_short_allb Z.leb lambda nu = true.
  Proof.
    induction nu.
    - intros lambda mu Hlength Hlm Hmn.
      destruct lambda.
      + destruct mu ; firstorder.
      + simpl in Hlength ; firstorder.
    - intros lambda mu Hlength Hlm Hmn.
      destruct mu ; simpl in Hlength.
      + firstorder.
      + destruct lambda.
        * firstorder.
        * simpl_destruct Hlm as [H1 Hlm].
          simpl_destruct Hmn as [H2 Hmn].
          pose (H3 := Z.le_trans _ _ _ H1 H2).
          rewrite Zle_is_le_bool in H3.
          simpl in *.
          autorewrite with rewritesome in *.
          split ; [assumption|].
          exact (IHnu lambda mu Hlength Hlm Hmn).
  Qed.
  Theorem thm_Zvec_leb_app :
    forall mu1 mu2 nu1 nu2,
      length mu1 = length nu1
      -> (Zvec_short_allb Z.leb (mu1 ++ mu2) (nu1 ++ nu2) = true
          <-> Zvec_short_allb Z.leb mu1 nu1 = true
              /\ Zvec_short_allb Z.leb mu2 nu2 = true).
  Proof.
    induction mu1 as [|a1 mu1].
    - destruct nu1.
      + firstorder.
      + simpl. firstorder.
    - destruct nu1 as [|x1 nu1].
      + simpl. firstorder.
      + intros nu2 Hlength.
        simpl_extra.
        simpl_extra in Hlength.
        destruct (IHmu1 mu2 nu1 nu2 Hlength) as [H2 H3].
        split ; firstorder.
  Qed.
  Ltac tac_nondecb lambda :=
    destruct lambda ;
    unfold Zvec_nondecb ;
    simpl_extra ;
    firstorder.
  Theorem thm_Zvec_nondecb_01_geq :
    forall a b lambda,
      Zvec_nondecb (a::b::lambda) = true
      -> (a <= b)%Z.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_cons :
    forall a lambda,
      Zvec_nondecb (a::lambda) = true
      -> Zvec_nondecb lambda = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_skip :
    forall a b lambda,
      Zvec_nondecb (a::b::lambda) = true
      -> Zvec_nondecb (a::lambda) = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_join :
    forall a lambda,
      (a <= hd a lambda)%Z
      -> Zvec_nondecb (lambda) = true
      -> Zvec_nondecb (a::lambda) = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_join2 :
    forall a b lambda,
      (a <= b)%Z
      -> Zvec_nondecb (b::lambda) = true
      -> Zvec_nondecb (a::b::lambda) = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_join3 :
    forall a b c lambda,
      (a <= b)%Z
      -> (b <= c)%Z
      -> Zvec_nondecb (a::c::lambda) = true
      -> Zvec_nondecb (a::b::c::lambda) = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_app :
    forall lambda mu,
      Zvec_nondecb (lambda++mu) = true
      -> Zvec_nondecb lambda = true
         /\ Zvec_nondecb mu = true.
  Proof.
    destruct lambda as [|a lambda].
    - simpl ; firstorder.
    - induction lambda as [|b lambda].
      + simpl ; firstorder.
        destruct mu.
        * firstorder.
        * exact (thm_Zvec_nondecb_cons _ _ H).
      + intros mu H.
        pose (H0 := IHlambda mu (thm_Zvec_nondecb_skip _ _ _ H)).
        firstorder.
        unfold Zvec_nondecb in H.
        simpl_destruct H as [Hab H].
        destruct lambda as [|c lambda].
        * unfold Zvec_nondecb ; simpl.
          rewrite (Zle_imp_le_bool _ _ Hab).
          trivial.
        * simpl_destruct H as [Hbc H].
          exact (thm_Zvec_nondecb_join3 _ _ _ _ Hab Hbc H0).
  Qed.
  Theorem thm_Zvec_nondecb_app_hd :
    forall a lambda b mu,
      Zvec_nondecb (a::lambda++(b::mu)) = true -> (a <= b)%Z.
  Proof.
    intros a lambda b mu H.
    unfold Zvec_nondecb in H.
    induction lambda.
    - simpl_extra in H.
      firstorder.
    - refine (IHlambda _).
      destruct lambda ;
        simpl ;
        simpl_destruct H as [H [H0 H1]] ;
        rewrite (Zle_imp_le_bool _ _ (Zle_trans _ _ _ H H0)) ;
        firstorder.
  Qed.
  Theorem thm_Zvec_nondecb_app2 :
    forall lambda mu,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb mu = true
      -> match mu with
           | nil => True
           | a::mu' => (last lambda a <= a)%Z
         end
      -> Zvec_nondecb (lambda++mu) = true.
  Proof.
    destruct mu as [|z mu].
    - rewrite app_nil_r.
      trivial.
    - simpl.
      induction lambda as [|a lambda].
      + trivial.
      + intros Hal Hzm Hlz.
        destruct lambda as [|b lambda] ; simpl.
        * simpl in Hlz.
          exact (thm_Zvec_nondecb_join2 _ _ _ Hlz Hzm).
        * refine (thm_Zvec_nondecb_join2
                    a b _ (thm_Zvec_nondecb_01_geq _ _ _ Hal) _).
          simpl in IHlambda.
          simpl in Hlz.
          exact (IHlambda (thm_Zvec_nondecb_cons _ _ Hal) Hzm Hlz).
  Qed.
  Theorem thm_Zvec_nondecb_app_iff :
    forall lambda mu,
      Zvec_nondecb (lambda++mu) = true
      <-> Zvec_nondecb lambda = true
          /\ Zvec_nondecb mu = true
          /\ match mu with
               | nil => True
               | a::mu' => (last lambda a <= a)%Z
             end.
  Proof.
    split.
    - intros H.
      pose (H0 := thm_Zvec_nondecb_app _ _ H).
      firstorder.
      destruct mu ; trivial.
      destruct lambda as [|a lambda].
      + simpl ; omega.
      + assert (a::lambda <> nil) as H2.
        { discriminate. }
        rewrite (app_removelast_last z H2) in *.
        rewrite thm_last_app.
        simpl in *.
        rewrite <- app_assoc in H.
        pose (H3 := thm_Zvec_nondecb_app _ _ H).
        destruct H3 as [H3 H4].
        exact (thm_Zvec_nondecb_app_hd _ _ _ _ H4).
    - pose (H := thm_Zvec_nondecb_app2 lambda mu).
      firstorder.
  Qed.
  Theorem thm_Zvec_total_app :
    forall lambda mu,
      Zvec_total (lambda++mu)
      = (Zvec_total lambda + Zvec_total mu)%Z.
  Proof.
    induction lambda ; simpl.
    - trivial.
    - intros.
      rewrite (IHlambda mu).
      exact (Zplus_assoc _ _ _).
  Qed.
  Theorem thm_Zvec_nondecb_total_app :
    forall lambda mu,
      Zvec_nondecb (lambda++mu) = true
      -> Zvec_total (lambda++mu) = 0%Z
      -> (Zvec_total lambda <= 0)%Z
         /\ (Zvec_total mu >= 0)%Z.
  Proof.
    intros lambda mu H Htot.
    assert (Zvec_total lambda <= 0 \/ 0 <= Zvec_total mu)%Z as Hor.
    {
      pose (H0 := thm_Zvec_nondecb_app _ _ H).
      destruct H0 as [H0 H1].
      destruct mu as [|a mu].
      - right ; firstorder.
      - destruct (Z_lt_le_dec a 0) as [H2|H2].
        + left.
          assert (Zvec_allb (Z.gtb 0) lambda = true) as H3.
          {
            generalize lambda as lambda0, H.
            induction lambda0.
            - unfold Zvec_nondecb ; simpl ; firstorder.
            - simpl.
              intros H3.
              rewrite (IHlambda0 (thm_Zvec_nondecb_cons _ _ H3)).
              pose (H4 := thm_Zvec_nondecb_app_hd _ _ _ _ H3).
              pose (H5 := Z.le_lt_trans _ _ _ H4 H2).
              rewrite <- Z.ltb_lt, <- Z.gtb_ltb in H5.
              rewrite H5.
              trivial.
          }
          assert (forall lambda0,
                    Zvec_allb (Z.gtb 0) lambda0 = true
                    -> Zvec_total lambda0 <= 0)%Z as H4.
          {
            induction lambda0.
            - simpl ; firstorder.
            - simpl_extra.
              firstorder.
              rewrite Z.gtb_lt in H4.
              omega.
          }
          exact (H4 _ H3).
        + right.
          generalize mu as mu0, a as a0, H2, H1.
          induction mu0.
          * unfold Zvec_total ; simpl ; firstorder.
          * intros a1 Ha1 H3.
            pose (H4 := thm_Zvec_nondecb_cons _ _ H3).
            clearbody H4.
            unfold Zvec_nondecb in H3.
            simpl_destruct H3 as [Ha10 H3].
            simpl in IHmu0.
            simpl.
            pose (H5 := (IHmu0 _ (Z.le_trans _ _ _ Ha1 Ha10) H4)).
            omega.
    }
    rewrite (thm_Zvec_total_app _ _) in Htot.
    destruct Hor as [H0|H0] ; omega.
  Qed.
  Theorem thm_Zvec_total_mrev:
    forall lambda,
      (Zvec_total (rev (map Z.opp lambda))
       = - Zvec_total lambda)%Z.
  Proof.
    induction lambda.
    - trivial.
    - simpl.
      rewrite thm_Zvec_total_app, IHlambda.
      simpl.
      omega.
  Qed.
  Theorem thm_Zvec_nondecb_fact1 :
    forall a b lambda,
      (0 <= b)%Z
      -> Zvec_nondecb (a::b::lambda) = true
      -> Zvec_allb (Z.leb 0%Z) lambda = true.
  Proof.
    unfold Zvec_nondecb.
    simpl.
    intros a b lambda H1 H2.
    simpl_destruct H2 as [H2 H3].
    induction lambda.
    - simpl ; trivial.
    - simpl_extra.
      simpl_destruct H3 as [H3 H4].
      split.
      + exact (Z.le_trans _ _ _ H1 H3).
      + refine (IHlambda _).
        simpl in H4.
        generalize H4.
        destruct lambda ; firstorder.
        simpl_extra.
        simpl_extra in H0.
        firstorder.
  Qed.
  Theorem thm_Zvec_nondecb_fact2 :
    forall a b lambda,
      (0 <= b)%Z
      -> Zvec_nondecb (a::b::lambda) = true
      -> (Zvec_total lambda >= 0)%Z.
  Proof.
    unfold Zvec_nondecb.
    simpl.
    intros a b lambda H1 H2.
    generalize lambda as lambda0, (thm_Zvec_nondecb_fact1 a b lambda H1 H2).
    induction lambda0.
    - unfold Zvec_total ; firstorder.
    - simpl_extra.
      firstorder.
  Qed.
  Theorem thm_Zvec_nondecb_fact3 :
    forall a b lambda,
      Zvec_nondecb (a::b::lambda) = true
      -> Zvec_short_allb Z.leb (a::b::lambda) lambda = true.
  Proof.
    intros a b lambda Hab.
    pose (Hb := thm_Zvec_nondecb_cons a (b::lambda) Hab).
    unfold Zvec_nondecb, tl in Hab.
    unfold Zvec_nondecb, tl in Hb.
    refine (thm_Zvec_leb_trans32 _ _ _ _ Hab Hb).
    simpl.
    omega.
  Qed.
End theorems.

Section more_list_thm.
  Theorem thm_Zvec_nondecb_mrev :
    forall lambda,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb (rev (map Z.opp lambda)) = true.
  Proof.
    induction lambda.
    - trivial.
    - simpl.
      intros Hal.
      rewrite thm_Zvec_nondecb_app_iff.
      repeat try split.
      + exact (IHlambda (thm_Zvec_nondecb_cons _ _ Hal)).
      + rewrite thm_last_rev.
        destruct lambda ; simpl.
        * omega.
        * unfold Zvec_nondecb in Hal.
          simpl_destruct Hal as [Haz _].
          omega.
  Qed.
  Theorem thm_Zvec_mrev_inverse :
    forall l, l = map Z.opp (rev (rev (map Z.opp l))).
  Proof.
    intros l.
    rewrite rev_involutive, map_map.
    induction l.
    - trivial.
    - simpl.
      rewrite Z.opp_involutive, <- IHl.
      trivial.
  Qed.
  Theorem thm_Zvec_leb_mrev :
    forall lambda mu : list Z,
      length lambda = length mu
      -> Zvec_short_allb Z.leb mu lambda = true
      -> Zvec_short_allb
           Z.leb (rev (map Z.opp lambda)) (rev (map Z.opp mu)) = true.
  Proof.
    intros lambda mu.
    set (rlambda := rev (map Z.opp lambda)).
    set (rmu := rev (map Z.opp mu)).
    assert (lambda = map Z.opp (rev rlambda)) as Hlambda.
    { apply thm_Zvec_mrev_inverse. }
    assert (mu = map Z.opp (rev rmu)) as Hmu.
    { apply thm_Zvec_mrev_inverse. }
    rewrite Hlambda, Hmu.
    tac_length.
    generalize rlambda, rmu.
    clear.
    induction rlambda.
    - trivial.
    - destruct rmu; simpl.
      + firstorder.
      + simpl_extra.
        intros Hlength H.
        assert (length (map Z.opp (rev rmu))
                = length (map Z.opp (rev rlambda)))
          as Hlength2.
        { tac_length. }
        rewrite thm_Zvec_leb_app in H.
        simpl_destruct H as [H1 H2].
        simpl_extra in H2.
        split.
        * clear -H2. omega.
        * refine (IHrlambda rmu Hlength H1).
        * exact Hlength2.
  Qed.
  Theorem thm_Zvec_leb_mrev1 :
    forall lambda mu : list Z,
      length lambda = S (S (length mu))
      -> Zvec_short_allb Z.leb mu (tl (tl lambda)) = true
      -> Zvec_short_allb
           Z.leb (rev (map Z.opp lambda)) (rev (map Z.opp mu)) = true.
  Proof.
    destruct lambda as [|a [|b lambda]] ; simpl ; firstorder.
    simpl_extra in H.
    rewrite <- app_assoc ; simpl.
    rewrite (app_nil_end (rev (map Z.opp mu))).
    rewrite thm_Zvec_leb_app.
    - simpl_extra.
      apply thm_Zvec_leb_mrev ; trivial.
    - tac_length.
  Qed.
  Theorem thm_Zvec_leb_mrev2 :
    forall lambda mu : list Z,
      length lambda = S (S (length mu))
      -> Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb
           Z.leb (rev (map Z.opp mu))
           (tl (tl (rev (map Z.opp lambda)))) = true.
  Proof.
    intros lambda mu Hlength.
    rewrite thm_tl_rev, thm_removelast_map.
    rewrite thm_tl_rev, thm_removelast_map.
    assert (lambda <> nil) as H ; tac_length.
    rewrite (app_removelast_last 0%Z H) at 1.
    set (a := last lambda 0%Z).
    assert (removelast lambda <> nil) as H0 ; tac_length.
    rewrite (app_removelast_last 0%Z H0) at 1.
    set (b := last (removelast lambda) 0%Z).
    set (l := removelast (removelast lambda)).
    rewrite <- app_assoc.
    simpl.
    rewrite (app_nil_end mu) at 1.
    intros H1.
    assert (length mu = length l) as H2 ; unfold l ; tac_length.
    refine (thm_Zvec_leb_mrev mu l _ _).
    - assumption.
    - rewrite thm_Zvec_leb_app in H1 ; firstorder.
  Qed.
  Theorem thm_Zvec_total_mul :
    forall m lambda,
      (Zvec_total (Zvec_mul m lambda) = m * Zvec_total lambda)%Z.
  Proof.
    unfold Zvec_mul.
    induction lambda ; simpl.
    - omega.
    - rewrite IHlambda.
      rewrite Z.mul_add_distr_l.
      trivial.
  Qed.
  Theorem thm_Z_of_nat_S :
    forall n, Z.of_nat (S n) = (1 + Z.of_nat n)%Z.
  Proof.
    intros.
    rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    trivial.
  Qed.
  Theorem thm_Zvec_total_repeat :
    forall m a,
      (Zvec_total (repeat a m) = (Z.of_nat m) * a)%Z.
  Proof.
    intros.
    induction m.
    - trivial.
    - simpl repeat.
      simpl Zvec_total.
      rewrite IHm, thm_Z_of_nat_S.
      rewrite Z.mul_add_distr_r.
      omega.
  Qed.
  Theorem thm_Zvec_nondecb_repeat :
    forall a n, Zvec_nondecb (repeat a n) = true.
  Proof.
    destruct n ; simpl ; firstorder.
    induction n ; simpl ; firstorder.
    apply thm_Zvec_nondecb_join2.
    omega.
    assumption.
  Qed.
  (*Here Zvec_short_map_zip is used to pick the first (length mu) components of lambda*)
  Theorem thm_Zvec_leb_total :
    forall mu lambda,
      length mu <= length lambda
      -> Zvec_short_allb Z.leb lambda mu = true
      -> (Zvec_total (Zvec_short_map_zip (fun _ a => a) mu lambda)
          <= Zvec_total mu)%Z.
  Proof.
    induction mu.
    - simpl ; firstorder.
    - destruct lambda.
      + simpl ; firstorder.
      + simpl.
        intros H H0.
        simpl_destruct H0 as [H0 H1].
        pose (H2 := (IHmu _ (le_S_n _ _ H) H1)).
        omega.
  Qed.
  Theorem thm_Zvec_leb_eqb_tot :
    forall lambda mu,
      length mu <= length lambda
      -> Zvec_short_allb Z.leb lambda mu = true
      -> (Zvec_short_allb Z.eqb lambda mu = true
          <-> Zvec_total mu
              = Zvec_total (Zvec_short_map_zip (fun _ a => a) mu lambda)).
  Proof.
    intros lambda mu Hlength Hleb.
    split.
    - generalize mu as mu0, lambda as lambda0, Hlength.
      induction mu0.
      + simpl ; firstorder.
      + destruct lambda0.
        * simpl ; firstorder.
        * simpl.
          intros H H0.
          simpl_destruct H0 as [H0 H1].
          rewrite H0.
          rewrite <- (IHmu0 _ (le_S_n _ _ H) H1).
          trivial.
    - generalize mu as mu0, lambda as lambda0, Hlength, Hleb.
      induction mu0.
      + simpl ; firstorder.
        destruct lambda0 ; firstorder.
      + destruct lambda0.
        * simpl ; firstorder.
        * simpl.
          intros H H0 H2.
          simpl_destruct H0 as [H0 H1].
          pose (H3 := le_S_n _ _ H).
          pose (H4 := thm_Zvec_leb_total _ _ H3 H1).
          simpl_extra.
          split ; [|refine (IHmu0 _ H3 H1 _)] ; omega.
  Qed.
  Theorem thm_Zvec_nondecb_partialsum :
    (forall lambda mu,
       Zvec_nondecb lambda = true
       -> Zvec_total lambda = 0
       -> Zvec_total (Zvec_short_map_zip (fun _ a : Z => a) mu lambda) <= 0)%Z.
  Proof.
    pose (tmp := (fix tmp (lambda mu : list Z) :=
                    match mu with
                      | nil => lambda
                      | _::mu' => match lambda with
                                    | nil => nil
                                    | _::lambda' => tmp lambda' mu'
                                  end
                    end)).
    assert (forall mu lambda,
              (Zvec_short_map_zip (fun _ a : Z => a) mu lambda)++(tmp lambda mu)
              = lambda) as H.
    {
      induction mu ; simpl.
      - destruct lambda ; simpl ; trivial.
      - destruct lambda ; simpl ; trivial.
        rewrite (IHmu lambda).
        trivial.
    }
    intros lambda mu Hnondec Htot.
    pose (thm1 :=
            thm_Zvec_nondecb_total_app
              (Zvec_short_map_zip (fun _ a : Z => a) mu lambda)
              (tmp lambda mu)).
    rewrite H in thm1.
    firstorder.
  Qed.
  Theorem thm_Zvec_mul_0 :
    forall l, Zvec_mul 0%Z l = repeat 0%Z (length l).
  Proof.
    induction l.
    - trivial.
    - simpl ; rewrite IHl ; firstorder.
  Qed.
  Theorem thm_Zvec_leb_leb_eq :
    forall lambda mu,
      length lambda = length mu
      -> Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb mu lambda = true
      -> lambda = mu.
  Proof.
    induction lambda.
    - destruct mu.
      + trivial.
      + simpl ; intros H ; discriminate H.
    - destruct mu.
      + simpl ; intros H ; discriminate H.
      + simpl_extra.
        firstorder.
  Qed.
  Theorem thm_Zvec_leb_nth :
    forall n lambda mu a b,
      n < length lambda
      -> n < length mu
      -> Zvec_short_allb Z.leb lambda mu = true
      -> (nth n lambda a <= nth n mu b)%Z.
  Proof.
    induction n.
    all : destruct lambda, mu ; simpl in * ; firstorder ; try omega.
    all : autorewrite with rewritesome in *.
    all : try (apply IHn ; try omega).
    all : firstorder.
  Qed.
  Theorem thm_Zvec_nondecb_nth :
    forall lambda p r a b,
      Zvec_nondecb lambda = true
      -> p < r
      -> r < length lambda
      -> (nth p lambda a <= nth r lambda b)%Z.
  Proof.
    intros.
    destruct (nth_split lambda b H1) as [l2 [l5 [H2 H5]]].
    rewrite H2 at 1.
    rewrite app_nth1 at 1.
    rewrite <- H5 in H0.
    destruct (nth_split l2 a H0) as [l3 [l4 [H3 H4]]].
    set (aa := nth p _ _) in *.
    set (bb := nth r _ _) in *.
    rewrite H2, H3, <- app_assoc in H.
    destruct (thm_Zvec_nondecb_app _ _ H) as [_ H6].
    simpl in H6.
    exact (thm_Zvec_nondecb_app_hd _ _ _ _ H6).
    omega.
  Qed.
End more_list_thm.