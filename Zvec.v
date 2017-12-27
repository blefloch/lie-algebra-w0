Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Our files*)
Require Import Tools.
Require Import ListExtras.
Open Scope nat_scope.

(*TODO: look up split, combine*)
(*TODO: look up "fold"*)

Section functions.
  Fixpoint total lambda :=
    match lambda with
      | nil => 0%Z
      | a::lambda' => (a + total lambda')%Z
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
  Definition Zvec_all_nonnegb := forallb (Z.leb 0).
End functions.

Section Zhelpers.
  Theorem thm_Z_of_nat_S :
    forall n, Z.of_nat (S n) = (1 + Z.of_nat n)%Z.
  Proof.
    intros.
    rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    trivial.
  Qed.
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

Section even.
  Theorem thm_Odd_even_false :
    forall n, Nat.Odd n -> Nat.even n = false.
  Proof.
    intros n H.
    rewrite <- Nat.odd_spec in H.
    rewrite <- Nat.negb_odd, H.
    trivial.
  Qed.
  Theorem thm_mul_2_l_even : forall n, Nat.even (2 * n) = true.
  Proof.
    intros n.
    rewrite Nat.even_spec.
    exists n.
    intuition.
  Qed.
  Theorem thm_Z_even_pos :
    forall a, Z.even a = true -> (0 < a)%Z -> (2 <= a)%Z.
  Proof.
    intros a Heven.
    assert (1 <= a -> 1 < a)%Z.
    {
      intros H.
      destruct (Zle_lt_or_eq _ _ H) as [H0|H0].
      - assumption.
      - rewrite <- H0 in *.
        discriminate Heven.
    }
    omega.
  Qed.
  Theorem thm_Zeven_pos_explicit_1 :
    forall a : positive,
      Z.even (Z.pos (a~1)) = false.
  Proof.
    trivial.
  Qed.
  Theorem thm_Zeven_pos_explicit_0 :
    forall a : positive,
      Z.even (Z.pos (a~0)) = true.
  Proof.
    trivial.
  Qed.
  Theorem thm_Zeven_neg_explicit_1 :
    forall a : positive,
      Z.even (Z.neg (a~1)) = false.
  Proof.
    trivial.
  Qed.
  Theorem thm_Zeven_neg_explicit_0 :
    forall a : positive,
      Z.even (Z.neg (a~0)) = true.
  Proof.
    trivial.
  Qed.
  Theorem thm_Zeven_mul_2_l :
    forall n, Z.even (2 * n) = true.
  Proof.
    intro n ; case n ; simpl ; tauto.
  Qed.
  Theorem thm_Zeven_mul_2_r :
    forall n, Z.even (n * 2) = true.
  Proof.
    intros.
    rewrite Z.mul_comm.
    exact (thm_Zeven_mul_2_l _).
  Qed.
  Theorem thm_even_between_0_and_2 :
    forall a, Z.Even a -> (0 <= a)%Z -> (a <= 2)%Z -> a = 0%Z \/ a = 2%Z.
  Proof.
    intros a HaEven Hamin Hamax.
    destruct HaEven as [a2 Ha2].
    rewrite Ha2 in *.
    assert (0 <= a2 <= 1)%Z as H3.
    { omega. }
    rewrite Z.lt_eq_cases, Z.lt_eq_cases in H3.
    destruct H3 as [[H3|H3] [H4|H4]].
    all : try omega.
  Qed.
  Theorem thm_Z_of_nat_even :
    forall n, Z.even (Z.of_nat n) = Nat.even n.
  Proof.
    induction n.
    - trivial.
    - rewrite Nat.even_succ, <- Nat.negb_even, <- IHn.
      refine (negb_sym _ _ _).
      rewrite Z.negb_even, <- Z.odd_succ, Nat2Z.inj_succ.
      trivial.
  Qed.
End even.

Hint Rewrite
     Z.even_add
     Z.even_sub
     Z.even_opp
     Z.even_0
     Z.even_1
     thm_Zeven_pos_explicit_1
     thm_Zeven_pos_explicit_0
     thm_Zeven_neg_explicit_1
     thm_Zeven_neg_explicit_0
     thm_Zeven_mul_2_l
     thm_Zeven_mul_2_r
: rewriteeven.

Section misc.
  Theorem thm_Zvec_mul_0 :
    forall l, Zvec_mul 0%Z l = repeat 0%Z (length l).
  Proof.
    induction l.
    - trivial.
    - simpl ; rewrite IHl ; firstorder.
  Qed.
  Theorem thm_Zvec_mul_1 :
    forall lambda, Zvec_mul 1 lambda = lambda.
  Proof.
    induction lambda.
    - trivial.
    - unfold Zvec_mul, map in *.
      rewrite Z.mul_1_l, IHlambda.
      trivial.
  Qed.
  Theorem thm_Zvec_eqb_eq :
    forall lambda mu,
      length lambda = length mu
      -> Zvec_short_allb Z.eqb lambda mu = true
         <-> lambda = mu.
  Proof.
    induction lambda.
    - destruct mu ; simpl.
      + tauto.
      + discriminate.
    - destruct mu ; simpl.
      + discriminate.
      + simpl_extra.
        firstorder.
  Qed.
  Theorem thm_Zvec_nonnegb_from_sub :
    forall lambda mu,
      length lambda = length mu
      -> Zvec_all_nonnegb mu = true
      -> Zvec_all_nonnegb (Zvec_short_sub lambda mu) = true
      -> Zvec_all_nonnegb lambda = true.
  Proof.
    unfold Zvec_all_nonnegb.
    induction lambda ; destruct mu ; simpl ; intuition.
    try rewrite Bool.andb_true_iff in *.
    try rewrite Z.leb_le in *.
    intuition.
    apply (IHlambda mu) ; intuition.
  Qed.
  Theorem thm_Zvec_short_even_sub_id :
    forall mu,
      Zvec_short_allb (fun a b : Z => Z.even (a - b)) mu mu = true.
  Proof.
    induction mu ; [tauto|].
    simpl.
    rewrite Bool.andb_true_iff, Z.even_sub.
    exact (conj (eqb_reflx _) IHmu).
  Qed.
  Theorem thm_Zvec_sub_add_const :
    forall nu t,
      Zvec_short_sub (nu) (map (Z.add t) nu)
      = repeat (-t)%Z (length nu).
  Proof.
    intros nu t.
    unfold Zvec_short_sub.
    induction nu.
    - trivial.
    - simpl.
      rewrite IHnu, Z.add_comm, Z.sub_add_distr, Z.sub_diag, Z.sub_0_l.
      trivial.
  Qed.
  Theorem thm_Zvec_sub_add_const2 :
    forall a nu t,
      Zvec_short_sub (a::nu) (a::map (Z.add t) nu)
      = 0%Z::repeat (-t)%Z (length nu).
  Proof.
    intros a nu t.
    rewrite <- thm_Zvec_sub_add_const.
    unfold Zvec_short_sub.
    simpl.
    rewrite Z.sub_diag.
    trivial.
  Qed.
End misc.

Section leb.
  Theorem thm_Zvec_leb_cons :
    forall a b lambda mu,
      Zvec_short_allb Z.leb (a::lambda) (b::mu) = true
      <-> (a <= b)%Z /\ Zvec_short_allb Z.leb lambda mu = true.
  Proof.
    intros.
    simpl_extra.
    split ; trivial.
  Qed.
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
  Theorem thm_Zvec_leb_irrefl :
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
  Theorem thm_Zleb_add_const :
    forall a b c, (a + b <=? a + c)%Z = (b <=? c)%Z.
  Proof.
    intros a b c.
    destruct (Sumbool.sumbool_of_bool (b <=? c)%Z) as [H|H] ;
      rewrite H.
    - exact (Zle_bool_plus_mono _ _ _ _ (Z.leb_refl _) H).
    - rewrite Z.leb_gt in *.
      exact (Zplus_lt_compat_l _ _ _ H).
  Qed.
End leb.

Section nondecb.
  Ltac tac_nondecb lambda :=
    destruct lambda ;
    unfold Zvec_nondecb ;
    simpl_extra ;
    firstorder.
  Theorem thm_Zvec_nondecb_nil :
    Zvec_nondecb nil = true .
  Proof.
    unfold Zvec_nondecb.
    simpl.
    trivial.
  Qed.
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
        rewrite last_app_cons.
        simpl in *.
        rewrite <- app_assoc in H.
        pose (H3 := thm_Zvec_nondecb_app _ _ H).
        destruct H3 as [H3 H4].
        exact (thm_Zvec_nondecb_app_hd _ _ _ _ H4).
    - pose (H := thm_Zvec_nondecb_app2 lambda mu).
      firstorder.
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
  Theorem thm_Zvec_nondecb_hd_last_eq :
    forall lambda a,
      Zvec_nondecb lambda = true
      -> hd a lambda = a
      -> a = last lambda a
      -> lambda = repeat a (length lambda).
  Proof.
    intros lambda z.
    induction lambda.
    - trivial.
    - intros Hinc Hhd Hlast.
      simpl in Hhd.
      rewrite <- Hhd in *.
      pose (Hinc2 := thm_Zvec_nondecb_cons _ _ Hinc).
      destruct lambda as [|b [|c lambda]].
      + simpl in * ; trivial.
      + simpl in * ; rewrite Hlast ; trivial.
      + assert (b::c::lambda <> nil) as H2; [discriminate|].
        rewrite (app_removelast_last a H2) in Hinc2.
        simpl in Hlast, Hinc2.
        rewrite <- Hlast in Hinc2.
        pose (Hba := thm_Zvec_nondecb_app_hd _ _ _ _ Hinc2).
        pose (Hab := thm_Zvec_nondecb_01_geq _ _ _ Hinc).
        assert (b = a) as Haeqb.
        { clear - Hab Hba ; omega. }
        simpl repeat.
        rewrite cons_eq.
        simpl repeat in IHlambda.
        firstorder.
        refine (IHlambda (thm_Zvec_nondecb_cons _ _ Hinc) _ _).
        * assumption.
        * assumption.
  Qed.
  Theorem thm_Zvec_nondecb_firstn :
    forall p lambda,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb (firstn p lambda) = true.
  Proof.
    intros.
    rewrite <- (firstn_skipn p lambda) in H.
    pose (H1 := thm_Zvec_nondecb_app _ _ H).
    tauto.
  Qed.
  Theorem thm_Zvec_nondecb_skipn :
    forall p lambda,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb (skipn p lambda) = true.
  Proof.
    intros.
    rewrite <- (firstn_skipn p lambda) in H.
    pose (H1 := thm_Zvec_nondecb_app _ _ H).
    tauto.
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
  Theorem thm_Zvec_nondecb_from_sub :
    forall lambda mu,
      length lambda = length mu
      -> Zvec_nondecb mu = true
      -> Zvec_nondecb (Zvec_short_sub lambda mu) = true
      -> Zvec_nondecb lambda = true.
  Proof.
    induction lambda ; [tauto|].
    destruct lambda ; [tauto|].
    destruct mu as [|c [|d mu]] ; try discriminate.
    intros.
    apply thm_Zvec_nondecb_join2.
    - unfold Zvec_nondecb in *.
      simpl in *.
      rewrite Bool.andb_true_iff, Z.leb_le in *.
      intuition.
    - apply (IHlambda (d::mu)%list).
      + simpl.
        injection H.
        intuition.
      + exact (thm_Zvec_nondecb_cons _ _ H0).
      + unfold Zvec_short_sub in *.
        simpl in *.
        exact (thm_Zvec_nondecb_cons _ _ H1).
  Qed.
  Theorem thm_Zvec_nondecb_long_min_tl :
    forall nu,
      Zvec_nondecb nu = true
      -> Zvec_long_min nu (tl nu) = nu.
  Proof.
    induction nu ; trivial.
    destruct nu ; trivial.
    simpl in *.
    intro H.
    rewrite <- (IHnu (thm_Zvec_nondecb_cons _ _ H)) at 3.
    unfold Zvec_long_min.
    simpl.
    rewrite cons_eq.
    exact (conj (Z.min_l _ _ (thm_Zvec_nondecb_01_geq _ _ _ H)) eq_refl).
  Qed.
  Theorem thm_Zvec_nondecb_short_max_tl :
    forall nu,
      Zvec_nondecb nu = true
      -> Zvec_short_max nu (tl nu) = tl nu.
  Proof.
    induction nu ; trivial.
    destruct nu ; trivial.
    simpl in *.
    intro H.
    rewrite <- (IHnu (thm_Zvec_nondecb_cons _ _ H)) at 3.
    unfold Zvec_short_max.
    simpl.
    rewrite cons_eq.
    exact (conj (Z.max_r _ _ (thm_Zvec_nondecb_01_geq _ _ _ H)) eq_refl).
  Qed.
  Theorem thm_Zvec_nondecb_plus_constant :
    forall a lambda,
      Zvec_nondecb (map (Z.add a) lambda)
      = Zvec_nondecb lambda.
  Proof.
    induction lambda.
    - trivial.
    - destruct lambda.
      + trivial.
      + unfold Zvec_nondecb in *.
        simpl in *.
        rewrite IHlambda, thm_Zleb_add_const.
        trivial.
  Qed.
End nondecb.

Section total.
  Theorem thm_total_app :
    forall lambda mu,
      total (lambda++mu)
      = (total lambda + total mu)%Z.
  Proof.
    induction lambda ; simpl.
    - trivial.
    - intros.
      rewrite (IHlambda mu).
      exact (Zplus_assoc _ _ _).
  Qed.
  Theorem thm_total_mul :
    forall m lambda,
      (total (Zvec_mul m lambda) = m * total lambda)%Z.
  Proof.
    unfold Zvec_mul.
    induction lambda ; simpl.
    - omega.
    - rewrite IHlambda.
      rewrite Z.mul_add_distr_l.
      trivial.
  Qed.
  Theorem thm_total_repeat :
    forall m a,
      (total (repeat a m) = (Z.of_nat m) * a)%Z.
  Proof.
    intros.
    induction m.
    - trivial.
    - simpl repeat.
      simpl total.
      rewrite IHm, thm_Z_of_nat_S.
      rewrite Z.mul_add_distr_r.
      omega.
  Qed.
  Theorem thm_total_from_sub :
    forall lambda mu,
      length lambda = length mu
      -> (total lambda
          = total (Zvec_short_sub lambda mu)
            + total mu)%Z.
  Proof.
    induction lambda.
    all : destruct mu.
    all : simpl.
    all : intuition.
    injection H.
    intros H0.
    pose (H1 := IHlambda mu H0).
    unfold Zvec_short_sub in H1.
    omega.
  Qed.
  Theorem thm_total_plus_constant :
    forall a lambda,
      total (map (Z.add a) lambda)
      = (total lambda + a * Z.of_nat (length lambda))%Z.
  Proof.
    induction lambda.
    - compute ; destruct a ; trivial.
    - simpl length in *.
      simpl map in *.
      simpl total in *.
      rewrite thm_Z_of_nat_S, IHlambda.
      ring.
  Qed.
End total.

Section leb_nondecb.
  Theorem thm_Zvec_nondecb_fact1 :
    forall a b lambda,
      (0 <= b)%Z
      -> Zvec_nondecb (a::b::lambda) = true
      -> forallb (Z.leb 0%Z) lambda = true.
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
  Theorem thm_Zvec_nondecb_hd_leb:
    forall lambda a,
      Zvec_nondecb lambda = true
      -> (a <= hd a lambda)%Z
      -> Zvec_short_allb Z.leb (repeat a (length lambda)) lambda = true.
  Proof.
    induction lambda.
    - simpl ; firstorder.
    - intros.
      simpl_extra.
      simpl in H0.
      firstorder.
      refine (IHlambda a0 (thm_Zvec_nondecb_cons _ _ H) _).
      destruct lambda ; simpl ;
      [|unfold Zvec_nondecb in H ; simpl_destruct H as [H _]] ;
      omega.
  Qed.
  Theorem thm_Zvec_nondecb_last_leb :
    forall lambda a,
      Zvec_nondecb (lambda ++ a::nil) = true
      -> Zvec_short_allb Z.leb (lambda ++ a::nil)
                         (repeat a (1 + length lambda)) = true.
  Proof.
    intros lambda a H.
    assert (forallb (Z.geb a) lambda = true) as H0.
    {
      induction lambda.
      - trivial.
      - simpl in *.
        simpl_extra.
        split.
        + rewrite Z.geb_le.
          exact (thm_Zvec_nondecb_app_hd _ _ _ _ H).
        + exact (IHlambda (thm_Zvec_nondecb_cons _ _ H)).
    }
    rewrite plus_comm, repeat_plus.
    simpl.
    rewrite thm_Zvec_leb_app.
    split.
    - induction lambda.
      + trivial.
      + simpl_extra.
        simpl_extra in H0.
        rewrite Z.geb_le in H0.
        pose (H2 := IHlambda (thm_Zvec_nondecb_cons _ _ H)).
        firstorder.
    - exact (thm_Zvec_leb_refl _).
    - tac_length.
  Qed.
  Theorem thm_Zvec_nondecb_last_leb2 :
    forall a lambda,
      last lambda a = a
      -> Zvec_nondecb lambda = true
      -> Zvec_short_allb Z.leb lambda
                         (repeat a (length lambda)) = true.
  Proof.
    intros a lambda.
    destruct (list_eq_dec Z.eq_dec lambda nil) as [H|H].
    - rewrite H in * ; simpl ; trivial.
    - pose (H0 := app_removelast_last a H).
      intros H1 H2.
      rewrite H1 in *.
      rewrite H0 in H2.
      pose (H3 := thm_Zvec_nondecb_last_leb _ _ H2).
      rewrite <- H0 in H3.
      assert (1 + length (removelast lambda) = length lambda) as H4.
      {
        simpl_length.
        destruct lambda ; simpl.
        - contradiction (H (eq_refl _)).
        - omega.
      }
      rewrite H4 in H3.
      exact H3.
  Qed.
End leb_nondecb.

Section leb_total.
  Theorem thm_Zvec_leb_total :
    forall mu lambda,
      length mu <= length lambda
      -> Zvec_short_allb Z.leb lambda mu = true
      -> (total (firstn (length mu) lambda)
          <= total mu)%Z.
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
          <-> total mu
              = total (firstn (length mu) lambda)).
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
  Theorem thm_Zvec_leb_eq_tot :
    forall lambda mu : list Z,
      length lambda = length mu
      -> Zvec_short_allb Z.leb lambda mu = true
      -> total lambda = total mu <-> lambda = mu.
  Proof.
    intros lambda mu Hlength Hleb.
    assert (length mu <= length lambda) as Hlength2.
    { omega. }
    pose (H := thm_Zvec_leb_eqb_tot lambda mu Hlength2 Hleb).
    assert (length lambda <= length mu) as Hlength3.
    { omega. }
    rewrite (firstn_id _ _ _ Hlength3) in H.
    rewrite Z.eq_sym_iff, <- H.
    exact (thm_Zvec_eqb_eq lambda mu Hlength).
  Qed.
  Theorem thm_Zvec_leb_total_same_length :
    forall mu lambda,
      length mu = length lambda
      -> Zvec_short_allb Z.leb lambda mu = true
      -> (total lambda <= total mu)%Z.
  Proof.
    induction mu.
    - destruct lambda.
      + omega.
      + discriminate.
    - destruct lambda.
      + discriminate.
      + simpl_extra.
        intros H [H0 H1].
        pose (H2 := IHmu lambda H H1).
        omega.
  Qed.
End leb_total.

Section nondecb_total.
  Theorem thm_Zvec_nondecb_total_app :
    forall lambda mu,
      Zvec_nondecb (lambda++mu) = true
      -> total (lambda++mu) = 0%Z
      -> (total lambda <= 0)%Z
         /\ (total mu >= 0)%Z.
  Proof.
    intros lambda mu H Htot.
    assert (total lambda <= 0 \/ 0 <= total mu)%Z as Hor.
    {
      pose (H0 := thm_Zvec_nondecb_app _ _ H).
      destruct H0 as [H0 H1].
      destruct mu as [|a mu].
      - right ; firstorder.
      - destruct (Z_lt_le_dec a 0) as [H2|H2].
        + left.
          assert (forallb (Z.gtb 0) lambda = true) as H3.
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
                    forallb (Z.gtb 0) lambda0 = true
                    -> total lambda0 <= 0)%Z as H4.
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
          * unfold total ; simpl ; firstorder.
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
    rewrite (thm_total_app _ _) in Htot.
    destruct Hor as [H0|H0] ; omega.
  Qed.
  Theorem thm_Zvec_nondecb_partialsum :
    (forall lambda p,
       Zvec_nondecb lambda = true
       -> total lambda = 0
       -> total (firstn p lambda) <= 0)%Z.
  Proof.
    intros lambda p Hinc Htot.
    pose (Hval := firstn_skipn p lambda).
    rewrite <- Hval in Hinc, Htot.
    pose (H := thm_Zvec_nondecb_total_app _ _ Hinc Htot).
    firstorder.
  Qed.
  Theorem thm_Zvec_nondecb_fact2 :
    forall a b lambda,
      (0 <= b)%Z
      -> Zvec_nondecb (a::b::lambda) = true
      -> (total lambda >= 0)%Z.
  Proof.
    unfold Zvec_nondecb.
    simpl.
    intros a b lambda H1 H2.
    generalize lambda as lambda0, (thm_Zvec_nondecb_fact1 a b lambda H1 H2).
    induction lambda0.
    - unfold total ; firstorder.
    - simpl_extra.
      firstorder.
  Qed.
End nondecb_total.

Tactic Notation "tac_nondecb" :=
  repeat
    (simpl || match goal with
                | [ |- Zvec_nondecb nil = true ]
                  => exact thm_Zvec_nondecb_nil
                | [ |- Zvec_nondecb (_::_::_::_) = true ]
                  => refine (thm_Zvec_nondecb_join3 _ _ _ _ _ _ _)
                | [ |- Zvec_nondecb (_::_::_) = true ]
                  => refine (thm_Zvec_nondecb_join2 _ _ _ _ _)
                | [ |- Zvec_nondecb (_::_) = true ]
                  => refine (thm_Zvec_nondecb_join _ _ _ _)
                | [ |- Zvec_nondecb (_++_) = true ]
                  => rewrite thm_Zvec_nondecb_app_iff
                | [ |- Zvec_nondecb (repeat _ _) = true ]
                  => refine (thm_Zvec_nondecb_repeat _ _)
                | [ |- _ /\ _ ]
                  => split
                | [ |- context[hd] ]
                  => simpl_hd
                | [ |- context[last (repeat _ _)]]
                  => rewrite last_repeat
                | [ |- context[if ?p=?0 then _ else _]]
                  => (destruct p ; simpl ; try omega) (*Possibly dangerous loop?*)
                | [ |- _ ]
                  => try omega
              end).

Hint Rewrite
     thm_total_app
     thm_total_repeat
     thm_Z_of_nat_S
     Z.mul_add_distr_r
     Z.add_assoc
     Z.mul_1_l
     Z.mul_1_r
     Z.mul_0_l
     Z.mul_0_r
: rewritetotal.
Tactic Notation "simpl_total" :=
  repeat (simpl || autorewrite with rewritetotal).
Tactic Notation "simpl_total" "in" hyp(H) :=
  repeat (simpl in H || autorewrite with rewritetotal in H).
