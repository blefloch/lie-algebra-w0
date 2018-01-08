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


Section generalities.
  Theorem thm_C_radical_cons_le :
    forall g a lambda,
      lie_algebra_type g = lie_C_type
      -> lie_is_radical_revwt_alg g (a :: lambda) = true
      -> (a <= hd a lambda)%Z.
  Proof.
    intros g a lambda Hgtype.
    destruct g ; try discriminate Hgtype ; destruct s as [n Hn].
    unfold lie_is_radical_revwt_alg.
    simpl_extra.
    intuition.
    destruct lambda ; simpl ; intuition.
    refine (thm_Zvec_nondecb_01_geq _ _ _ H1).
  Qed.
  Theorem thm_C_radical_total_even :
    forall (g : lie_algebra) (lambda : list Z),
      lie_algebra_type g = lie_C_type
      -> lie_is_radical_revwt_alg g lambda = true
      -> Z.even (total lambda) = true.
  Proof.
    intros g lambda Hgtype Hrad.
    destruct g ; try discriminate Hgtype ; destruct s as [n Hn].
    unfold lie_is_radical_revwt_alg in Hrad.
    simpl_destruct Hrad as [Hlen [[Hinc H0hd] Heven]].
    assumption.
  Qed.
  Theorem thm_C_radical_nondecb :
    forall g lambda,
      lie_algebra_type g = lie_C_type
      -> lie_is_radical_revwt_alg g lambda = true
      -> Zvec_nondecb lambda = true.
  Proof.
    intros g lambda Hgtype Hrad.
    destruct g as [| |[n Hn]| | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    unfold lie_is_radical_revwt_alg in Hrad.
    simpl_extra in Hrad.
    intuition.
  Qed.
End generalities.
    
Section exceptional_structure.
  Theorem thm_C_exceptional_structure :
    forall g lambda,
      lie_algebra_type g = lie_C_type
      -> Is_exceptional_revwt_alg g lambda
      -> let n := lie_rank g in
         (lambda = repeat 0%Z n)
         \/ (exists m, (0 <= m)%Z /\ lambda = repeat 0%Z (n - 1) ++ (m * 2)%Z::nil)
         \/ (exists j, 1 <= j /\ 2 * j <= n
                       /\ lambda = repeat 0%Z (n - 2 * j) ++ repeat 1%Z (2 * j))
         \/ lambda = repeat 0%Z (n - 2) ++ 2%Z::2%Z::nil
         \/ (exists m, (3 <= m)%Z /\ lambda = m::m::nil)
         \/ lambda = (2::2::2::nil)%Z
         \/ lambda = (2::2::2::2::nil)%Z.
  Proof.
    intros g lambda Hgtype [i [m [Hmul Hlambdaval]]] n'.
    pose (H := thm_lie_fundamental_revwt_is_radical g i).
    set (mu := lie_radical_fundamental_revwt_alg g i) in *.
    pose (Hlenmu := thm_radical_length g mu H).
    destruct g ; try discriminate Hgtype ; destruct s as [n Hn].
    simpl in *.
    unfold is_exceptional_multiplier in Hmul.
    simpl in Hmul.
    destruct (Sumbool.sumbool_of_bool (m <? 0)%Z) as [Hmlt0|Hmlt0] ;
      rewrite Hmlt0 in * ; [discriminate Hmul|rewrite Z.ltb_ge in Hmlt0].
    destruct (Sumbool.sumbool_of_bool (m =? 0)%Z) as [Hm0|Hm0] ;
      rewrite Hm0 in *.
    {
      left.
      rewrite Z.eqb_eq in Hm0.
      rewrite Hm0 in *.
      rewrite thm_Zvec_mul_0, Hlenmu in Hlambdaval.
      assumption.
    }
    destruct (Sumbool.sumbool_of_bool (i =? 0)) as [Hi0|Hi0] ;
      rewrite Hi0 in * ; [discriminate Hmul|].
    destruct (Sumbool.sumbool_of_bool (n <? i)) as [Hni|Hni] ;
      rewrite Hni in * ; [discriminate Hmul|simpl in Hmul].
    repeat rewrite orb_true_iff in Hmul.
    repeat rewrite andb_true_iff in Hmul.
    destruct Hmul as [[[[[Hmul|Hmul]|Hmul]|Hmul]|Hmul]|Hmul].
    all : repeat rewrite Z.eqb_eq in Hmul.
    all : repeat rewrite Nat.eqb_eq in Hmul.
    - right ; left.
      exists m.
      split ; [assumption|].
      rewrite Hlambdaval.
      unfold n', mu, lie_radical_fundamental_revwt_alg, lie_rank, Zvec_mul.
      rewrite Hi0, Hni, Hmul.
      simpl.
      rewrite map_app, map_repeat, Z.mul_0_r.
      simpl.
      trivial.
    - right ; right ; left.
      destruct Hmul as [Heven Hm1].
      pose (Hevencopy := Heven).
      rewrite Nat.even_spec in Hevencopy.
      destruct Hevencopy as [j Hj].
      exists j.
      repeat split.
      + rewrite Hj in *.
        destruct j ; [discriminate Hi0|clear ; omega].
      + rewrite Hj in *.
        rewrite Nat.ltb_ge in Hni.
        unfold n'.
        clear -Hni.
        omega.
      + rewrite Hlambdaval.
        unfold mul in Hj.
        rewrite <- Hj.
        unfold n', mu, lie_radical_fundamental_revwt_alg, lie_rank, Zvec_mul.
        rewrite Hi0, Hni.
        simpl.
        rewrite Heven, Hm1.
        rewrite map_app, map_repeat, map_repeat.
        simpl.
        trivial.
    - right ; right ; right ; left.
      destruct Hmul as [Hi2 Hm2].
      rewrite Hlambdaval.
      unfold mu.
      rewrite Hi2, Hm2 in *.
      unfold n', mu, lie_radical_fundamental_revwt_alg, lie_rank, Zvec_mul.
      rewrite Hi0, Hni.
      simpl.
      rewrite map_app, map_repeat.
      simpl.
      trivial.
    - rewrite Hmul in *.
      destruct i as [|[|[|]]] ; [discriminate Hi0 | | |] ;
      try (rewrite Nat.ltb_ge in Hni ; clear -Hni ; omega).
      + right ; left.
        exists m.
        rewrite Hlambdaval.
        split ; [assumption|].
        unfold n', mu, lie_radical_fundamental_revwt_alg, lie_rank, Zvec_mul.
        rewrite Hmul at 1.
        rewrite Hi0, Hni.
        simpl.
        rewrite map_app, map_repeat, Z.mul_0_r.
        simpl.
        trivial.
      + destruct (Sumbool.sumbool_of_bool (1 =? m)%Z) as [H1m|H1m].
        {
          right ; right ; left.
          exists 1.
          unfold n'.
          rewrite Z.eqb_eq in H1m.
          rewrite Hmul, Hlambdaval, <- H1m, thm_Zvec_mul_1.
          unfold mu, lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank.
          rewrite Hmul.
          simpl.
          intuition.
        }
        destruct (Sumbool.sumbool_of_bool (2 =? m)%Z) as [H2m|H2m].
        {
          right ; right ; right ; left.
          unfold n'.
          rewrite Z.eqb_eq in H2m.
          rewrite Hmul, Hlambdaval, <- H2m.
          unfold mu, lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank.
          rewrite Hmul.
          simpl.
          intuition.
        }
        rewrite Z.eqb_neq in *.
        assert (3 <= m)%Z.
        { omega. }
        right ; right ; right ; right ; left.
        exists m.
        rewrite Hlambdaval.
        split ; [assumption|].
        unfold n', mu, lie_radical_fundamental_revwt_alg, lie_rank, Zvec_mul.
        simpl.
        rewrite Hmul.
        rewrite Hni.
        simpl.
        rewrite Z.mul_1_r.
        trivial.
    - unfold mu in Hlambdaval.
      destruct Hmul as [[Hn3 Hi3] Hm1].
      rewrite Hm1, thm_Zvec_mul_1 in Hlambdaval.
      unfold lie_radical_fundamental_revwt_alg, lie_rank, Zvec_mul in Hlambdaval.
      rewrite Hi0, Hni in Hlambdaval.
      simpl in Hlambdaval.
      rewrite Hn3, Hi3 in Hlambdaval.
      simpl in Hlambdaval.
      intuition.
    - unfold mu in Hlambdaval.
      destruct Hmul as [[Hn4 Hi4] Hm2].
      rewrite Hm2 in Hlambdaval.
      unfold lie_radical_fundamental_revwt_alg, lie_rank, Zvec_mul in Hlambdaval.
      rewrite Hi0, Hni in Hlambdaval.
      simpl in Hlambdaval.
      rewrite Hn4, Hi4 in Hlambdaval.
      simpl in Hlambdaval.
      intuition.
  Qed.
  Theorem thm_C_prepend_zero_exceptional0 :
    forall g h,
      lie_algebra_type g = lie_C_type
      -> lie_algebra_type h = lie_C_type
      -> lie_rank g = 1 + lie_rank h
      -> forall lambda,
           lambda = repeat 0%Z (lie_rank h)
           -> Is_exceptional_revwt_alg g (0%Z::lambda).
  Proof.
    intros g h Hgtype Hhtype Hrank lambda Hval.
    destruct g as [| |[n Hn]| | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    simpl in Hrank.
    rewrite Hval, cons_repeat, <- Hrank.
    exact (thm_zero_is_exceptional_revwt _).
  Qed.
  Theorem thm_C_prepend_zero_exceptional1 :
    forall g h,
      lie_algebra_type g = lie_C_type
      -> lie_algebra_type h = lie_C_type
      -> lie_rank g = 1 + lie_rank h
      -> forall lambda,
           (exists m, (0 <= m)%Z /\ lambda = repeat 0%Z (lie_rank h - 1) ++ (m * 2)%Z::nil)
           -> Is_exceptional_revwt_alg g (0%Z::lambda).
  Proof.
    intros g h Hgtype Hhtype Hrank lambda [m [H0m H]].
    destruct g as [| |[n Hn]| | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    simpl in Hrank.
    exists 1, m.
    rewrite H, app_comm_cons, cons_repeat, minus_Sn_m, <- Hrank ;
      [|
       destruct h as [| |[k Hk]| | | | | | ] ;
         try (simpl in Hhtype; discriminate Hhtype) ;
         simpl ; omega
      ].
    unfold is_exceptional_multiplier, lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank.
    simpl.
    assert (n <? 1 = false) as H0.
    { rewrite Nat.ltb_ge. omega. }
    rewrite H0.
    split.
    + rewrite <- Z.ltb_ge in H0m ; rewrite H0m.
      destruct (m =? 0)%Z ; trivial.
    + unfold Zvec_mul.
      rewrite map_app, map_repeat, Z.mul_0_r.
      simpl ; trivial.
  Qed.
  Theorem thm_C_prepend_zero_exceptional2 :
    forall g h,
      lie_algebra_type g = lie_C_type
      -> lie_algebra_type h = lie_C_type
      -> lie_rank g = 1 + lie_rank h
      -> forall lambda,
           (exists j, 1 <= j /\ 2 * j <= lie_rank h
                      /\ lambda = repeat 0%Z (lie_rank h - 2 * j) ++ repeat 1%Z (2 * j))
           -> Is_exceptional_revwt_alg g (0%Z::lambda).
  Proof.
    intros g h Hgtype Hhtype Hrank lambda [j [H1j [Hjn H]]].
    destruct g as [| |[n Hn]| | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    simpl in Hrank.
    exists (2 * j), 1%Z.
    rewrite H, app_comm_cons, cons_repeat, minus_Sn_m, <- Hrank ; [|omega].
    unfold is_exceptional_multiplier, lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank.
    assert (2 * j =? 0 = false) as H0.
    { rewrite Nat.eqb_neq. omega. }
    assert (n <? 2 * j = false) as H1.
    { rewrite Nat.ltb_ge. omega. }
    assert (even (2 * j) = true) as H2.
    { rewrite Nat.even_spec. exists j. trivial. }
    rewrite H0, H1, H2.
    simpl.
    repeat rewrite orb_true_r.
    repeat rewrite orb_true_l.
    rewrite thm_Zvec_mul_1.
    intuition.
  Qed.
  Theorem thm_C_prepend_zero_exceptional3 :
    forall g h,
      lie_algebra_type g = lie_C_type
      -> lie_algebra_type h = lie_C_type
      -> lie_rank g = 1 + lie_rank h
      -> forall lambda,
           2 <= lie_rank h
           -> lambda = repeat 0%Z (lie_rank h - 2) ++ 2%Z::2%Z::nil
           -> Is_exceptional_revwt_alg g (0%Z::lambda).
  Proof.
    intros g h Hgtype Hhtype Hrank lambda Hrkh H.
    destruct g as [| |[n Hn]| | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    simpl in Hrank.
    exists 2, 2%Z.
    rewrite H, app_comm_cons, cons_repeat, minus_Sn_m, <- Hrank ; [|omega].
    unfold is_exceptional_multiplier, lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank, Zvec_mul.
    assert (n <? 2 = false) as H0.
    { rewrite Nat.ltb_ge. omega. }
    rewrite H0.
    simpl.
    rewrite map_app, map_repeat.
    simpl.
    intuition.
  Qed.
End exceptional_structure.

Section reduction.
  Theorem thm_reduction1_radical :
    forall g h,
      lie_algebra_type g = lie_C_type
      -> lie_algebra_type h = lie_C_type
      -> lie_rank g = 1 + lie_rank h
      -> forall mu mun,
           Z.Even mun
           -> lie_is_radical_revwt_alg g (mun::mu) = true
           -> lie_is_radical_revwt_alg h mu = true.
  Proof.
    intros g h Hgtype Hhtype Hrank mu mun Heven Hradlambda.
    destruct g ; try discriminate Hgtype ; destruct s as [n Hn].
    destruct h ; try discriminate Hhtype ; destruct s as [m Hm].
    clear Hgtype Hhtype.
    simpl in Hrank.
    unfold lie_is_radical_revwt_alg, lie_algebra_type, lie_is_radical_revwt_type, lie_embedding_dim, lie_rank in *.
    repeat (rewrite Bool.andb_true_iff in *)
           || (rewrite Nat.eqb_eq in *)
           || simpl.
    simpl in *.
    firstorder.
    - refine (thm_Zvec_nondecb_cons _ _ H0).
    - destruct mu ; simpl ; trivial.
      pose (H7 := thm_Zvec_nondecb_01_geq _ _ _ H0).
      rewrite Z.leb_le in *.
      omega.
    - rewrite H3 in H1.
      autorewrite with rewriteeven in H1.
      rewrite eqb_true_iff in H1.
      rewrite <- H1.
      tauto.
  Qed.
  Theorem thm_reduction1 :
    forall g h,
      lie_algebra_type g = lie_C_type
      -> lie_algebra_type h = lie_C_type
      -> lie_rank g = 1 + lie_rank h
      -> forall mu mun,
           (0 <= mun)%Z
           -> (mun <= hd mun mu)%Z
           -> Z.Even mun
           -> Is_mixed_revwt_alg h mu
           -> Is_mixed_revwt_alg g (mun::mu).
  Proof.
    intros g h Hgtype Hhtype Hrank mu mun H0 H1 [a Ha] Hmu.
    destruct g ; try discriminate Hgtype ; destruct s as [n Hn].
    destruct h ; try discriminate Hhtype ; destruct s as [m Hm].
    clear Hgtype Hhtype.
    simpl in Hrank.
    refine (mixed_by_induction _ _ _ _ Hmu _).
    unfold Is_known_w0_branching_revwt_alg ; simpl.
    pose (Hmurad := thm_mixed_is_radical _ _ Hmu).
    unfold lie_is_radical_revwt_alg, lie_algebra_type, lie_is_radical_revwt_type, lie_embedding_dim, lie_rank, Is_known_w0_branching_C_revwt in *.
    repeat (rewrite Bool.andb_true_iff in *)
           || (rewrite Nat.eqb_eq in *)
           || simpl.
    intuition.
    all : try (refine (thm_Zvec_nondecb_join mun mu H1 _) ; assumption).
    all : try (rewrite Z.leb_le ; assumption).
    all : try (rewrite Z.add_comm, Z.even_add_even ; [|exists a] ; intuition).
    rewrite thm_Zvec_nondecb_long_min_tl.
    rewrite thm_Zvec_nondecb_short_max_tl.
    simpl.
    - exact (thm_Zvec_short_even_sub_id _).
    - destruct mu.
      + trivial.
      + apply thm_Zvec_nondecb_join ; assumption.
    - assumption.
  Qed.
  Theorem thm_reduction2_radical :
    forall g h,
      lie_algebra_type g = lie_C_type
      -> lie_algebra_type h = lie_C_type
      -> lie_rank g = 1 + lie_rank h
      -> forall mu a b,
           Z.Odd a
           -> Z.Odd b
           -> lie_is_radical_revwt_alg g (a::b::mu) = true
           -> lie_is_radical_revwt_alg h (0%Z::mu) = true.
  Proof.
    intros g h Hgtype Hhtype Hrank mu a b HaOdd HbOdd Hradlambda.
    destruct g ; try discriminate Hgtype ; destruct s as [n Hn].
    destruct h ; try discriminate Hhtype ; destruct s as [m Hm].
    clear Hgtype Hhtype.
    simpl in Hrank.
    unfold lie_is_radical_revwt_alg, lie_algebra_type, lie_is_radical_revwt_type, lie_embedding_dim, lie_rank in *.
    autorewrite with rewritesome in *.
    simpl in *.
    firstorder.
    - refine (thm_Zvec_nondecb_join _ _ _ _).
      + destruct mu ; [exact (Z.le_refl _)|simpl].
        unfold Zvec_nondecb, tl, Zvec_short_allb in H0.
        simpl_extra in H0.
        omega.
      + refine (thm_Zvec_nondecb_cons _ _ (thm_Zvec_nondecb_cons _ _ H0)).
    - rewrite H3, H4 in H1.
      autorewrite with rewriteeven in H1.
      destruct (Z.even (total mu)) ; compute in H1 ; trivial ; discriminate.
  Qed.
  Theorem thm_reduction2 :
    forall g h,
      lie_algebra_type g = lie_C_type
      -> lie_algebra_type h = lie_C_type
      -> lie_rank g = 1 + lie_rank h
      -> forall mu mun1 mun,
           (0 <= mun)%Z
           -> (mun <= mun1)%Z
           -> (mun1 <= hd mun1 mu)%Z
           -> Z.Odd mun
           -> Z.Odd mun1
           -> Is_mixed_revwt_alg h (0%Z::mu)
           -> Is_mixed_revwt_alg g (mun::mun1::mu).
  Proof.
    intros g h Hgtype Hhtype Hrank mu mun mun1 H0 H1 H2 [a Ha] [b Hb] Hmu.
    destruct g ; try discriminate Hgtype ; destruct s as [n Hn].
    destruct h ; try discriminate Hhtype ; destruct s as [m Hm].
    clear Hgtype Hhtype.
    simpl in Hrank.
    refine (mixed_by_induction _ _ _ _ Hmu _).
    unfold Is_known_w0_branching_revwt_alg ; simpl.
    pose (Hmurad := thm_mixed_is_radical _ _ Hmu).
    repeat unfold lie_is_radical_revwt_alg, lie_algebra_type, lie_is_radical_revwt_type, lie_embedding_dim, lie_rank, Is_known_w0_branching_C_revwt in *.
    repeat (rewrite Bool.andb_true_iff in *) || (rewrite Nat.eqb_eq in *).
    destruct Hmurad as [Hlen0m [[Hinc0m _] Heven0m]].
    assert (length (mun1 :: mun :: mu) = n) as Hlen.
    { rewrite Hrank, <- Hlen0m ; exact eq_refl. }
    assert (Zvec_nondecb (mun1 :: mun :: mu) = true) as Hincmu.
    {
      refine (thm_Zvec_nondecb_join2 _ _ _ H1 _).
      refine (thm_Zvec_nondecb_join _ _ H2 _).
      exact (thm_Zvec_nondecb_cons _ _ Hinc0m).
    }
    assert ((0 <=? hd 0 (mun1 :: mun :: mu))%Z = true).
    { rewrite Z.leb_le ; assumption. }
    assert (Z.even (total (mun1 :: mun :: mu)) = true).
    {
      simpl.
      rewrite Ha, Hb.
      autorewrite with rewriteeven.
      simpl in Heven0m.
      rewrite Heven0m.
      tauto.
    }
    intuition.
    simpl tl.
    pose (Hmin := thm_Zvec_nondecb_long_min_tl
                  (mun::mu) (thm_Zvec_nondecb_cons _ _ Hincmu)).
    pose (Hmax := thm_Zvec_nondecb_short_max_tl
                    (mun::mu) (thm_Zvec_nondecb_cons _ _ Hincmu)).
    simpl in Hmin, Hmax.
    unfold Zvec_long_min, Zvec_short_max in *.
    simpl Zvec_short_map_zip in *.
    rewrite Hmin, Hmax, (Z.max_l _ _ H0).
    simpl.
    rewrite (thm_Zvec_short_even_sub_id _), Ha, Hb.
    autorewrite with rewriteeven.
    tauto.
  Qed.
End reduction.

Ltac show_mixed_by_ideal g mu Hnval :=
  repeat match goal with
           | [ |- _ /\ _ ] => split
           | [ |- _ \/ Is_mixed_revwt_alg _ _ ]
             => right ; refine (mixed_by_ideal g _ mu _ _ _)
           | [ |- Is_mixed_revwt_alg g mu ]
             => refine (mixed_by_hand g mu _)
           | [ |- is_mixed_by_hand_revwt_alg g mu = true]
             => try exact eq_refl ;
               try (compute ; try rewrite Hnval ; tauto)
           | [ |- length _ = length mu ]
             => exact eq_refl
           | [ |- lie_is_radical_revwt_alg g (Zvec_short_sub _ mu) = true ]
             => unfold Zvec_short_sub, lie_is_radical_revwt_alg ;
               simpl ;
               unfold Zvec_nondecb ;
               simpl_extra
           | [ H : Z.Even _ |- context[Z.even] ]
             => let x := fresh "x" in
                (destruct H as [x H] ; rewrite H in *)
           | [ H : Z.Odd _ |- context[Z.even] ]
             => let x := fresh "x" in
                (destruct H as [x H] ; rewrite H in *)
           | [ |- context[Z.even] ]
             => (progress autorewrite with rewriteeven in *)
                  || (repeat destruct (Z.even _))
           | [ |- _ ] => try rewrite Hnval ; simpl ; intuition ; try omega
         end.

Ltac show_exceptional g i m :=
  repeat match goal with
           | [ |- _ /\ _ ] => split
           | [ |- Is_exceptional_revwt_alg _ _ \/ _ ]
             => left ; exists i, m
           | [ |- is_exceptional_multiplier g i m = true ]
             => unfold is_exceptional_multiplier ;
               simpl ;
               let H := fresh "H" in
               (assert (m <? 0 = false)%Z as H;
                [apply Z.ltb_nlt; omega|];
                try rewrite H) ;
                 autorewrite with rewritebool ;
                 intuition
           | [ |- context[lie_radical_fundamental_revwt_alg] ]
             => unfold lie_radical_fundamental_revwt_alg ;
               simpl ;
               try rewrite Z.mul_1_r ;
               try rewrite Z.mul_1_l ;
               try rewrite Z.mul_0_r ;
               try rewrite Z.mul_0_l ;
               intuition
         end.

Section C12.
  Theorem thm_main_C1 :
    forall (Hn : 1 > 0) (lambda : list Z),
      let g := lie_C (exist (fun n : nat => n > 0) 1 Hn) in
      lie_is_radical_revwt_alg g lambda = true
      -> Is_exceptional_revwt_alg g lambda
         \/ Is_mixed_revwt_alg g lambda.
  Proof.
    intros Hn lambda g Hrad.
    unfold lie_is_radical_revwt_alg, lie_algebra_type, g, lie_is_radical_revwt_type in Hrad.
    repeat rewrite andb_true_iff in *.
    rewrite Nat.eqb_eq, Z.leb_le in *.
    simpl in *.
    intuition.
    destruct lambda as [|a [|]] ; simpl in * ; try discriminate.
    rewrite Z.add_0_r, Z.even_spec in *.
    match goal with [ H : Z.Even ?a |- _ ] => destruct H as [a2 Ha2]; rewrite Ha2 in * end.
    left.
    exists 1, a2.
    rewrite Z.mul_comm.
    simpl.
    unfold g, is_exceptional_multiplier, lie_rank.
    assert (0 <= a2)%Z as Ha20.
    {  omega. }
    rewrite <- Z.ltb_ge in Ha20.
    rewrite Ha20.
    simpl.
    destruct (a2 =? 0)%Z ; tauto.
  Qed.
  Theorem thm_main_C2 :
    forall (Hn : 2 > 0) (lambda : list Z),
      let g := lie_C (exist (fun n : nat => n > 0) 2 Hn) in
      lie_is_radical_revwt_alg g lambda = true
      -> Is_exceptional_revwt_alg g lambda
         \/ Is_mixed_revwt_alg g lambda.
  Proof.
    intros Hn lambda g Hrad.
    pose (Hlen := thm_radical_length _ _ Hrad).
    clearbody Hlen.
    destruct lambda as [|a [|b [|]]] ; simpl in Hlen ; try omega.
    unfold lie_is_radical_revwt_alg, lie_algebra_type, g, lie_is_radical_revwt_type, Zvec_nondecb, total in Hrad.
    simpl in *.
    repeat rewrite andb_true_iff in *.
    repeat rewrite Z.leb_le in *.
    destruct Hrad as [[[Hab _] H0a] Heven].
    destruct (Zle_lt_or_eq _ _ H0a) as [H0a'|H0a'] ;
      destruct (Zle_lt_or_eq _ _ Hab) as [Hab'|Hab'].
    - assert (b <> a + 1)%Z as H.
      {
        intros H.
        rewrite H in Heven.
        autorewrite with rewriteeven in Heven.
        destruct (Z.even a) ; compute in Heven ; discriminate Heven.
      }
      show_mixed_by_ideal g (1::3::nil)%Z omitted.
    - rewrite <- Hab' in *.
      show_exceptional g 2 a.
    - rewrite <- H0a' in *.
      destruct (Z.Even_or_Odd b) as [H|H].
      + destruct H as [x H].
        show_exceptional g 1 x.
        rewrite (Z.mul_comm x 2), <- H.
        trivial.
      + destruct H as [x H].
        rewrite H in Heven.
        autorewrite with rewriteeven in Heven.
        simpl in Heven.
        discriminate Heven.
    - rewrite <- Hab', <- H0a'.
      exact (or_introl (thm_zero_is_exceptional_revwt g)).
  Qed.
End C12.

Section main.
  Theorem thm_main_C_hd_even :
    forall n
           (Hn1 : S (S (S n)) > 0)
           a lambda,
      let g := lie_C (exist (fun n : nat => n > 0) (S (S (S n))) Hn1) in
      forall (Hradg : lie_is_radical_revwt_alg g (a :: lambda) = true)
             (Hn : S (S n) > 0),
        let h := lie_C (exist (fun n : nat => n > 0) (S (S n)) Hn) in
        (forall lambda : list Z,
           lie_is_radical_revwt_alg h lambda = true ->
           Is_exceptional_revwt_alg h lambda \/ Is_mixed_revwt_alg h lambda)
        -> lie_algebra_type h = lie_C_type
        -> lie_algebra_type g = lie_C_type
        -> lie_rank g = 1 + lie_rank h
        -> (0 <= a)%Z
        -> (a <= hd a lambda)%Z
        -> Z.Even a
        -> Is_exceptional_revwt_alg g (a :: lambda) \/
           Is_mixed_revwt_alg g (a :: lambda).
  Proof.
    intros n Hn1 a lambda g Hradg Hn h IHnHn Hhtype Hgtype Hrank H0a Hahd HaEven.
    destruct (IHnHn lambda (thm_reduction1_radical
                              g h Hgtype Hhtype Hrank lambda a HaEven Hradg))
               as [Hexc|Hmix].
    - destruct (thm_C_exceptional_structure h lambda Hhtype Hexc)
        as [H|[H|[H|[H|[H|[H|H]]]]]].
      + rewrite H in Hahd.
        simpl in Hahd.
        assert (a = 0%Z) as H0 ; [omega|].
        rewrite H0.
        exact (or_introl
                 (thm_C_prepend_zero_exceptional0
                    g h Hgtype Hhtype Hrank lambda H)).
      + destruct H as [m [H0m H]].
        rewrite H in Hahd.
        simpl in Hahd.
        assert (a = 0%Z) as H0 ; [omega|].
        rewrite H0.
        left.
        refine (thm_C_prepend_zero_exceptional1 g h Hgtype Hhtype Hrank lambda _).
        exists m ; intuition.
      + destruct H as [j [H1j [Hjn H]]].
        assert (2 * j =? 0 = false) as H1.
        { rewrite Nat.eqb_neq. omega. }
        rewrite H, hd_app, hd_repeat, hd_repeat, H1 in Hahd.
        assert (a = 0%Z) as H0.
        {
          destruct (_ =? _) in Hahd ;
          destruct HaEven as [b Hb] ; omega.
        }
        rewrite H0.
        left.
        refine (thm_C_prepend_zero_exceptional2 g h Hgtype Hhtype Hrank lambda _).
        exists j ; intuition.
      + left.
        rewrite H, hd_app, hd_repeat in Hahd.
        assert (2 <= lie_rank h) as H1.
        { unfold h, lie_rank ; omega. }
        destruct (le_lt_eq_dec _ _ H1) as [Hrkh2|Hrkh2].
        * assert (lie_rank h - 2 =? 0 = false) as H2.
          { rewrite Nat.eqb_neq. omega. }
          rewrite H2 in Hahd.
          assert (a = 0%Z) as H0 ; [omega|].
          rewrite H0.
          exact (thm_C_prepend_zero_exceptional3 g h Hgtype Hhtype Hrank lambda H1 H).
        * assert (n = 0) as Hnval.
          { unfold h in * ; simpl in * ; omega. }
          rewrite <- Hrkh2 in *.
          destruct (thm_even_between_0_and_2 a HaEven H0a Hahd) as [H0|H0].
          all : exists (if (a =? 2)%Z then 3 else 2),
                  (if (a =? 2)%Z then 1%Z else 2%Z).
          all : rewrite H, H0 in *.
          all : unfold g, is_exceptional_multiplier,
                lie_radical_fundamental_revwt_alg.
          all : simpl.
          all : rewrite Hnval in *.
          all : tauto.
      + (*The exceptional 2::2::2::nil is treated elsewhere.  Others are at least
                2::3::3::nil or 0::3::3::nil or 4::4::4::nil, mixed by hand*)
        destruct H as [m [H3m H]].
        assert (n = 0) as Hnval.
        {
          pose (Hlen := thm_radical_length _ _ Hradg).
          rewrite H in Hlen.
          unfold g, lie_embedding_dim, lie_rank in Hlen.
          simpl_extra in Hlen.
          intuition.
        }
        rewrite H in *.
        simpl in *.
        destruct (Zle_lt_or_eq _ _ Hahd) as [H0|H0].
        destruct (Zle_lt_or_eq _ _ H0a) as [H1|H1].
        * assert (2 <= a)%Z.
          {
            destruct HaEven as [a2 Ha2].
            rewrite Ha2 in *.
            omega.
          }
          show_mixed_by_ideal g (2::3::3::nil)%Z Hnval.
        * rewrite <- H1 in *.
          show_mixed_by_ideal g (0::3::3::nil)%Z Hnval.
        * rewrite H0, Hnval in *.
          assert (4 <= m)%Z.
          {
            destruct HaEven as [a2 Ha2].
            rewrite Ha2 in *.
            omega.
          }
          show_mixed_by_ideal g (4::4::4::nil)%Z Hnval.
      + assert (n = 1) as Hnval.
        {
          pose (Hlen := thm_radical_length _ _ Hradg).
          rewrite H in Hlen.
          unfold g, lie_embedding_dim, lie_rank in Hlen.
          simpl_extra in Hlen.
          intuition.
        }
        rewrite H in *.
        simpl in *.
        destruct (thm_even_between_0_and_2 a HaEven H0a Hahd) as [H0|H0].
        * rewrite H0.
          right.
          refine (mixed_by_hand g _ _).
          compute ; try rewrite Hnval ; tauto.
        * left.
          exists 4, 2%Z.
          unfold g, is_exceptional_multiplier, lie_radical_fundamental_revwt_alg.
          simpl in *.
          rewrite H0, Hnval in *.
          tauto.
      + assert (n = 2) as Hnval.
        {
          pose (Hlen := thm_radical_length _ _ Hradg).
          rewrite H in Hlen.
          unfold g, lie_embedding_dim, lie_rank in Hlen.
          simpl_extra in Hlen.
          intuition.
        }
        rewrite H in Hahd.
        simpl in Hahd.
        destruct (thm_even_between_0_and_2 a HaEven H0a Hahd) as [H0|H0].
        all : rewrite H, H0.
        all : right.
        all : refine (mixed_by_hand g _ _).
        all : compute ; try rewrite Hnval ; tauto.
    - exact (or_intror
               (thm_reduction1
                  g h Hgtype Hhtype Hrank lambda a H0a Hahd HaEven Hmix)).
  Qed.

  Ltac show_exceptional g i m :=
    repeat match goal with
             | [ |- _ /\ _ ] => split
             | [ |- Is_exceptional_revwt_alg _ _ \/ _ ]
               => left ; exists i, m
             | [ |- is_exceptional_multiplier g i m = true ]
               => unfold is_exceptional_multiplier, g, lie_embedding_dim, lie_rank ;
                 let H := fresh "H" in
                 (assert (m <? 0 = false)%Z as H;
                  [apply Z.ltb_nlt; omega|];
                  try rewrite H) ;
                   autorewrite with rewritebool ;
                   intuition
             | [ |- context[lie_radical_fundamental_revwt_alg] ]
               => unfold lie_radical_fundamental_revwt_alg, g, lie_embedding_dim, lie_rank ;
                 try rewrite thm_Zvec_mul_1 ;
                 try rewrite Z.mul_1_r ;
                 try rewrite Z.mul_1_l ;
                 try rewrite Z.mul_0_r ;
                 try rewrite Z.mul_0_l ;
                 intuition
             | [ |- context[Nat.eqb ?p ?q] ]
               => let H := fresh "H" in
                  ((assert ((p =? q) = true) as H ;
                    [rewrite Nat.eqb_eq ; omega|rewrite H in *])
                     || (assert ((p =? q) = false) as H ;
                         [rewrite Nat.eqb_neq ; omega|rewrite H in *]))
             | [ |- context[Nat.leb ?p ?q] ]
               => let H := fresh "H" in
                  ((assert ((p <=? q) = true) as H ;
                    [rewrite Nat.leb_le ; omega|rewrite H in *])
                     || (assert ((p <=? q) = false) as H ;
                         [rewrite Nat.leb_gt ; omega|rewrite H in *]))
             | [ |- context[Nat.ltb ?p ?q] ]
               => let H := fresh "H" in
                  ((assert ((p <? q) = true) as H ;
                    [rewrite Nat.ltb_lt ; omega|rewrite H in *])
                     || (assert ((p <? q) = false) as H ;
                         [rewrite Nat.ltb_ge ; omega|rewrite H in *]))
             | [ |- context[Z.eqb ?p ?q] ]
               => let H := fresh "H" in
                  ((assert ((p =? q)%Z = true) as H ;
                    [rewrite Z.eqb_eq ; omega|rewrite H in *])
                     || (assert ((p =? q)%Z = false) as H ;
                         [rewrite Z.eqb_neq ; omega|rewrite H in *]))
             | [ |- context[Z.leb ?p ?q] ]
               => let H := fresh "H" in
                  ((assert ((p <=? q)%Z = true) as H ;
                    [rewrite Z.leb_le ; omega|rewrite H in *])
                     || (assert ((p <=? q)%Z = false) as H ;
                         [rewrite Z.leb_gt ; omega|rewrite H in *]))
             | [ |- context[Z.ltb ?p ?q] ]
               => let H := fresh "H" in
                  ((assert ((p <? q)%Z = true) as H ;
                    [rewrite Z.ltb_lt ; omega|rewrite H in *])
                     || (assert ((p <? q)%Z = false) as H ;
                         [rewrite Z.ltb_ge ; omega|rewrite H in *]))
             | [ |- context[even] ]
               => try rewrite thm_mul_2_l_even
           end.

  Theorem thm_main_C_hd_odd_odd :
    forall n
           (Hn1 : S (S (S n)) > 0)
           a b lambda,
      let g := lie_C (exist (fun n : nat => n > 0) (S (S (S n))) Hn1) in
      forall (Hradg : lie_is_radical_revwt_alg g (a::b::lambda) = true)
             (Hn : S (S n) > 0),
        let h := lie_C (exist (fun n : nat => n > 0) (S (S n)) Hn) in
        (forall lambda : list Z,
           lie_is_radical_revwt_alg h lambda = true ->
           Is_exceptional_revwt_alg h lambda \/ Is_mixed_revwt_alg h lambda)
        -> lie_algebra_type h = lie_C_type
        -> lie_algebra_type g = lie_C_type
        -> lie_rank g = 1 + lie_rank h
        -> (0 <= a)%Z
        -> (a <= hd a (b::lambda))%Z
        -> Z.Odd a
        -> Z.Odd b
        -> Is_exceptional_revwt_alg g (a::b::lambda) \/
           Is_mixed_revwt_alg g (a::b::lambda).
  Proof.
    intros n Hn1 a b lambda g Hradg Hn h IHnHn Hhtype Hgtype Hrank H0a Hahd HaOdd HbOdd.
    pose (Hlen := thm_radical_length _ _ Hradg).
    simpl in Hahd.
    assert (1 <= a)%Z as H1a.
    { destruct HaOdd as [a2 Ha2] ; rewrite Ha2 in * ; omega. }
    assert (1 <= b)%Z as H1b.
    { omega. }
    destruct lambda as [|c lambda] ; try (simpl in * ; discriminate Hlen).
    assert (b <= c)%Z as Hbc.
    {
      pose (Hinc := thm_C_radical_nondecb _ _ Hgtype Hradg).
      unfold Zvec_nondecb in Hinc.
      simpl_extra in Hinc.
      omega.
    }
    destruct (IHnHn (0%Z::c::lambda)
                    (thm_reduction2_radical
                       g h Hgtype Hhtype Hrank _ a b HaOdd HbOdd Hradg))
      as [Hexc|Hmix].
    - destruct (thm_C_exceptional_structure h _ Hhtype Hexc)
        as [H|[H|[H|[H|[H|[H|H]]]]]].
      + simpl in H.
        repeat rewrite cons_eq in H.
        omega.
      + destruct H as [m [H0m H]].
        simpl in H.
        destruct n.
        * simpl in *.
          repeat rewrite cons_eq in H.
          destruct H as [_ [Hc H]].
          rewrite Hc, H in *.
          assert (b < m * 2)%Z.
          { destruct HbOdd as [b2 Hb2] ; rewrite Hb2 in * ; omega. }
          show_mixed_by_ideal g (1::1::2::nil)%Z omitted.
        * simpl in H.
          repeat rewrite cons_eq in H.
          omega.
      + destruct H as [j [H1j [Hjn H]]].
        set (t := lie_rank h - 2 * j) in *.
        destruct t ; [discriminate (repeat_spec_hd _ _ _ _ _ H)|].
        destruct t ; simpl in H ; repeat rewrite cons_eq in H.
        * destruct H as [_ H].
          assert (a::b::c::lambda = repeat 1%Z (2 * S j)) as H1.
          {
            simpl.
            pose (H1 := repeat_spec_hd _ _ _ _ _ H).
            rewrite <- plus_n_Sm.
            repeat (simpl ; rewrite cons_eq).
            intuition.
          }
          rewrite H1 in *.
          rewrite repeat_length in Hlen.
          simpl lie_embedding_dim in Hlen.
          show_exceptional g (2 * (S j)) 1%Z.
          all : rewrite Hlen in *.
          all : try rewrite Nat.sub_diag in *.
          all : simpl ; intuition.
        * omega.
      + simpl in H.
        destruct n as [|[|]] ; simpl in H.
        * discriminate H.
        * repeat rewrite cons_eq in H.
          destruct H as [_ [Hc Hlambda]].
          assert (b = 1%Z) as Hb.
          { destruct HbOdd as [b2 Hb2] ; rewrite Hb2 in * ; omega. }
          assert (a = 1%Z) as Ha.
          { omega. }
          rewrite Ha, Hb, Hc, Hlambda in *.
          right.
          refine (mixed_by_hand g _ _).
          compute ; try rewrite Hnval ; tauto.
        * repeat rewrite cons_eq in H.
          omega.
      + destruct H as [m [H3m H]].
        repeat rewrite cons_eq in H.
        omega.
      + discriminate H.
      + discriminate H.
    - exact (or_intror
               (thm_reduction2
                  g h Hgtype Hhtype Hrank (c::lambda) b a H0a Hahd Hbc HaOdd HbOdd Hmix)).
  Qed.


  Theorem thm_main_C :
    forall g,
      lie_algebra_type g = lie_C_type
      -> forall lambda,
           lie_is_radical_revwt_alg g lambda = true
           -> (Is_exceptional_revwt_alg g lambda)
              \/ (Is_mixed_revwt_alg g lambda).
  Proof.
    intros g Hgtype.
    destruct g as [| |[n Hn]| | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    destruct n ; [clear -Hn ; elimtype False ; omega|].
    destruct n ; [exact (thm_main_C1 Hn)|].
    generalize n, Hn ; clear n Hn Hgtype.
    induction n.
    - exact thm_main_C2.
    - intros Hn1 lambda Hradg.
      destruct lambda as [|a lambda].
      + unfold lie_is_radical_revwt_alg, lie_algebra_type in Hradg.
        rewrite Bool.andb_true_iff in Hradg.
        destruct Hradg as [Hlength Hrad].
        discriminate Hlength.
      + assert (S (S n) > 0) as Hn.
        { omega. }
        pose (IHnHn := IHn Hn).
        set (h := lie_C (exist (fun n : nat => n > 0) (S (S n)) Hn)) in *.
        assert (lie_algebra_type h = lie_C_type) as Hhtype.
        { simpl ; trivial. }
        set (g := lie_C (exist (fun n : nat => n > 0) (S (S (S n))) Hn1)) in *.
        assert (lie_algebra_type g = lie_C_type) as Hgtype.
        { simpl ; trivial. }
        assert (lie_rank g = 1 + lie_rank h) as Hrank.
        { simpl ; trivial. }
        assert (0 <= a)%Z as H0a.
        {
          unfold lie_is_radical_revwt_alg, lie_algebra_type in Hradg.
          simpl_extra in Hradg.
          tauto.
        }
        assert (a <= hd a lambda)%Z as Hahd.
        { exact (thm_C_radical_cons_le _ _ _ Hgtype Hradg). }
        destruct (Z.Even_or_Odd a) as [HaEven|HaOdd].
        {
          pose (H := IHnHn lambda
                           (thm_reduction1_radical
                              g h Hgtype Hhtype Hrank lambda a HaEven Hradg)).
          exact (thm_main_C_hd_even
                   n Hn1 a lambda Hradg Hn
                   IHnHn Hhtype Hgtype Hrank H0a Hahd HaEven).
        }
        {
          pose (Hlen := thm_radical_length _ _ Hradg) ; clearbody Hlen.
          destruct lambda as [|b lambda] ; try discriminate Hlen.
          destruct (Z.Even_or_Odd b) as [HbEven|HbOdd].
          {
            (*First component (a) is odd, second (b) is even.
             For g of odd rank (n even), subtract 1 starting from b onwards.
             For g of even rank (n odd), subtract 1 starting from a onwards.
             In both cases show that the resulting weight is mixed hence the
             original weight a::b::lambda is mixed.*)
            destruct (Nat.Even_or_Odd n) as [HnEven|HnOdd].
            {
              simpl in Hahd.
              pose (mu := a::(map (Z.add (-1)%Z) (b::lambda))).
              right ; refine (mixed_by_ideal g _ mu _ _ _).
              - pose (b' := (-1 + b)%Z).
                pose (lambda' := (map (Z.add (-1)%Z) lambda)).
                assert (b'::lambda' = map (Z.add (-1)) (b::lambda)) as Hval'.
                { trivial. }
                assert (1 <= a)%Z as H1a.
                { destruct HaOdd as [a2 Ha2] ; rewrite Ha2 ; omega. }
                assert (a <= b')%Z as Hab'.
                {
                  destruct HaOdd as [a2 Ha2] ; rewrite Ha2.
                  unfold b'.
                  destruct HbEven as [b2 Hb2] ; rewrite Hb2.
                  omega.
                }
                assert (lie_is_radical_revwt_alg g (a::b'::lambda') = true) as Hradmu.
                {
                  unfold lie_is_radical_revwt_alg.
                  simpl_extra.
                  unfold lie_is_radical_revwt_alg in Hradg.
                  simpl_extra in Hradg.
                  repeat split.
                  - unfold lambda'.
                    tac_length.
                  - refine (thm_Zvec_nondecb_join a (b'::lambda') Hab' _).
                    rewrite Hval', thm_Zvec_nondecb_plus_constant.
                    refine (thm_Zvec_nondecb_cons a (b::lambda) _).
                    tauto.
                  - assumption.
                  - destruct Hradg as [Hlen2 [[Hinc2 H0a2] Heven]].
                    rewrite <- thm_total_cons.
                    rewrite <- thm_total_cons in Heven.
                    rewrite Hval', thm_total_plus_constant, Z.add_assoc, Z.even_add, Heven, Z.even_mul, thm_Z_of_nat_even.
                    simpl.
                    rewrite <- Nat.even_spec in HnEven.
                    rewrite Hlen2, HnEven.
                    trivial.
                }
                assert (Z.Odd b') as Hb'Odd.
                {
                  destruct HbEven as [b2 Hb2].
                  unfold b'.
                  rewrite Hb2.
                  exists (-1 + b2)%Z.
                  omega.
                }
                destruct (thm_main_C_hd_odd_odd
                            n Hn1 a b' lambda' Hradmu Hn
                            IHnHn Hhtype Hgtype Hrank H0a Hab' HaOdd Hb'Odd)
                  as [Hexc|Hmix] ;
                  [|assumption].
                destruct (thm_C_exceptional_structure g _ Hgtype Hexc)
                  as [H | [[? [? H]] | [H|[H|[H|[H|H]]]]]].
                all : repeat (simpl in H ; rewrite cons_eq in H).
                all : try omega.
                all : try (destruct HaOdd as [a2 Ha2] ; rewrite Ha2 in * ; omega).
                + destruct H as [j [H1j [Hjmax H]]].
                  set (t := lie_rank g - 2 * j) in *.
                  destruct t ; simpl in H ; repeat rewrite cons_eq in H.
                  * destruct HnEven as [n2 Hn2].
                    simpl in Hlen.
                    rewrite Hn2 in Hlen.
                    assert (length (a::b'::lambda') = 2 * j) as Hlen2.
                    { rewrite H. tac_length. }
                    unfold lambda' in Hlen2.
                    simpl_length in Hlen2.
                    clear - Hlen Hlen2.
                    omega.
                  * omega.
                + destruct H as [m [H3m H]].
                  assert (length (a::b'::lambda') = 2) as Hlen2.
                  { rewrite H. trivial. }
                  rewrite Hval' in Hlen2.
                  simpl_length in Hlen2.
                  simpl_length in Hlen.
                  clear - Hlen Hlen2.
                  omega.
              - tac_length.
              - unfold mu.
                rewrite thm_Zvec_sub_add_const2.
                simpl (- -1)%Z.
                unfold lie_is_radical_revwt_alg, g, lie_is_radical_revwt_type, lie_algebra_type, lie_embedding_dim, lie_rank.
                simpl in Hlen ; repeat rewrite eq_S_iff in Hlen.
                autorewrite with rewritesome.
                repeat split.
                + tac_length.
                + tac_nondecb.
                + rewrite thm_total_cons, thm_total_repeat, Z.add_0_l, Z.mul_1_r, thm_Z_of_nat_even.
                  destruct HnEven as [n2 Hn2].
                  rewrite Hn2 in Hlen.
                  simpl length ; rewrite Hlen.
                  rewrite Nat.even_spec.
                  exists (S n2).
                  omega.
            }
            {
              pose (mu := (map (Z.add (-1)%Z) (a::b::lambda))).
              right ; refine (mixed_by_ideal g _ mu _ _ _).
              - pose (a' := (-1 + a)%Z).
                pose (b' := (-1 + b)%Z).
                pose (lambda' := (map (Z.add (-1)%Z) lambda)).
                assert (mu = a'::b'::lambda') as Hmuval.
                { trivial. }
                assert (1 <= a)%Z as H1a.
                { destruct HaOdd as [a2 Ha2] ; rewrite Ha2 ; omega. }
                assert (0 <= a')%Z as H0a'.
                { unfold a' ; omega. }
                assert (lie_is_radical_revwt_alg g (a'::b'::lambda') = true) as Hradmu.
                {
                  unfold lie_is_radical_revwt_alg.
                  simpl_extra.
                  unfold lie_is_radical_revwt_alg in Hradg.
                  simpl_extra in Hradg.
                  repeat split.
                  - unfold lambda'.
                    simpl_length in Hlen.
                    tac_length.
                  - rewrite <- Hmuval.
                    unfold mu.
                    rewrite thm_Zvec_nondecb_plus_constant.
                    tauto.
                  - assumption.
                  - destruct Hradg as [Hlen2 [[Hinc2 H0a2] Heven]].
                    rewrite <- thm_total_cons, <- thm_total_cons in Heven.
                    rewrite <- thm_total_cons, <- thm_total_cons, <- Hmuval.
                    unfold mu.
                    rewrite thm_total_plus_constant, Hlen, Z.even_add, Heven.
                    rewrite Z.even_mul.
                    unfold lie_embedding_dim, g, lie_rank.
                    repeat rewrite thm_Z_of_nat_S.
                    autorewrite with rewriteeven.
                    rewrite thm_Z_of_nat_even, (thm_Odd_even_false _ HnOdd).
                    trivial.
                }
                assert (a' <= hd a' (b'::lambda'))%Z as Ha'hd.
                {
                  unfold b', lambda', map, hd, a'.
                  unfold hd in Hahd.
                  omega.
                }
                assert (Z.Even a') as Ha'Even.
                {
                  destruct HaOdd as [a2 Ha2].
                  unfold a'.
                  rewrite Ha2.
                  exists a2.
                  omega.
                }
                destruct (thm_main_C_hd_even
                            _ Hn1 a' (b'::lambda') Hradmu Hn
                            IHnHn Hhtype Hgtype Hrank H0a' Ha'hd Ha'Even)
                  as [Hexc|Hmix] ;
                  [elimtype False|assumption].
                simpl in Hahd.
                assert (1 <= b')%Z as H1b'.
                { destruct HbEven as [b2 Hb2] ; unfold b' ; rewrite Hb2 ; omega. }
                assert (forall m nu, a'::b'::lambda' <> m::m::nu) as Hconsneq.
                {
                  intros m nu H.
                  rewrite cons_eq, cons_eq in H.
                  destruct HaOdd as [a2 Ha2].
                  unfold a' in H.
                  rewrite Ha2 in H.
                  destruct HbEven as [b2 Hb2].
                  unfold b' in H.
                  rewrite Hb2 in H.
                  omega.
                }
                destruct (thm_C_exceptional_structure g _ Hgtype Hexc)
                  as [H|[H|[H|[H|[H|[H|H]]]]]].
                + simpl in H.
                  rewrite cons_eq, cons_eq in H.
                  omega.
                + destruct H as [m [H0m H]].
                  contradiction (Hconsneq _ _ H).
                + destruct H as [j [H1j [Hjmax H]]].
                  destruct (le_lt_eq_dec _ _ Hjmax) as [H0|H0].
                  {
                    assert (1 <= lie_rank g - 2 * j) as H1.
                    { omega. }
                    destruct (le_lt_eq_dec _ _ H1) as [H2|H2].
                    - set (t := lie_rank g - 2 * j) in *.
                      destruct t as [|[|]] ; try omega.
                      contradiction (Hconsneq _ _ H).
                    - rewrite <- H2 in *.
                      destruct HnOdd as [n2 Hn2].
                      simpl lie_rank in H2.
                      rewrite Hn2 in H2.
                      clear -H2.
                      omega.
                  }
                  {
                    rewrite <- H0, Nat.sub_diag in *.
                    simpl in H.
                    rewrite (repeat_spec_hd _ _ _ _ _ H), <- Z.even_spec, Z.even_1 in Ha'Even.
                    discriminate Ha'Even.
                  }
                + destruct HbEven as [b2 Hb2].
                  unfold b' in H.
                  rewrite Hb2 in H.
                  destruct n ;
                  simpl repeat in H;
                  simpl app in H ;
                  rewrite cons_eq, cons_eq in H ;
                  destruct H as [_ [H _]] ;
                  omega.
                + destruct H as [m [H3m H]].
                  contradiction (Hconsneq _ _ H).
                + contradiction (Hconsneq _ _ H).
                + contradiction (Hconsneq _ _ H).
              - clear ; tac_length.
              - unfold mu.
                rewrite thm_Zvec_sub_add_const.
                simpl (- -1)%Z.
                rewrite Hlen.
                unfold lie_is_radical_revwt_alg, g, lie_algebra_type, lie_is_radical_revwt_type, lie_embedding_dim, lie_rank.
                autorewrite with rewritesome.
                repeat split.
                + clear ; tac_length.
                + refine (thm_Zvec_nondecb_join _ _ _ _).
                  simpl ; omega.
                  fold (repeat 1%Z (S (S n))).
                  refine (thm_Zvec_nondecb_repeat _ _).
                + rewrite thm_total_repeat, thm_Z_of_nat_S, thm_Z_of_nat_S, thm_Z_of_nat_S, Z.mul_1_r.
                  autorewrite with rewriteeven.
                  rewrite thm_Z_of_nat_even.
                  rewrite <- Nat.odd_spec in HnOdd.
                  rewrite <- Nat.negb_odd, HnOdd.
                  trivial.
            }
          }
          {
            exact (thm_main_C_hd_odd_odd
                     n Hn1 a b lambda Hradg Hn
                     IHnHn Hhtype Hgtype Hrank H0a Hahd HaOdd HbOdd).
          }
        }
  Qed.
End main.
