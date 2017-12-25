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

(*TODO: move*)
Theorem thm_repeat_cons :
  forall A (a : A) p, a :: repeat a p = repeat a (S p).
Proof.
  trivial.
Qed.
Theorem repeat_tl :
  forall A (a : A) n, tl (repeat a n) = repeat a (n - 1).
Proof.
  destruct n ; simpl ; firstorder.
Qed.
Theorem thm_eq_repeat_fact :
  forall A (a : A) lambda n,
    lambda = repeat a n -> lambda = repeat a (length lambda).
Proof.
  induction lambda.
  - simpl ; tauto.
  - simpl.
    destruct n.
    + simpl ; discriminate.
    + simpl.
      intros H.
      injection H.
      intros H0 H1.
      rewrite <- (IHlambda _ H0), H1.
      trivial.
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

Theorem thm_i_n_cases :
  forall i n,
    ((i =? 0) = true /\ i = 0)
    \/ ((n <? i) = true /\ n < i)
    \/ ((i =? 0) = false /\ (n <? i) = false /\ 1 <= i /\ i <= n).
Proof.
  intros.
  destruct i.
  - tauto.
  - right.
    destruct (le_lt_dec (S i) n).
    + right.
      rewrite Nat.ltb_ge, Nat.eqb_neq.
      omega.
    + left.
      rewrite Nat.ltb_lt.
      tauto.
Qed.

Theorem thm_apply_if_then_else :
  forall A B (f : A -> B) x y (b : bool),
    f (if b then x else y)
    = if b then f x else f y.
Proof.
  destruct b ; trivial.
Qed.
Theorem thm_args_if_then_else :
  forall A B (f g : A -> B) x (b : bool),
    (if b then f else g) x
    = if b then f x else g x.
Proof.
  destruct b ; trivial.
Qed.
Theorem thm_if_then_else_same :
  forall A (x : A) (b : bool),
    (if b then x else x) = x.
Proof.
  destruct b ; trivial.
Qed.
Theorem thm_if_then_else_same_prop :
  forall (P : Prop) (b : bool),
    (if b then P else P) <-> P.
Proof.
  destruct b ; tauto.
Qed.

Theorem thm_if_then_false_else :
  forall b1 b3 : bool,
    (if b1 then false else b3)
    = negb b1 && b3.
Proof.
  destruct b1, b3 ; simpl ; trivial.
Qed.
Theorem thm_if_then_true_else :
  forall b1 b3 : bool,
    (if b1 then true else b3)
    = b1 || b3.
Proof.
  destruct b1, b3 ; simpl ; trivial.
Qed.
Theorem thm_if_then_else :
  forall b1 b2 b3 : bool,
    (if b1 then b2 else b3)
    = (b1 && b2) || (negb b1 && b3).
Proof.
  destruct b1, b2, b3 ; simpl ; trivial.
Qed.

Hint Rewrite
     thm_if_then_false_else
     thm_if_then_true_else
     andb_false_l
     andb_false_r
     andb_true_l
     andb_true_r
     orb_false_l
     orb_false_r
     orb_true_l
     orb_true_r
     andb_true_iff
     andb_false_iff
     orb_true_iff
     orb_false_iff
     negb_andb
     negb_orb
     negb_involutive
     negb_false_iff
     negb_true_iff
     Z.negb_odd
     Z.negb_even
     Z.ltb_ge
     Z.eqb_eq
     Z.leb_le
     Nat.ltb_ge
     Nat.eqb_eq
     Nat.leb_le
: rewritebool.

Theorem thm_lie_zero_is_radical :
  forall g, lie_is_radical_revwt_alg
              g (repeat 0%Z (lie_embedding_dim g)) = true.
Proof.
  intros g.
  pose (rk := lie_rank g).
  destruct g as [[n Hn]|[n Hn]|[n Hn]|[n Hn]| | | | |].
  all : simpl in rk.
  all : unfold lie_is_radical_revwt_alg, lie_embedding_dim,
        lie_rank, lie_algebra_type, lie_is_radical_revwt_type.
  all : repeat rewrite thm_Zvec_nondecb_repeat.
  all : repeat rewrite thm_Zvec_total_repeat.
  all : repeat rewrite repeat_length.
  all : repeat rewrite repeat_tl.
  all : repeat rewrite Z.mul_0_r.
  all : repeat rewrite Z.even_0.
  all : repeat rewrite thm_hd_repeat, thm_if_then_else_same.
  all : repeat rewrite Z.eqb_refl.
  all : repeat rewrite Z.leb_refl.
  all : repeat rewrite Nat.eqb_refl.
  all : repeat rewrite andb_true_l.
  all : try tauto.
Qed.

(*TODO: split out a lemma about the length*)
Theorem thm_lie_fundamental_revwt_is_radical :
  forall g i, lie_is_radical_revwt_alg
                g (lie_radical_fundamental_revwt_alg g i) = true.
Proof.
  intros g i.
  pose (rk := lie_rank g).
  destruct g as [[n Hn]|[n Hn]|[n Hn]|[n Hn]| | | | |].
  all : simpl in rk.
  all : unfold lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank.
  all : destruct (thm_i_n_cases i rk)
    as [[Hib Hi]|[[Hnib Hni]|[Hib [Hnib [Hi Hni]]]]].
  all : try unfold rk in *.
  all : try rewrite Hib.
  all : try rewrite Hnib.
  all : autorewrite with rewritebool.
  all : try apply thm_lie_zero_is_radical.
  all : unfold lie_is_radical_revwt_alg, lie_algebra_type, lie_embedding_dim, lie_rank.
  all : unfold lie_is_radical_revwt_type.
  all : autorewrite with rewritelength rewritetotal.
  all : repeat rewrite thm_Zvec_nondecb_app_iff.
  all : repeat rewrite thm_Zvec_nondecb_repeat.
  all : repeat (rewrite Nat.sub_add ; [|omega]).
  all : repeat rewrite Nat.eqb_refl.
  all : repeat rewrite Z.eqb_refl.
  all : repeat rewrite andb_true_l.
  all : repeat rewrite thm_hd_app.
  all : repeat rewrite thm_hd_repeat.
  all : try rewrite Hib.
  all : autorewrite with rewritesome.
  all : try rewrite thm_Zvec_nondecb_app_iff.
  all : repeat rewrite thm_Zvec_nondecb_repeat.
  all : repeat rewrite true_eq_true.
  all : repeat rewrite or_True_iff2.
  - split.
    + destruct i.
      * simpl ; tauto.
      * assert (forall A (x : A), repeat x (S i) = x::(repeat x i)) as H.
        { tauto. }
        rewrite H, thm_last_repeat.
        assert (S n - S i <> 0) as H0.
        { omega. }
        rewrite <- Nat.eqb_neq in H0.
        rewrite H0.
        refine (Z_div_le _ _ _ (thm_gcd_nat1 (S i) n) _).
        rewrite Nat2Z.inj_sub_max.
        rewrite Z.max_le_iff, Z.opp_nonpos_nonneg.
        left.
        exact (Zle_0_nat _).
    + rewrite (Nat2Z.inj_sub (S n) i) ; [| omega].
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
      omega.
  - split.
    + destruct i ; simpl ; intuition.
      rewrite thm_last_repeat.
      destruct (n - S i) ; simpl ; firstorder.
    + destruct (n - i =? 0) ; firstorder.
  - destruct (Nat.Even_or_Odd i).
    + rewrite ((match Nat.even_spec i with conj _ x => x end) H).
      repeat split.
      * destruct i ; simpl ; intuition.
        rewrite thm_last_repeat.
        destruct (n - S i) ; simpl ; firstorder.
      * destruct (n - i =? 0) ; firstorder.
      * simpl.
        rewrite Z.mul_1_r, Z.even_spec.
        destruct H as [j Hj].
        exists (Z.of_nat j).
        rewrite Hj, Nat2Z.inj_mul.
        intuition.
    + pose (H2 := (match Nat.odd_spec i with conj _ x => x end) H).
      rewrite <- Nat.negb_even, negb_true_iff in H2.
      rewrite H2.
      repeat split.
      * destruct i ; simpl ; intuition.
        rewrite thm_last_repeat.
        destruct (n - S i) ; simpl ; firstorder.
      * destruct (n - i =? 0) ; firstorder.
      * simpl.
        apply thm_Zeven_mul_2_r.
  - repeat split.
    + repeat (rewrite thm_apply_if_then_else || rewrite thm_args_if_then_else).
      simpl_length.
      repeat rewrite thm_if_then_else_same.
      destruct (i =? n - 1) ; omega.
    + repeat (rewrite thm_apply_if_then_else || rewrite thm_args_if_then_else).
      destruct (i =? n - 1) ; [destruct (even n) | destruct (even i)].
      all : try refine (thm_Zvec_nondecb_join _ _ _ _).
      all : try refine (thm_Zvec_nondecb_app2 _ _ _ _ _).
      all : try exact (thm_Zvec_nondecb_repeat _ _).
      all : try rewrite thm_hd_repeat.
      all : try (destruct (n - 1 =? 0) ; omega).
      all : destruct i ; simpl ; intuition.
      all : rewrite thm_last_repeat.
      all : destruct (n - S i) ; simpl ; firstorder.
    + repeat rewrite (thm_apply_if_then_else _ _ (tl (A := Z))).
      repeat rewrite (thm_apply_if_then_else _ _ (hd 0%Z)).
      simpl hd.
      destruct (i =? n - 1) ;
        [destruct (even n) |
         destruct (even i) ; destruct (n - i)].
      all : simpl.
      all : repeat rewrite repeat_tl.
      all : repeat rewrite thm_hd_app.
      all : repeat rewrite thm_hd_repeat.
      all : try (destruct (i =? 0), (i - 1 =? 0) ; omega).
      all : try (destruct (n0 =? 0), (i =? 0) ; omega).
      all : destruct n as [|[|]] ; simpl ; omega.
    + repeat (rewrite thm_apply_if_then_else || rewrite thm_args_if_then_else).
      destruct (i =? n - 1) ; [set (t := n) in * | set (t := i) in *].
      all : destruct (Nat.Even_or_Odd t) as [H|H].
      all : try rewrite ((match Nat.even_spec _ with conj _ x => x end) H).
      all : try (pose (H2 := (match Nat.odd_spec _ with conj _ x => x end) H) ;
                 rewrite <- Nat.negb_even, negb_true_iff in H2 ;
                 rewrite H2 ;
                 clear H2).
      all : unfold Zvec_total ; fold Zvec_total.
      all : autorewrite with rewritetotal.
      all : destruct H as [u Hu].
      all : rewrite Hu.
      all : repeat ((rewrite Nat2Z.inj_add)
                      || (rewrite Nat2Z.inj_sub ; [|omega])
                      || (rewrite Nat2Z.inj_mul)).
      all : simpl Z.of_nat.
      all : autorewrite with rewriteeven.
      all : tauto.
  - repeat (destruct i ; simpl ; intuition ; try omega).
  - repeat (destruct i ; simpl ; intuition ; try omega).
  - repeat (destruct i ; simpl ; intuition ; try omega).
  - repeat (destruct i ; simpl ; intuition ; try omega).
  - repeat (destruct i ; simpl ; intuition ; try omega).
Qed.
Theorem thm_zero_is_exceptional_revwt :
  forall g, Is_exceptional_revwt_alg g (repeat 0%Z (lie_embedding_dim g)).
Proof.
  intros g.
  exists 1, 0%Z.
  unfold is_exceptional_multiplier.
  rewrite Z.ltb_irrefl, Z.eqb_refl, thm_Zvec_mul_0.
  pose (H := thm_lie_fundamental_revwt_is_radical g 1).
  unfold lie_is_radical_revwt_alg in H.
  rewrite andb_true_iff, Nat.eqb_eq in H.
  destruct H as [H _].
  rewrite H.
  tauto.
Qed.

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
End generalities.


    
Section exceptional_structure.
  (*TODO: refactor this repetitive proof; near the end the code is better.*)
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
      rewrite map_app, thm_repeat_map, Z.mul_0_r.
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
        rewrite map_app, thm_repeat_map, thm_repeat_map.
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
      rewrite map_app, thm_repeat_map.
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
        rewrite map_app, thm_repeat_map, Z.mul_0_r.
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
    rewrite Hval, thm_repeat_cons, <- Hrank.
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
    rewrite H, app_comm_cons, thm_repeat_cons, minus_Sn_m, <- Hrank ;
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
      rewrite map_app, thm_repeat_map, Z.mul_0_r.
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
    rewrite H, app_comm_cons, thm_repeat_cons, minus_Sn_m, <- Hrank ; [|omega].
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
    rewrite H, app_comm_cons, thm_repeat_cons, minus_Sn_m, <- Hrank ; [|omega].
    unfold is_exceptional_multiplier, lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank, Zvec_mul.
    assert (n <? 2 = false) as H0.
    { rewrite Nat.ltb_ge. omega. }
    rewrite H0.
    simpl.
    rewrite map_app, thm_repeat_map.
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
    assert (Z.even (Zvec_total (mun1 :: mun :: mu)) = true).
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
           | [ |- context[Z.even] ]
             => (progress autorewrite with rewriteeven in *)
                  || (repeat destruct (Z.even _))
           | [ |- _ ] => try rewrite Hnval ; simpl ; intuition ; try omega
         end.
(*TODO: move*)
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

Section C3.
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
                  rewrite H) ;
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
    unfold lie_is_radical_revwt_alg, lie_algebra_type, g, lie_is_radical_revwt_type, Zvec_nondecb, Zvec_total in Hrad.
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
(*
  Theorem thm_main_C3 :
    forall (Hn : 3 > 0) (lambda : list Z),
      let g := lie_C (exist (fun n : nat => n > 0) 3 Hn) in
      lie_is_radical_revwt_alg g lambda = true
      -> Is_exceptional_revwt_alg g lambda
         \/ Is_mixed_revwt_alg g lambda.
  Proof.
    intros Hn lambdacopy g Hrad.
    unfold lie_is_radical_revwt_alg, lie_algebra_type, g, lie_is_radical_revwt_type in Hrad.
    simpl_destruct Hrad as [Hlength [[Hinc H0a] Htot]].
    pose (lambda := lambdacopy).
    destruct lambdacopy as [|a [|b [|c [|]]]] ; simpl in Hlength ; try omega.
    simpl in *.
    rewrite Z.add_0_r in Htot.
    unfold Zvec_nondecb in Hinc.
    simpl_destruct Hinc as [Hab Hbc].
    destruct (Z_le_lt_eq_dec _ _ H0a) as [H0lta|H0eqa] ;
      destruct (Z_le_lt_eq_dec _ _ Hab) as [Haltb|Haeqb] ;
      destruct (Z_le_lt_eq_dec _ _ Hbc) as [Hbltc|Hbeqc].
    all : try rewrite <- H0eqa in *.
    all : try rewrite <- Haeqb in *.
    all : try rewrite <- Hbeqc in *.
    all : try (rewrite Z.even_add, Z.even_add,
               eqb_reflx, eqb_true_iff in Htot ;
               pose (H2lea := thm_Z_even_pos a Htot H0lta) ;
               clearbody H2lea).
    - show_mixed_by_ideal g (1::1::2::nil)%Z.
    - show_mixed_by_ideal g (2::3::3::nil)%Z.
    - show_mixed_by_ideal g (1::1::2::nil)%Z.
    - destruct (Zle_lt_or_eq _ _ H2lea) as [H2a|H2a].
      + assert (3 <= a)%Z as H.
        { omega. }
        destruct (Zle_lt_or_eq _ _ H) as [H0|H0].
        * show_mixed_by_ideal g (4::4::4::nil)%Z.
        * rewrite <- H0 in *.
          discriminate Htot.
      + rewrite <- H2a in *.
        left.
        exists 3, 1%Z.
        compute.
        tauto.
    - assert (1 + b <= c)%Z as H.
      { omega. }
      destruct (Zle_lt_or_eq _ _ H) as [H0|H0].
      + show_mixed_by_ideal g (0::1::3::nil)%Z.
      + rewrite <- H0 in Htot.
        clear -Htot.
        rewrite Z.even_add, Z.even_add, Z.even_add in Htot.
        destruct (Z.even b) in Htot ; compute in Htot ; discriminate Htot.
    - assert (1 <= b)%Z as H.
      { omega. }
      destruct (Zle_lt_or_eq _ _ H) as [H0|H0].
      + assert (2 <= b)%Z as H1.
        { omega. }
        destruct (Zle_lt_or_eq _ _ H1) as [H2|H2].
        * show_mixed_by_ideal g (0::3::3::nil)%Z.
        * rewrite <- H2 in *.
          left.
          exists 2, 2%Z.
          compute.
          tauto.
      + rewrite <- H0 in *.
        left.
        exists 2, 1%Z.
        compute.
        tauto.
    - left.
      simpl in Htot.
      rewrite Z.even_spec in Htot.
      destruct Htot as [c2 Hc].
      rewrite Hc in *.
      exists 1, c2.
      unfold is_exceptional_multiplier, lie_radical_fundamental_revwt_alg, g, lie_embedding_dim, lie_rank.
      assert (((1 =? 0) || (3 <? 1)) = false) as H0.
      { simpl. rewrite Nat.ltb_nlt. omega. }
      rewrite H0.
      split.
      + assert (~(c2 < 0)%Z) as Hc1 ; [omega|].
        assert (~(c2 = 0)%Z) as Hc2 ; [omega|].
        rewrite <- Z.ltb_nlt in Hc1.
        rewrite <- Z.eqb_neq in Hc2.
        rewrite Hc1, Hc2.
        compute.
        trivial.
      + rewrite <- Hc.
        simpl.
        rewrite Z.mul_0_r, Z.mul_comm.
        rewrite Hc.
        trivial.
    - left.
      exists 1, 0%Z.
      compute.
      tauto.
  Qed.
 *)
End C3.

Section main.
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
          destruct (IHnHn lambda
                          (thm_reduction1_radical
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
              rewrite H, thm_hd_app, thm_hd_repeat, thm_hd_repeat, H1 in Hahd.
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
              rewrite H, thm_hd_app, thm_hd_repeat in Hahd.
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
        }
        {
          (*First component is odd.*)
          admit.
        }
  Admitted.
End main.
