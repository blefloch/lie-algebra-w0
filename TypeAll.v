Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Nat.
Open Scope nat_scope.
(*Load our files*)
Require Import ListExtras.
Require Import Tools.
Require Import Zvec.
Require Import SimpleLieAlgebras.
Require Import Data.

Section radical_dominant.
  Theorem thm_dominant_length :
    forall g lambda,
      lie_is_dominant_revwt_alg g lambda = true
      -> length lambda = lie_embedding_dim g.
  Proof.
    intros g lambda H.
    unfold lie_is_dominant_revwt_alg in H.
    rewrite Bool.andb_true_iff, Nat.eqb_eq in H.
    destruct H as [H _].
    assumption.
  Qed.
  Theorem thm_radical_dominant :
    forall g lambda,
      lie_is_radical_revwt_alg g lambda = true
      -> lie_is_dominant_revwt_alg g lambda = true.
  Proof.
    intros g lambda Hrad.
    unfold lie_is_radical_revwt_alg, lie_is_dominant_revwt_alg in *.
    rewrite Bool.andb_true_iff in *.
    destruct Hrad as [Hlength Hrad].
    split.
    - assumption.
    - destruct (lie_algebra_type g).
      all : unfold lie_is_radical_revwt_type, lie_is_dominant_revwt_type in *.
      all : rewrite Bool.andb_true_iff in *.
      all : try rewrite Bool.andb_true_iff in *.
      all : firstorder.
      all : repeat (destruct lambda ; try discriminate Hrad).
      all : try rewrite Bool.andb_true_iff in *.
      all : simpl ; firstorder.
  Qed.
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
  Local Theorem thm_i_n_cases :
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
End radical_dominant.

Section exceptional.
  Theorem thm_exceptional_multiplier_nonneg :
    forall g i m,
      is_exceptional_multiplier g i m = true
      -> (0 <= m)%Z.
  Proof.
    intros g i m.
    destruct (Z_lt_le_dec m 0) as [H|H].
    - unfold is_exceptional_multiplier.
      rewrite Zlt_is_lt_bool in H.
      rewrite H.
      firstorder.
    - firstorder.
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
End exceptional.

Section mixed.
  Theorem thm_mixed_is_radical :
    forall g lambda,
      Is_mixed_revwt_alg g lambda
      -> lie_is_radical_revwt_alg g lambda = true.
  Proof.
    intros g lambda H.
    induction H.
    - unfold is_mixed_by_hand_revwt_alg in H.
      rewrite Bool.andb_true_iff in H.
      destruct H as [H _].
      assumption.
    - unfold lie_is_radical_revwt_alg in *.
      rewrite Bool.andb_true_iff in *.
      destruct H1 as [H1 H2].
      destruct IHIs_mixed_revwt_alg as [IHl IHrad].
      split.
      + rewrite H0. assumption.
      + destruct g.
        all : unfold lie_algebra_type, lie_is_radical_revwt_type in *.
        all : repeat rewrite Bool.andb_true_iff in *.
        all : repeat match goal with
                       | [H : _ /\ _ |- _ ] => destruct H
                       | [ |- _ /\ _ ] => split
                       | [H0 : length ?lambda = length ?mu,
                          H1 : Zvec_nondecb ?mu = true,
                          H2 : Zvec_nondecb (Zvec_short_sub ?lambda ?mu) = true
                          |- Zvec_nondecb ?lambda = true ]
                         => exact (thm_Zvec_nondecb_from_sub lambda mu H0 H1 H2)
                       | [H : (_ =? _)%Z = true |- _ ] => rewrite Z.eqb_eq in *
                       | [ |- (_ =? _)%Z = true ] => rewrite Z.eqb_eq in *
                       | [H : (_ =? _)%nat = true |- _ ] => rewrite Nat.eqb_eq in *
                       | [ |- (_ =? _)%nat = true ] => rewrite Nat.eqb_eq in *
                       | [H : length ?lambda = length ?mu
                          |- context [Zvec_total ?lambda] ]
                         => rewrite (thm_Zvec_total_from_sub lambda mu H)
                       | [H : Zvec_total ?mu = _ |- context[Zvec_total ?mu] ]
                         => rewrite H ; intuition
                       | [H : (_ <=? _)%Z = true |- _ ] => rewrite Z.leb_le in *
                       | [ |- (_ <=? _)%Z = true ] => rewrite Z.leb_le in *
                       | [ |- context [hd 0%Z ?lambda] ]
                         => unfold Zvec_short_sub in * ;
                           destruct lambda, mu ;
                           simpl in * ;
                           intuition
                       | [ |- context[Z.even (_ + _)%Z] ]
                         => rewrite Z.even_add, Bool.eqb_true_iff ; simpl
                       | [ H : ?b = true |- context[?b] ]
                         => rewrite H ; intuition
                       | [ H : length ?lambda = length ?mu |- length ?lambda = _ ]
                         => rewrite H ; assumption
                       | [H0 : length ?lambda = length ?mu,
                          H1 : Zvec_all_nonnegb ?mu = true,
                          H2 : Zvec_all_nonnegb (Zvec_short_sub ?lambda ?mu) = true
                          |- Zvec_all_nonnegb ?lambda = true ]
                         => exact (thm_Zvec_nonnegb_from_sub lambda mu H0 H1 H2)
                     end.
        all : simpl in *.
        all : destruct mu as [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 mu]]]]]]]].
        all : try discriminate IHl.
        all : simpl in *.
        all : destruct lambda as [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|a8 lambda]]]]]]]].
        all : try discriminate H0.
        all : simpl in *.
        all : rewrite Bool.andb_true_iff in *.
        all : intuition.
        all : try exact ((fun H => thm_Zvec_nonnegb_from_sub _ _ H H2 H3) eq_refl).
        assert (3 <> 0)%Z as H6 ; [discriminate|].
        all : try rewrite Z.eqb_eq, (Zmod_divides _ _ H6) in H4.
        all : try rewrite Z.eqb_eq, (Zmod_divides _ _ H6) in H5.
        all : try rewrite Z.eqb_eq, (Zmod_divides _ _ H6).
        all : try rewrite Z.even_spec in *.
        all : destruct H4 as [x H4].
        all : destruct H5 as [y H5].
        all : exists (x + y)%Z.
        all : omega.
    - unfold Is_known_w0_branching_revwt_alg in H0.
      intuition.
  Qed.
End mixed.
