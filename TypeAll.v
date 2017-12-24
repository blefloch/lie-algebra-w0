Require Import ZArith.
Require Import List.
(*Load our files*)
Require Import Zvec.
Require Import SimpleLieAlgebras.
Require Import Data.

Section theorems_for_all_types.
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
End theorems_for_all_types.
