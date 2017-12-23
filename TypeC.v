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
Theorem thm_even_is_2_mul :
  forall a, Z.even a = true -> exists b, a = (2 * b)%Z.
Proof.
  intros.
  destruct a as [|[]|[]].
  all : simpl in * ; try discriminate H.
  - exists 0%Z ; trivial.
  - exists (Z.pos p) ; trivial.
  - exists (Z.neg p) ; trivial.
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
: rewriteeven.

Section C3.
  (*
  Ltac show_mixed_by_ideal g lambda mu :=
    match goal with
      | [ |- _]
        =>
        (right;
         refine (mixed_by_ideal g lambda mu _ _ _) ;
         [
           refine (mixed_by_hand g mu _) ;
           unfold g ;
           simpl ; trivial
         |
         tac_length
         |
         unfold g ;
           unfold Zvec_short_sub, lie_is_radical_revwt_alg ;
           simpl ;
           unfold Zvec_nondecb ;
           simpl_extra ;
           omega
        ])
    end.
   *)
  Ltac show_mixed_by_ideal g mu :=
    repeat match goal with
             | [ |- _ /\ _ ] => split
             | [ |- _ \/ Is_mixed_revwt_alg _ _ ]
               => right ; refine (mixed_by_ideal g _ mu _ _ _)
             | [ |- Is_mixed_revwt_alg g mu ]
               => exact (mixed_by_hand g mu eq_refl)
             | [ |- length _ = length mu ]
               => exact eq_refl
             | [ |- lie_is_radical_revwt_alg g (Zvec_short_sub _ mu) = true ]
               => unfold Zvec_short_sub, lie_is_radical_revwt_alg ;
                 simpl ;
                 unfold Zvec_nondecb ;
                 simpl_extra
             | [ |- context[Z.even] ]
               => (progress autorewrite with rewriteeven in *)
                    || (repeat destruct (Z.even _))
             | [ |- _ ] => simpl ; firstorder ; try omega
           end.
  Theorem thm_main_C3 :
    forall (Hn : 3 > 2) (lambda : list Z),
      let g := lie_C (exist (fun n : nat => n > 2) 3 Hn) in
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
      destruct (thm_even_is_2_mul _ Htot) as [c2 Hc].
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
    destruct n as [|[|[|n]]].
    all : try (clear -Hn; elimtype False; omega).
    generalize n, Hn. clear n Hn Hgtype.
    induction n.
    - exact thm_main_C3.
    - intros Hn1 lambda Hrad.
      unfold lie_is_radical_revwt_alg, lie_algebra_type in Hrad.
      autorewrite with rewritesome in Hrad.
      destruct Hrad as [Hlength Hrad].
      simpl in Hlength.
      assert (S (S (S n)) > 2) as Hn.
      { omega. }
      pose (h := lie_C (exist (fun n : nat => n > 2) (S (S (S n))) Hn)).
      assert (lie_algebra_type h = lie_C_type) as Hhtype.
      { simpl ; trivial. }
      admit.
  Admitted.
End main.
