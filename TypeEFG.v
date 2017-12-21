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

Theorem thm_main_E6 :
  forall g,
    lie_algebra_type g = lie_E6_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_E7 :
  forall g,
    lie_algebra_type g = lie_E7_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_E8 :
  forall g,
    lie_algebra_type g = lie_E8_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_F4 :
  forall g,
    lie_algebra_type g = lie_F4_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_G2 :
  forall g,
    lie_algebra_type g = lie_G2_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
