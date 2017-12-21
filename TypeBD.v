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

Theorem thm_main_B :
  forall g,
    lie_algebra_type g = lie_B_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_D :
  forall g,
    lie_algebra_type g = lie_D_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
