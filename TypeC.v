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

Theorem thm_main_C :
  forall g,
    lie_algebra_type g = lie_C_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
