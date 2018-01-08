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
         is_radical g lambda = true
         -> (Is_nonmixed g lambda)
            \/ (Is_mixed g lambda).
Admitted.
Theorem thm_main_D :
  forall g,
    lie_algebra_type g = lie_D_type
    -> forall lambda,
         is_radical g lambda = true
         -> (Is_nonmixed g lambda)
            \/ (Is_mixed g lambda).
Admitted.
