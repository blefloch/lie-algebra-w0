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
Require Import TypeA.
Require Import TypeBD.
Require Import TypeC.
Require Import TypeEFG.
Open Scope nat_scope.

Theorem main :
  forall g lambda,
    lie_is_radical_revwt_alg g lambda = true
    -> (Is_exceptional_revwt_alg g lambda) \/ (Is_mixed_revwt_alg g lambda).
Proof.
  intros g lambda Hrad.
  pose (Hlength := thm_radical_length _ _ Hrad).
  pose (gcopy := g).
  pose (lambdacopy := lambda).
  destruct g as [[n Hn]|[n Hn]|[n Hn]|[n Hn]| | | | |].
  - refine (thm_main_A _ _ _ Hrad) ; firstorder.
  - refine (thm_main_B _ _ _ Hrad) ; firstorder.
  - refine (thm_main_C _ _ _ Hrad) ; firstorder.
  - refine (thm_main_D _ _ _ Hrad) ; firstorder.
  - refine (thm_main_E6 _ _ _ Hrad) ; firstorder.
  - refine (thm_main_E7 _ _ _ Hrad) ; firstorder.
  - refine (thm_main_E8 _ _ _ Hrad) ; firstorder.
  - refine (thm_main_F4 _ _ _ Hrad) ; firstorder.
  - refine (thm_main_G2 _ _ _ Hrad) ; firstorder.
Qed.

(*TODO: look up split, combine*)
(*TODO: look up "fold"*)