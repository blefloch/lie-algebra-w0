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
Open Scope nat_scope.

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
End theorems_for_all_types.
