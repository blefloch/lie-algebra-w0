Require Import ZArith.
(*Load our files*)
Require Data.

Section theorems_for_all_types.
  Theorem thm_exceptional_multiplier_nonneg :
    forall g i m,
      Data.is_exceptional_multiplier g i m = true
      -> (0 <= m)%Z.
  Proof.
    intros g i m.
    destruct (Z_lt_le_dec m 0) as [H|H].
    - unfold Data.is_exceptional_multiplier.
      rewrite Zlt_is_lt_bool in H.
      rewrite H.
      firstorder.
    - firstorder.
  Qed.
End theorems_for_all_types.
