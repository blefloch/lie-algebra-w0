Require SimpleLieAlgebras.
Require Data.
Require TypeA.
Require TypeBD.
Require TypeC.
Require TypeEFG.
Open Scope nat_scope.

Theorem main :
  forall g lambda,
    SimpleLieAlgebras.Is_radical g lambda
    -> (Data.Is_nonmixed g lambda) \/ (Data.Is_mixed g lambda).
Proof.
  intros g lambda Hrad.
  destruct g.
  - refine (TypeA.thm_main_A _ _ _ Hrad) ; firstorder.
  - refine (TypeBD.thm_main_B _ _ _ Hrad) ; firstorder.
  - refine (TypeC.thm_main_C _ _ _ Hrad) ; firstorder.
  - refine (TypeBD.thm_main_D _ _ _ Hrad) ; firstorder.
  - refine (TypeEFG.thm_main_E6 _ _ _ Hrad) ; firstorder.
  - refine (TypeEFG.thm_main_E7 _ _ _ Hrad) ; firstorder.
  - refine (TypeEFG.thm_main_E8 _ _ _ Hrad) ; firstorder.
  - refine (TypeEFG.thm_main_F4 _ _ _ Hrad) ; firstorder.
  - refine (TypeEFG.thm_main_G2 _ _ _ Hrad) ; firstorder.
Qed.
