Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Load our files*)
Require Import ListExtras.
Open Scope nat_scope.

Section rewrite_helpers.
  Definition Zleb_iff n m : (n <=? m)%Z = true <-> (n <= m)%Z :=
    conj (Zle_bool_imp_le n m) (Zle_imp_le_bool n m).
  Definition true_eq_true : true = true <-> True :=
    conj (fun _ => I) (fun _ => eq_refl).
  Definition or_True_iff P : P /\ True <-> P :=
    conj (and_ind (fun H0 _ => H0)) (fun H => conj H I).
  Definition or_True_iff2 P : True /\ P <-> P :=
    conj (and_ind (fun _ H1 => H1)) (conj I).
  Definition eq_S_iff n m : S n = S m <-> n = m :=
    conj (eq_add_S n m) (f_equal_nat nat S n m).
  Definition le_S_n_iff n m : S n <= S m <-> n <= m :=
    conj (le_S_n n m) (le_n_S n m).
  Definition lt_S_n_iff n m : S n < S m <-> n < m :=
    conj (lt_S_n n m) (lt_n_S n m).
  Definition Zge_le_iff n m : (n >= m <-> m <= n)%Z :=
    conj (Z.ge_le n m) (Z.le_ge m n).
  Definition Zgt_lt_iff n m : (n > m <-> m < n)%Z :=
    conj (Z.gt_lt n m) (Z.lt_gt m n).
End rewrite_helpers.

Hint Rewrite
     andb_true_iff
     andb_true_iff
     Nat.eqb_eq
     Z.eqb_eq
     Zleb_iff
     true_eq_true
     or_True_iff
     or_True_iff2
     list_eq_iff_hd_tl
     eq_S_iff
     le_S_n_iff
     lt_S_n_iff
     Zgt_lt_iff
     Zge_le_iff
     Nat.add_1_l
     map_app
: rewritesome.

Tactic Notation "simpl_extra" :=
  repeat (simpl || autorewrite with rewritesome).
Tactic Notation "simpl_extra" "in" hyp(H) :=
  repeat (simpl in H || autorewrite with rewritesome in H).
Tactic Notation "simpl_destruct" hyp(H) "as" simple_intropattern(pattern) :=
  simpl_extra in H ; destruct H as pattern.
