Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Load our files*)
Require Import ListExtras.
Open Scope nat_scope.

Section nat.
  Definition nat_ind2
             (P : nat -> Prop)
             (f0 : P 0) (f1 : P 1)
             (fn : forall (n : nat), P n -> P (S (S n))) :=
    fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
      | 0 => f0
      | 1 => f1
      | S (S n0) => fn n0 (F n0)
    end.
  Theorem thm_1_lt_SS :
    forall n, 1 < S (S n).
  Proof.
    intros ; firstorder.
  Qed.
  Theorem thm_S_minus_1 :
    forall n, S n - 1 = n.
  Proof.
    intros ; omega.
  Qed.
End nat.

Section prop.
  Theorem thm_apply_if_then_else :
    forall A B (f : A -> B) x y (b : bool),
      f (if b then x else y)
      = if b then f x else f y.
  Proof.
    destruct b ; trivial.
  Qed.
  Theorem thm_args_if_then_else :
    forall A B (f g : A -> B) x (b : bool),
      (if b then f else g) x
      = if b then f x else g x.
  Proof.
    destruct b ; trivial.
  Qed.
  Theorem thm_if_then_else_same :
    forall A (x : A) (b : bool),
      (if b then x else x) = x.
  Proof.
    destruct b ; trivial.
  Qed.
  Theorem thm_if_then_else_same_prop :
    forall (P : Prop) (b : bool),
      (if b then P else P) <-> P.
  Proof.
    destruct b ; tauto.
  Qed.
  Theorem thm_if_then_false_else :
    forall b1 b3 : bool,
      (if b1 then false else b3)
      = negb b1 && b3.
  Proof.
    destruct b1, b3 ; simpl ; trivial.
  Qed.
  Theorem thm_if_then_true_else :
    forall b1 b3 : bool,
      (if b1 then true else b3)
      = b1 || b3.
  Proof.
    destruct b1, b3 ; simpl ; trivial.
  Qed.
  Theorem thm_if_then_else :
    forall b1 b2 b3 : bool,
      (if b1 then b2 else b3)
      = (b1 && b2) || (negb b1 && b3).
  Proof.
    destruct b1, b2, b3 ; simpl ; trivial.
  Qed.
End prop.

Hint Rewrite
     thm_if_then_false_else
     thm_if_then_true_else
     andb_false_l
     andb_false_r
     andb_true_l
     andb_true_r
     orb_false_l
     orb_false_r
     orb_true_l
     orb_true_r
     andb_true_iff
     andb_false_iff
     orb_true_iff
     orb_false_iff
     negb_andb
     negb_orb
     negb_involutive
     negb_false_iff
     negb_true_iff
     Z.negb_odd
     Z.negb_even
     Z.ltb_ge
     Z.eqb_eq
     Z.leb_le
     Nat.ltb_ge
     Nat.eqb_eq
     Nat.leb_le
: rewritebool.

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
