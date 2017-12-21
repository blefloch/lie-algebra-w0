Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Load our files*)
Open Scope nat_scope.

Section rewrite_helpers.
  Definition Zleb_iff n m : (n <=? m)%Z = true <-> (n <= m)%Z :=
    conj (Zle_bool_imp_le n m) (Zle_imp_le_bool n m).
  Definition true_eq_true : true = true <-> True :=
    conj (fun _ => I) (fun _ => eq_refl).
  Theorem or_True_iff : forall P, P /\ True <-> P.
  Proof.
    firstorder.
  Qed.
  Theorem or_True_iff2 : forall P, True /\ P <-> P.
  Proof.
    firstorder.
  Qed.
  Theorem list_eq_iff_hd_tl A (a : A) lambda b mu :
    a::lambda = b::mu <-> a = b /\ lambda = mu.
  Proof.
    split ; intros.
    inversion H ; firstorder.
    destruct H as [H1 H2].
    rewrite H1, H2 ; firstorder.
  Qed.
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
Tactic Notation "simpl_length" :=
  repeat (simpl || autorewrite with rewritelength).
Tactic Notation "simpl_length" "in" hyp(H) :=
  repeat (simpl in H || autorewrite with rewritelength in H).

Section rewrite_length.
  Fixpoint hdn {A} n (l : list A) :=
    match n with
      | 0 => nil
      | S n' => match l with
                  | nil => nil
                  | a::l' => a::(hdn n' l')
                end
    end.
  Fixpoint tln {A} n (l : list A) :=
    match n with
      | 0 => l
      | S n' => match l with
                  | nil => nil
                  | a::l' => (tln n' l')
                end
    end.
  Variable A : Type.
  Theorem thm_hdn_tln :
    forall n (l : list A), n <= length l -> l = (hdn n l) ++ (tln n l).
  Proof.
    induction n.
    - simpl ; trivial.
    - destruct l as [|a l].
      + simpl ; trivial.
      + simpl.
        intros.
        rewrite <- IHn.
        * trivial.
        * omega.
  Qed.
  Theorem hdn_length :
    forall n (l : list A), length (hdn n l) = min n (length l).
  Proof.
    induction n.
    - simpl ; trivial.
    - destruct l.
      + simpl ; trivial.
      + simpl.
        rewrite IHn.
        trivial.
  Qed.
  Theorem tln_length :
    forall n (l : list A), length (tln n l) = length l - n.
  Proof.
    induction n.
    - simpl.
      trivial.
      intros.
      omega.
    - destruct l.
      + simpl ; trivial.
      + simpl.
        rewrite IHn.
        trivial.
  Qed.
  Theorem thm_cons_length :
    forall (a : A) lambda,
      length (a::lambda) = 1 + length lambda.
  Proof.
    firstorder.
  Qed.
  Theorem thm_tl_length :
    forall (lambda : list A),
      length (tl lambda) = length lambda - 1.
  Proof.
    destruct lambda ; firstorder.
  Qed.
  Theorem thm_nnil_length :
    forall (l : list A), l <> nil <-> length l > 0.
  Proof.
    destruct l ; simpl ; firstorder.
  Qed.
  Theorem thm_removelast_length :
    forall (l : list A), length (removelast l) = length l - 1.
  Proof.
    destruct l as [|a l].
    - trivial.
    - generalize a.
      induction l.
      + trivial.
      + simpl.
        simpl in IHl.
        rewrite IHl.
        intros.
        omega.
  Qed.
End rewrite_length.
Hint Rewrite
     thm_cons_length
     thm_tl_length
     thm_nnil_length
     map_length
     rev_length
     app_length
     repeat_length
     thm_removelast_length
     hdn_length
     tln_length
: rewritelength.
Ltac tac_length := simpl_length ; try omega.
Ltac destruct_bool b H :=
  destruct (Sumbool.sumbool_of_bool b) as [H|H] ;
  rewrite H.
