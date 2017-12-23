Require Import List.
Require Import ZArith.
Require Import Nat.
Open Scope nat_scope.

Section hdn_tln.
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
  Theorem thm_hdn_id :
    forall A (lambda : list A) p,
      length lambda <= p
      -> hdn p lambda = lambda.
  Proof.
    induction lambda.
    - destruct p ; simpl ; tauto.
    - destruct p ; simpl ; firstorder.
      rewrite IHlambda ; trivial.
      refine (le_S_n _ _ _).
      assumption.
  Qed.
  Theorem thm_hdn_tln :
    forall A n (l : list A), l = (hdn n l) ++ (tln n l).
  Proof.
    induction n.
    - simpl ; trivial.
    - destruct l as [|a l].
      + simpl ; trivial.
      + simpl.
        rewrite <- IHn.
        trivial.
  Qed.
End hdn_tln.

Section list_helpers.
  Theorem list_eq_iff_hd_tl A (a : A) lambda b mu :
    a::lambda = b::mu <-> a = b /\ lambda = mu.
  Proof.
    split ; intros.
    inversion H ; firstorder.
    destruct H as [H1 H2].
    rewrite H1, H2 ; firstorder.
  Qed.
  Theorem thm_last_app:
    forall A lambda a mu (b : A),
      last (lambda ++ (a::mu)) b = last (a::mu) b.
  Proof.
    intros A lambda a mu b.
    induction lambda as [|x lambda].
    - trivial.
    - rewrite <- IHlambda.
      simpl.
      generalize (app_cons_not_nil lambda mu a).
      destruct (lambda ++ a::mu) ; firstorder.
  Qed.
  Theorem thm_last_rev :
    forall A l (a : A), last (rev l) a = hd a l.
  Proof.
    intros.
    destruct l.
    - trivial.
    - simpl.
      rewrite thm_last_app.
      simpl.
      trivial.
  Qed.
  Theorem thm_tl_app :
    forall A (lambda mu : list A),
      lambda <> nil
      -> tl (lambda ++ mu) = (tl lambda) ++ mu.
  Proof.
    destruct lambda ; firstorder.
  Qed.
  Theorem thm_tl_rev :
    forall {A} (l : list A), tl (rev l) = rev (removelast l).
  Proof.
    destruct l.
    - trivial.
    - generalize a.
      induction l.
      + trivial.
      + simpl.
        simpl in IHl.
        intros.
        rewrite thm_tl_app, IHl.
        trivial.
        intros H.
        destruct (app_eq_nil _ _ H) as [_ H0].
        discriminate H0.
  Qed.
  Theorem thm_removelast_map :
    forall {A B} (f : A -> B) (l : list A),
      removelast (map f l) = map f (removelast l).
  Proof.
    intros.
    induction l.
    - trivial.
    - simpl.
      destruct l.
      + trivial.
      + simpl.
        simpl in IHl.
        rewrite IHl.
        trivial.
  Qed.
  Theorem thm_hd_repeat :
    forall A (a b : A) n,
      hd a (repeat b n) = if n =? 0 then a else b.
  Proof.
    intros.
    destruct n ; firstorder.
  Qed.
  Theorem thm_hd_app :
    forall A (a : A) lambda mu,
      hd a (lambda++mu)
      = hd (hd a mu) lambda.
  Proof.
    destruct lambda ; firstorder.
  Qed.
  Theorem thm_last_repeat :
    forall {A} (a b : A) n,
      last (repeat a n) b
      = if n =? 0 then b else a.
  Proof.
    destruct n ; simpl ; trivial.
    induction n ; simpl ; trivial.
  Qed.
  Theorem thm_repeat_map :
    forall A B (f : A -> B) a n, map f (repeat a n) = repeat (f a) n.
  Proof.
    induction n.
    - trivial.
    - simpl.
      rewrite IHn.
      trivial.
  Qed.
  Theorem thm_repeat_plus :
    forall A (a : A) p q,
      repeat a (p + q) = repeat a p ++ repeat a q.
  Proof.
    intros.
    induction p.
    - trivial.
    - simpl.
      rewrite IHp.
      trivial.
  Qed.
  Theorem thm_nth_repeat1 :
    forall A (a : A) k n, nth k (repeat a n) a = a.
  Proof.
    induction k ; destruct n ; simpl ; firstorder.
  Qed.
  Theorem thm_nth_app_repeat :
    forall A p q l (a b : A),
      p <= l
      -> l < p + q
      -> nth l (repeat a p ++ repeat b q) b = b.
  Proof.
    intros.
    rewrite app_nth2.
    all : rewrite repeat_length.
    rewrite thm_nth_repeat1 ; trivial.
    assumption.
  Qed.
  Theorem thm_nth_tl_tl :
    forall A (a : A) k lambda,
      2 <= k -> nth (k - 2) (tl (tl lambda)) a = nth k lambda a.
  Proof.
    intros.
    destruct k as [|[|k]] ; simpl ; try omega.
    rewrite PeanoNat.Nat.sub_0_r.
    destruct lambda as [|x [|y lambda]].
    all : simpl ; firstorder.
    all : destruct k ; trivial.
  Qed.
  Theorem thm_repeat_fact1 :
    forall A (a : A) p lambda,
      repeat a (S p) ++ lambda = repeat a p ++ (a::lambda).
  Proof.
    simpl.
    induction p.
    - trivial.
    - simpl ; intros ; rewrite IHp ; firstorder.
  Qed.
  Theorem thm_cons_repeat_app :
    forall A (a : A) p,
      a :: repeat a p = repeat a p ++ a::nil.
  Proof.
    intros.
    rewrite <- thm_repeat_fact1, app_nil_r.
    trivial.
  Qed.
End list_helpers.

Definition repeat2 (a b : Z) (p q : nat) :=
  repeat a p ++ repeat b q.

Theorem thm_hdn_long :
  forall A p (lambda : list A),
    length lambda < p -> hdn p lambda = lambda.
Proof.
  induction p.
  - firstorder.
    contradiction (Nat.nlt_0_r _ H).
  - destruct lambda ; simpl.
    + trivial.
    + intros H.
      rewrite (IHp _ (lt_S_n _ _ H)).
      trivial.
Qed.
Theorem thm_tln_long :
  forall A p (lambda : list A),
    length lambda < p -> tln p lambda = nil.
Proof.
  induction p.
  - firstorder.
    contradiction (Nat.nlt_0_r _ H).
  - destruct lambda ; simpl.
    + trivial.
    + intros H.
      rewrite (IHp _ (lt_S_n _ _ H)).
      trivial.
Qed.
Theorem thm_hd_hdn :
  forall A (a : A) p lambda,
    hd a (hdn p lambda) = if p =? 0 then a else hd a lambda.
Proof.
  destruct p ; [|destruct lambda] ; simpl ; firstorder.
Qed.
Theorem thm_hd_tln_nth :
  forall A (a : A) p lambda,
    hd a (tln p lambda) = nth p lambda a.
Proof.
  induction p ; destruct lambda ; firstorder.
Qed.
Theorem thm_nth_0_hd :
  forall A (a : A) lambda,
    nth 0 lambda a = hd a lambda.
Proof.
  destruct lambda ; simpl ; firstorder.
Qed.
Theorem thm_nth_hdn :
  forall A (a : A) p q lambda,
    p < q -> nth p (hdn q lambda) a
             = nth p lambda a.
Proof.
  induction p.
  - destruct q.
    + intros ; omega.
    + destruct lambda ; simpl ; trivial.
  - destruct q.
    + intros ; omega.
    + intros.
      destruct lambda ; simpl ; trivial.
      exact (IHp _ _ (lt_S_n _ _ H)).
Qed.
Theorem thm_nth_last :
  forall A (a : A) lambda,
    nth (length lambda - 1) lambda a = last lambda a.
Proof.
  intros.
  induction lambda.
  - trivial.
  - simpl.
    destruct lambda.
    + simpl ; trivial.
    + simpl.
      simpl in IHlambda.
      rewrite Nat.sub_0_r in IHlambda.
      assumption.
Qed.
Theorem thm_last_hdn :
  forall A (a : A) p lambda,
    p <= length lambda
    -> last (hdn p lambda) a = if p =? 0 then a else nth (p - 1) lambda a.
Proof.
  induction p.
  - trivial.
  - destruct lambda.
    + simpl. omega.
    + simpl.
      intros.
      pose (H1 := IHp _ (le_S_n _ _ H)).
      rewrite H1.
      destruct lambda.
      * destruct p ; simpl in *; trivial ; omega.
      * destruct p ; trivial.
        rewrite Nat.sub_0_r in *.
        destruct p ; simpl ; trivial.
Qed.

Theorem thm_repeat_fact2 :
  forall A (a b : A) lambda mu p,
    lambda ++ a::mu = repeat b p -> a = b.
Proof.
  induction lambda.
  - simpl.
    destruct p.
    + discriminate.
    + simpl.
      rewrite list_eq_iff_hd_tl.
      firstorder.
  - simpl.
    destruct p.
    + discriminate.
    + simpl.
      rewrite list_eq_iff_hd_tl.
      firstorder.
Qed.
Theorem thm_repeat_fact3 :
  forall A (b c e : A) lambda mu nu q,
    lambda ++ b :: mu ++ c :: nu = repeat e q -> b = c.
Proof.
  intros.
  rewrite app_comm_cons in H.
  rewrite (thm_repeat_fact2  _ _ _ _ _ _ H) in *.
  rewrite app_assoc in H.
  rewrite (thm_repeat_fact2  _ _ _ _ _ _ H) in *.
  firstorder.
Qed.
Theorem thm_repeat2_fact1 :
  forall A (a b c d e : A) lambda mu nu p q,
    a::lambda ++ b::mu ++ c::nu = repeat d p ++ repeat e q
    -> a = b \/ b = c.
Proof.
  intros.
  destruct p as [|p].
  - rewrite app_comm_cons in H.
    rewrite (thm_repeat_fact3 _ _ _ _ _ _ _ _ H).
    firstorder.
  - simpl in H.
    rewrite list_eq_iff_hd_tl in H.
    destruct H as [Had H].
    rewrite Had in *.
    generalize p, H.
    clear.
    induction lambda.
    + simpl in *.
      intros.
      destruct p.
      * simpl in *.
        rewrite <- (app_nil_l (_::_)) in H.
        rewrite (thm_repeat_fact3 _ _ _ _ _ _ _ _ H).
        firstorder.
      * simpl in *.
        rewrite list_eq_iff_hd_tl in H.
        firstorder.
    + destruct p.
      * simpl in *.
        intros.
        rewrite app_comm_cons in H.
        rewrite (thm_repeat_fact3 _ _ _ _ _ _ _ _ H).
        firstorder.
      * simpl.
        rewrite list_eq_iff_hd_tl.
        firstorder.
Qed.

Section rewrite_length.
  Variable A : Type.
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

Tactic Notation "simpl_length" :=
  repeat (simpl || autorewrite with rewritelength).
Tactic Notation "simpl_length" "in" hyp(H) :=
  repeat (simpl in H || autorewrite with rewritelength in H).
Ltac tac_length := simpl_length ; try omega.
Ltac destruct_bool b H :=
  destruct (Sumbool.sumbool_of_bool b) as [H|H] ;
  rewrite H.

Hint Rewrite
     thm_hd_app
     thm_hd_repeat
: rewritehd.
Tactic Notation "simpl_hd" :=
  repeat (simpl || autorewrite with rewritehd).
Tactic Notation "simpl_hd" "in" hyp(H) :=
  repeat (simpl in H || autorewrite with rewritehd in H).

