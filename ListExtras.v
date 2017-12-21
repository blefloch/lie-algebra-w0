Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Our files*)
Require Import Rewriting.
Open Scope nat_scope.

Section list_helpers.
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
        tac_length.
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
      + simpl_extra.
        firstorder.
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
    all: autorewrite with rewritelength in *.
    rewrite thm_nth_repeat1 ; trivial.
    omega.
  Qed.
  Theorem thm_nth_tl_tl :
    forall A (a : A) k lambda,
      2 <= k -> nth (k - 2) (tl (tl lambda)) a = nth k lambda a.
  Proof.
    intros.
    destruct k as [|[|k]] ; simpl ; try omega.
    rewrite Nat.sub_0_r.
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
End list_helpers.

