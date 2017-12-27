Require Import List.
Require Import ZArith.
Require Import Nat.
Open Scope nat_scope.
(*This file defines repeat2 and some theorems about lists.*)

Section functions.
  Definition repeat2 (a b : Z) (p q : nat) :=
    repeat a p ++ repeat b q.
End functions.

Section basic.
  Theorem cons_nil A (x : A) l :
    x::l <> nil.
  Proof.
    discriminate.
  Qed.
  Theorem cons_eq A (x : A) l y l' :
    x::l = y::l' <-> x = y /\ l = l'.
  Proof.
    split ; intros H.
    inversion H ; firstorder.
    destruct H as [H1 H2].
    rewrite H1, H2 ; firstorder.
  Qed.
End basic.

Section app.
  Theorem last_indep A l (d d' : A) :
    l <> nil -> last l d = last l d'.
  Proof.
    induction l as [|x l].
    - intros H. contradiction (H eq_refl).
    - destruct l as [|y l].
      + intros _. exact eq_refl.
      + intros _.
        simpl in *.
        rewrite (IHl (cons_nil A y l)).
        exact eq_refl.
  Qed.
  Theorem last_app A l l' (d : A) :
    last (l++l') d = last l' (last l d).
  Proof.
    induction l as [|x l].
    - trivial.
    - destruct l.
      + destruct l' ;
          [exact eq_refl|
           exact (last_indep _ _ _ _ (cons_nil _ _ _))].
      + exact IHl.
  Qed.
  Theorem last_app_cons A l x l' (y : A) :
    last (l ++ (x::l')) y = last (x::l') y.
  Proof.
    exact (eq_trans (last_app _ _ _ _)
                    (last_indep _ _ _ _ (cons_nil _ _ _))).
  Qed.
  Theorem tl_app A (l l' : list A) :
    l <> nil -> tl (l ++ l') = (tl l) ++ l'.
  Proof.
    destruct l ; firstorder.
  Qed.
  Theorem hd_app A (x : A) l l' :
    hd x (l++l') = hd (hd x l') l.
  Proof.
    destruct l ; firstorder.
  Qed.
End app.

Section rev.
  Theorem last_rev A l (x : A) :
    last (rev l) x = hd x l.
  Proof.
    destruct l.
    - trivial.
    - simpl.
      rewrite last_app_cons.
      trivial.
  Qed.
  Theorem tl_rev A (l : list A) :
    tl (rev l) = rev (removelast l).
  Proof.
    destruct l as [|x l].
    - trivial.
    - generalize x.
      induction l.
      + trivial.
      + simpl.
        simpl in IHl.
        intros.
        rewrite tl_app, IHl.
        trivial.
        intros H.
        destruct (app_eq_nil _ _ H) as [_ H0].
        discriminate H0.
  Qed.
End rev.

Section map.
  Theorem removelast_map A B (f : A -> B) l :
    removelast (map f l) = map f (removelast l).
  Proof.
    intros.
    induction l.
    - trivial.
    - simpl.
      destruct l.
      + trivial.
      + simpl in *.
        rewrite IHl.
        trivial.
  Qed.
End map.

Section repeat.
  Theorem hd_repeat A (a b : A) n :
    hd a (repeat b n) = if n =? 0 then a else b.
  Proof.
    destruct n ; firstorder.
  Qed.
  Theorem last_repeat A (a b : A) n :
    last (repeat a n) b = if n =? 0 then b else a.
  Proof.
    destruct n ; simpl ; trivial.
    induction n ; simpl ; trivial.
  Qed.
  Theorem map_repeat A B (f : A -> B) a n :
    map f (repeat a n) = repeat (f a) n.
  Proof.
    induction n.
    - trivial.
    - simpl.
      rewrite IHn.
      trivial.
  Qed.
  Theorem repeat_plus A (a : A) n m :
    repeat a (n + m) = repeat a n ++ repeat a m.
  Proof.
    induction n.
    - trivial.
    - simpl.
      rewrite IHn.
      trivial.
  Qed.
  Theorem cons_repeat A (a : A) n :
    a :: repeat a n = repeat a (S n).
  Proof.
    trivial.
  Qed.
  Theorem tl_repeat A (a : A) n :
    tl (repeat a n) = repeat a (n - 1).
  Proof.
    destruct n ; simpl ; firstorder.
  Qed.
  Theorem repeat_S_app A (a : A) n l :
    repeat a (S n) ++ l = repeat a n ++ (a::l).
  Proof.
    simpl.
    induction n.
    - trivial.
    - simpl ; intros ; rewrite IHn ; firstorder.
  Qed.
  Theorem repeat_spec_hd A (a : A) l b n :
    a::l = repeat b n -> a = b.
  Proof.
    destruct n ; simpl in * ; intuition ; try discriminate.
    injection H.
    trivial.
  Qed.
  Theorem repeat_spec1 A (a b : A) l l' n :
    l ++ a::l' = repeat b n -> a = b.
  Proof.
    generalize l' n ; clear l' n.
    induction l.
    - simpl.
      destruct n.
      + discriminate.
      + simpl.
        rewrite cons_eq.
        firstorder.
    - simpl.
      destruct n.
      + discriminate.
      + simpl.
        rewrite cons_eq.
        firstorder.
  Qed.
  Theorem repeat_spec2 A (a b c : A) l1 l2 l3 n :
    l1 ++ a :: l2 ++ b :: l3 = repeat c n -> a = b.
  Proof.
    intros H.
    rewrite app_comm_cons in H.
    rewrite (repeat_spec1  _ _ _ _ _ _ H) in *.
    rewrite app_assoc in H.
    rewrite (repeat_spec1  _ _ _ _ _ _ H) in *.
    firstorder.
  Qed.
  Theorem cons_repeat_app A (a : A) n :
    a :: repeat a n = repeat a n ++ a::nil.
  Proof.
    rewrite <- repeat_S_app, app_nil_r.
    trivial.
  Qed.
  Theorem eq_repeat_iff A (a : A) l n :
    l = repeat a n -> l = repeat a (length l).
  Proof.
    generalize n ; clear n.
    induction l.
    - simpl ; tauto.
    - simpl.
      destruct n.
      + simpl ; discriminate.
      + simpl.
        intros H.
        injection H.
        intros H0 H1.
        rewrite <- (IHl _ H0), H1.
        trivial.
  Qed.
  (*TODO: change to actually use repeat2*)
  Theorem repeat2_fact1 A (a1 a2 a3 d1 d2 : A) l1 l2 l3 n1 n2 :
    a1 :: l1 ++ a2 :: l2 ++ a3 :: l3 = repeat d1 n1 ++ repeat d2 n2
    -> a1 = a2 \/ a2 = a3.
  Proof.
    intros H.
    destruct n1 as [|n1].
    - rewrite app_comm_cons in H.
      rewrite (repeat_spec2 _ _ _ _ _ _ _ _ H).
      intuition.
    - simpl in H.
      rewrite cons_eq in H.
      destruct H as [Had H].
      rewrite Had in *.
      generalize n1, H.
      clear.
      induction l1.
      + simpl in *.
        intros.
        destruct n1 ; simpl in *.
        * rewrite <- (app_nil_l (_::_)) in H.
          rewrite (repeat_spec2 _ _ _ _ _ _ _ _ H).
          intuition.
        * rewrite cons_eq in H.
          intuition.
      + destruct n1 ; simpl in *.
        * intros.
          rewrite app_comm_cons in H.
          rewrite (repeat_spec2 _ _ _ _ _ _ _ _ H).
          intuition.
        * rewrite cons_eq.
          firstorder.
  Qed.
End repeat.

Section firstn_skipn.
  Theorem firstn_id A (l : list A) n :
    length l <= n -> firstn n l = l.
  Proof.
    generalize n ; clear n.
    induction l.
    - destruct n ; simpl ; tauto.
    - destruct n ; simpl ; firstorder.
      rewrite IHl ; trivial.
      refine (le_S_n _ _ _).
      assumption.
  Qed.
  Theorem skipn_nil A (l : list A) n :
    length l <= n -> skipn n l = nil.
  Proof.
    generalize n ; clear n.
    induction l ; destruct n ; simpl.
    - tauto.
    - tauto.
    - intros H ; contradiction (Nat.nle_succ_0 _ H).
    - intros H ; exact (IHl _ (le_S_n _ _ H)).
  Qed.
  Theorem hd_firstn A (a : A) n l :
    hd a (firstn n l) = if n =? 0 then a else hd a l.
  Proof.
    destruct n ; [|destruct l] ; simpl ; intuition.
  Qed.
  Theorem hd_skipn A (a : A) n l :
    hd a (skipn n l) = nth n l a.
  Proof.
    generalize l ; clear l.
    induction n ; destruct l ; simpl ; intuition.
  Qed.
End firstn_skipn.

Section nth.
  Theorem nth_0 A (a : A) l :
    nth 0 l a = hd a l.
  Proof.
    destruct l ; simpl ; intuition.
  Qed.
  Theorem nth_repeat A (a : A) k n :
    nth k (repeat a n) a = a.
  Proof.
    generalize n ; clear n.
    induction k ; destruct n ; simpl ; firstorder.
  Qed.
  Theorem nth_app_repeat2 A p q l (a b : A) :
    p <= l
    -> l < p + q
    -> nth l (repeat a p ++ repeat b q) b = b.
  Proof.
    intros.
    rewrite app_nth2.
    all : rewrite repeat_length.
    rewrite nth_repeat ; trivial.
    assumption.
  Qed.
  Theorem nth_tl_tl A (a : A) n l :
      2 <= n -> nth (n - 2) (tl (tl l)) a = nth n l a.
  Proof.
    intros.
    destruct n as [|[|n]] ; simpl ; try omega.
    rewrite PeanoNat.Nat.sub_0_r.
    destruct l as [|x [|y l]].
    all : simpl ; firstorder.
    all : destruct n ; trivial.
  Qed.
  Theorem nth_firstn1 A (a : A) p q l :
    p < q -> nth p (firstn q l) a = nth p l a.
  Proof.
    generalize q l ; clear q l.
    induction p.
    - destruct q.
      + intros ; omega.
      + destruct l ; simpl ; trivial.
    - destruct q.
      + intros ; omega.
      + intros.
        destruct l ; simpl ; trivial.
        exact (IHp _ _ (lt_S_n _ _ H)).
  Qed.
  Theorem nth_last A (a : A) l :
    nth (length l - 1) l a = last l a.
  Proof.
    induction l.
    - trivial.
    - simpl.
      destruct l.
      + simpl ; trivial.
      + simpl.
        simpl in IHl.
        rewrite Nat.sub_0_r in IHl.
        assumption.
  Qed.
  Theorem last_firstn A (a : A) n l :
    n <= length l
    -> last (firstn n l) a = if n =? 0 then a else nth (n - 1) l a.
  Proof.
    generalize l ; clear l.
    induction n.
    - trivial.
    - destruct l.
      + simpl. omega.
      + simpl.
        intros.
        pose (H1 := IHn _ (le_S_n _ _ H)).
        rewrite H1.
        destruct l.
        * destruct n ; simpl in *; trivial ; omega.
        * destruct n ; trivial.
          rewrite Nat.sub_0_r in *.
          destruct n ; simpl ; trivial.
  Qed.
End nth.

Section rewrite_length.
  Theorem length_firstn A n (l : list A) :
    length (firstn n l) = min n (length l).
  Proof.
    generalize l ; clear l.
    induction n.
    - simpl ; trivial.
    - destruct l.
      + simpl ; trivial.
      + simpl.
        rewrite IHn.
        trivial.
  Qed.
  Theorem length_skipn A n (l : list A) :
    length (skipn n l) = length l - n.
  Proof.
    generalize l ; clear l.
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
  Theorem length_cons A (a : A) l :
    length (a::l) = 1 + length l.
  Proof.
    firstorder.
  Qed.
  Theorem length_tl A (l : list A) :
    length (tl l) = length l - 1.
  Proof.
    destruct l ; firstorder.
  Qed.
  Theorem not_nil_iff_length_pos A (l : list A) :
    l <> nil <-> length l > 0.
  Proof.
    destruct l ; simpl ; firstorder.
  Qed.
  Theorem length_removelast A (l : list A) :
    length (removelast l) = length l - 1.
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
     length_cons
     length_tl
     not_nil_iff_length_pos
     map_length
     rev_length
     app_length
     repeat_length
     length_removelast
     length_firstn
     length_skipn
: list.
Tactic Notation "simpl_length" :=
  repeat (simpl || autorewrite with list).
Tactic Notation "simpl_length" "in" hyp(H) :=
  repeat (simpl in H || autorewrite with list in H).
Ltac tac_length := simpl_length ; try omega.

Hint Rewrite
     hd_app
     hd_repeat
: rewritehd.
Tactic Notation "simpl_hd" :=
  repeat (simpl || autorewrite with rewritehd).
Tactic Notation "simpl_hd" "in" hyp(H) :=
  repeat (simpl in H || autorewrite with rewritehd in H).

