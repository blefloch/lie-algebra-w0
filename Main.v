Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
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

Section helpers.
  Theorem thm_div_2_2 : (2 / 2 = 1)%Z.
  Proof.
    firstorder.
  Qed.
  Theorem thm_div_m2_2 : (-2 / 2 = -1)%Z.
  Proof.
    firstorder.
  Qed.
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
End helpers.

Section list_helpers.
  Variable A : Type.
  Theorem thm_last_app:
    forall lambda a mu (b : A),
      last (lambda ++ (a::mu)) b = last (a::mu) b.
  Proof.
    intros lambda a mu b.
    induction lambda as [|x lambda].
    - trivial.
    - rewrite <- IHlambda.
      simpl.
      generalize (app_cons_not_nil lambda mu a).
      destruct (lambda ++ a::mu) ; firstorder.
  Qed.
  Theorem thm_tl_app :
    forall (lambda mu : list A),
      lambda <> nil
      -> tl (lambda ++ mu) = (tl lambda) ++ mu.
  Proof.
    destruct lambda ; firstorder.
  Qed.
  (*TODO: replace "constant_list" by (built-in) "repeat"*)
  (*TODO: use "fold"*)
  Definition basic_list (x : A) i (y : A) n :=
    if (1 <=? i) && (i <=? n)
    then (repeat y (i - 1))++x::(repeat y (n - i))
    else repeat y n.
  Definition basic_list_rev (x : A) i (y : A) n :=
    if (1 <=? i) && (i <=? n)
    then (repeat y (n - i))++x::(repeat y (i - 1))
    else repeat y n.
  Fixpoint Zvec_total lambda :=
    match lambda with
      | nil => 0%Z
      | a::lambda' => (a + Zvec_total lambda')%Z
    end.
  Fixpoint Zvec_allb (testb : Z -> bool) lambda :=
    match lambda with
      | nil => true
      | a::lambda' => (testb a) && (Zvec_allb testb lambda')
    end.
  Fixpoint Zvec_short_allb (testb : Z -> Z -> bool) lambda mu :=
    match lambda with
      | nil => true
      | a::lambda' => match mu with
                        | nil => true
                        | b::mu' => (testb a b)
                                      && (Zvec_short_allb testb lambda' mu')
                      end
    end.
  Fixpoint Zvec_short_map_zip (f : Z -> Z -> Z) lambda mu :=
    match lambda with
      | nil => nil
      | a::lambda' => match mu with
                        | nil => nil
                        | b::mu' => (f a b)::(Zvec_short_map_zip f lambda' mu')
                      end
    end.
  Fixpoint Zvec_long_map_zip (f : Z -> Z -> Z) lambda mu :=
    match lambda with
      | nil => mu
      | a::lambda' => match mu with
                        | nil => lambda
                        | b::mu' => (f a b)::(Zvec_long_map_zip f lambda' mu')
                      end
    end.
  Definition Zvec_mul m := map (Z.mul m).
  Definition Zvec_short_sub := Zvec_short_map_zip Z.sub.
  Definition Zvec_short_max := Zvec_short_map_zip Z.max.
  Definition Zvec_long_min := Zvec_long_map_zip Z.min.
  Definition Zvec_nondecb lambda := Zvec_short_allb Z.leb lambda (tl lambda).
  Definition Zvec_nonincb lambda := Zvec_short_allb Z.leb (tl lambda) lambda.
  Definition Zvec_all_nonnegb := Zvec_allb (Z.leb 0).
End list_helpers.

Section list_thm.
  Theorem thm_Zvec_leb_refl :
    forall mu, Zvec_short_allb Z.leb mu mu = true.
  Proof.
    induction mu ; simpl.
    - firstorder.
    - rewrite IHmu, Z.leb_refl ; firstorder.
  Qed.
  Theorem thm_Zvec_leb_trans12 :
    forall lambda mu nu,
      length lambda <= length mu
      -> Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb mu nu = true
      -> Zvec_short_allb Z.leb lambda nu = true.
  Proof.
    induction lambda.
    - intros mu nu Hlength Hlm Hmn.
      destruct nu.
      + destruct mu ; firstorder.
      + simpl in Hlength ; firstorder.
    - intros mu nu Hlength Hlm Hmn.
      destruct mu ; simpl in Hlength.
      + firstorder.
      + destruct nu.
        * firstorder.
        * simpl_destruct Hlm as [H1 Hlm].
          simpl_destruct Hmn as [H2 Hmn].
          pose (H3 := Z.le_trans _ _ _ H1 H2).
          rewrite Zle_is_le_bool in H3.
          simpl.
          firstorder.
  Qed.
  Theorem thm_Zvec_leb_trans32 :
    forall nu lambda mu,
      length nu <= length mu
      -> Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb mu nu = true
      -> Zvec_short_allb Z.leb lambda nu = true.
  Proof.
    induction nu.
    - intros lambda mu Hlength Hlm Hmn.
      destruct lambda.
      + destruct mu ; firstorder.
      + simpl in Hlength ; firstorder.
    - intros lambda mu Hlength Hlm Hmn.
      destruct mu ; simpl in Hlength.
      + firstorder.
      + destruct lambda.
        * firstorder.
        * simpl_destruct Hlm as [H1 Hlm].
          simpl_destruct Hmn as [H2 Hmn].
          pose (H3 := Z.le_trans _ _ _ H1 H2).
          rewrite Zle_is_le_bool in H3.
          simpl in *.
          autorewrite with rewritesome in *.
          split ; [assumption|].
          exact (IHnu lambda mu Hlength Hlm Hmn).
  Qed.
  Theorem thm_Zvec_leb_app :
    forall mu1 mu2 nu1 nu2,
      length mu1 = length nu1
      -> (Zvec_short_allb Z.leb (mu1 ++ mu2) (nu1 ++ nu2) = true
          <-> Zvec_short_allb Z.leb mu1 nu1 = true
              /\ Zvec_short_allb Z.leb mu2 nu2 = true).
  Proof.
    induction mu1 as [|a1 mu1].
    - destruct nu1.
      + firstorder.
      + simpl. firstorder.
    - destruct nu1 as [|x1 nu1].
      + simpl. firstorder.
      + intros nu2 Hlength.
        simpl_extra.
        simpl_extra in Hlength.
        destruct (IHmu1 mu2 nu1 nu2 Hlength) as [H2 H3].
        split ; firstorder.
  Qed.
  Ltac tac_nondecb lambda :=
    destruct lambda ;
    unfold Zvec_nondecb ;
    simpl_extra ;
    firstorder.
  Theorem thm_Zvec_nondecb_01_geq :
    forall a b lambda,
      Zvec_nondecb (a::b::lambda) = true
      -> (a <= b)%Z.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_cons :
    forall a lambda,
      Zvec_nondecb (a::lambda) = true
      -> Zvec_nondecb lambda = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_skip :
    forall a b lambda,
      Zvec_nondecb (a::b::lambda) = true
      -> Zvec_nondecb (a::lambda) = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_join :
    forall a lambda,
      (a <= hd a lambda)%Z
      -> Zvec_nondecb (lambda) = true
      -> Zvec_nondecb (a::lambda) = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_join2 :
    forall a b lambda,
      (a <= b)%Z
      -> Zvec_nondecb (b::lambda) = true
      -> Zvec_nondecb (a::b::lambda) = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_join3 :
    forall a b c lambda,
      (a <= b)%Z
      -> (b <= c)%Z
      -> Zvec_nondecb (a::c::lambda) = true
      -> Zvec_nondecb (a::b::c::lambda) = true.
  Proof.
    tac_nondecb lambda.
  Qed.
  Theorem thm_Zvec_nondecb_app :
    forall lambda mu,
      Zvec_nondecb (lambda++mu) = true
      -> Zvec_nondecb lambda = true
         /\ Zvec_nondecb mu = true.
  Proof.
    destruct lambda as [|a lambda].
    - simpl ; firstorder.
    - induction lambda as [|b lambda].
      + simpl ; firstorder.
        destruct mu.
        * firstorder.
        * exact (thm_Zvec_nondecb_cons _ _ H).
      + intros mu H.
        pose (H0 := IHlambda mu (thm_Zvec_nondecb_skip _ _ _ H)).
        firstorder.
        unfold Zvec_nondecb in H.
        simpl_destruct H as [Hab H].
        destruct lambda as [|c lambda].
        * unfold Zvec_nondecb ; simpl.
          rewrite (Zle_imp_le_bool _ _ Hab).
          trivial.
        * simpl_destruct H as [Hbc H].
          exact (thm_Zvec_nondecb_join3 _ _ _ _ Hab Hbc H0).
  Qed.
  Theorem thm_Zvec_nondecb_app_hd :
    forall a lambda b mu,
      Zvec_nondecb (a::lambda++(b::mu)) = true -> (a <= b)%Z.
  Proof.
    intros a lambda b mu H.
    unfold Zvec_nondecb in H.
    induction lambda.
    - simpl_extra in H.
      firstorder.
    - refine (IHlambda _).
      destruct lambda ;
        simpl ;
        simpl_destruct H as [H [H0 H1]] ;
        rewrite (Zle_imp_le_bool _ _ (Zle_trans _ _ _ H H0)) ;
        firstorder.
  Qed.
  Theorem thm_Zvec_nondecb_app2 :
    forall lambda mu,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb mu = true
      -> match mu with
           | nil => True
           | a::mu' => (last lambda a <= a)%Z
         end
      -> Zvec_nondecb (lambda++mu) = true.
  Proof.
    destruct mu as [|z mu].
    - rewrite app_nil_r.
      trivial.
    - simpl.
      induction lambda as [|a lambda].
      + trivial.
      + intros Hal Hzm Hlz.
        destruct lambda as [|b lambda] ; simpl.
        * simpl in Hlz.
          exact (thm_Zvec_nondecb_join2 _ _ _ Hlz Hzm).
        * refine (thm_Zvec_nondecb_join2
                    a b _ (thm_Zvec_nondecb_01_geq _ _ _ Hal) _).
          simpl in IHlambda.
          simpl in Hlz.
          exact (IHlambda (thm_Zvec_nondecb_cons _ _ Hal) Hzm Hlz).
  Qed.
  Theorem thm_Zvec_nondecb_app_iff :
    forall lambda mu,
      Zvec_nondecb (lambda++mu) = true
      <-> Zvec_nondecb lambda = true
          /\ Zvec_nondecb mu = true
          /\ match mu with
               | nil => True
               | a::mu' => (last lambda a <= a)%Z
             end.
  Proof.
    split.
    - intros H.
      pose (H0 := thm_Zvec_nondecb_app _ _ H).
      firstorder.
      destruct mu ; trivial.
      destruct lambda as [|a lambda].
      + simpl ; omega.
      + assert (a::lambda <> nil) as H2.
        { discriminate. }
        rewrite (app_removelast_last z H2) in *.
        rewrite thm_last_app.
        simpl in *.
        rewrite <- app_assoc in H.
        pose (H3 := thm_Zvec_nondecb_app _ _ H).
        destruct H3 as [H3 H4].
        exact (thm_Zvec_nondecb_app_hd _ _ _ _ H4).
    - pose (H := thm_Zvec_nondecb_app2 lambda mu).
      firstorder.
  Qed.
  Theorem thm_Zvec_total_app :
    forall lambda mu,
      Zvec_total (lambda++mu)
      = (Zvec_total lambda + Zvec_total mu)%Z.
  Proof.
    induction lambda ; simpl.
    - trivial.
    - intros.
      rewrite (IHlambda mu).
      exact (Zplus_assoc _ _ _).
  Qed.
  Theorem thm_Zvec_nondecb_total_app :
    forall lambda mu,
      Zvec_nondecb (lambda++mu) = true
      -> Zvec_total (lambda++mu) = 0%Z
      -> (Zvec_total lambda <= 0)%Z
         /\ (Zvec_total mu >= 0)%Z.
  Proof.
    intros lambda mu H Htot.
    assert (Zvec_total lambda <= 0 \/ 0 <= Zvec_total mu)%Z as Hor.
    {
      pose (H0 := thm_Zvec_nondecb_app _ _ H).
      destruct H0 as [H0 H1].
      destruct mu as [|a mu].
      - right ; firstorder.
      - destruct (Z_lt_le_dec a 0) as [H2|H2].
        + left.
          assert (Zvec_allb (Z.gtb 0) lambda = true) as H3.
          {
            generalize lambda as lambda0, H.
            induction lambda0.
            - unfold Zvec_nondecb ; simpl ; firstorder.
            - simpl.
              intros H3.
              rewrite (IHlambda0 (thm_Zvec_nondecb_cons _ _ H3)).
              pose (H4 := thm_Zvec_nondecb_app_hd _ _ _ _ H3).
              pose (H5 := Z.le_lt_trans _ _ _ H4 H2).
              rewrite <- Z.ltb_lt, <- Z.gtb_ltb in H5.
              rewrite H5.
              trivial.
          }
          assert (forall lambda0,
                    Zvec_allb (Z.gtb 0) lambda0 = true
                    -> Zvec_total lambda0 <= 0)%Z as H4.
          {
            induction lambda0.
            - simpl ; firstorder.
            - simpl_extra.
              firstorder.
              rewrite Z.gtb_lt in H4.
              omega.
          }
          exact (H4 _ H3).
        + right.
          generalize mu as mu0, a as a0, H2, H1.
          induction mu0.
          * unfold Zvec_total ; simpl ; firstorder.
          * intros a1 Ha1 H3.
            pose (H4 := thm_Zvec_nondecb_cons _ _ H3).
            clearbody H4.
            unfold Zvec_nondecb in H3.
            simpl_destruct H3 as [Ha10 H3].
            simpl in IHmu0.
            simpl.
            pose (H5 := (IHmu0 _ (Z.le_trans _ _ _ Ha1 Ha10) H4)).
            omega.
    }
    rewrite (thm_Zvec_total_app _ _) in Htot.
    destruct Hor as [H0|H0] ; omega.
  Qed.
  Theorem thm_Zvec_total_mrev:
    forall lambda,
      (Zvec_total (rev (map Z.opp lambda))
       = - Zvec_total lambda)%Z.
  Proof.
    induction lambda.
    - trivial.
    - simpl.
      rewrite thm_Zvec_total_app, IHlambda.
      simpl.
      omega.
  Qed.
  Theorem thm_Zvec_nondecb_fact1 :
    forall a b lambda,
      (0 <= b)%Z
      -> Zvec_nondecb (a::b::lambda) = true
      -> Zvec_allb (Z.leb 0%Z) lambda = true.
  Proof.
    unfold Zvec_nondecb.
    simpl.
    intros a b lambda H1 H2.
    simpl_destruct H2 as [H2 H3].
    induction lambda.
    - simpl ; trivial.
    - simpl_extra.
      simpl_destruct H3 as [H3 H4].
      split.
      + exact (Z.le_trans _ _ _ H1 H3).
      + refine (IHlambda _).
        simpl in H4.
        generalize H4.
        destruct lambda ; firstorder.
        simpl_extra.
        simpl_extra in H0.
        firstorder.
  Qed.
  Theorem thm_Zvec_nondecb_fact2 :
    forall a b lambda,
      (0 <= b)%Z
      -> Zvec_nondecb (a::b::lambda) = true
      -> (Zvec_total lambda >= 0)%Z.
  Proof.
    unfold Zvec_nondecb.
    simpl.
    intros a b lambda H1 H2.
    generalize lambda as lambda0, (thm_Zvec_nondecb_fact1 a b lambda H1 H2).
    induction lambda0.
    - unfold Zvec_total ; firstorder.
    - simpl_extra.
      firstorder.
  Qed.
  Theorem thm_Zvec_nondecb_fact3 :
    forall a b lambda,
      Zvec_nondecb (a::b::lambda) = true
      -> Zvec_short_allb Z.leb (a::b::lambda) lambda = true.
  Proof.
    intros a b lambda Hab.
    pose (Hb := thm_Zvec_nondecb_cons a (b::lambda) Hab).
    unfold Zvec_nondecb, tl in Hab.
    unfold Zvec_nondecb, tl in Hb.
    refine (thm_Zvec_leb_trans32 _ _ _ _ Hab Hb).
    simpl.
    omega.
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
  Theorem thm_Zvec_nondecb_mrev :
    forall lambda,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb (rev (map Z.opp lambda)) = true.
  Proof.
    induction lambda.
    - trivial.
    - simpl.
      intros Hal.
      rewrite thm_Zvec_nondecb_app_iff.
      repeat try split.
      + exact (IHlambda (thm_Zvec_nondecb_cons _ _ Hal)).
      + rewrite thm_last_rev.
        destruct lambda ; simpl.
        * omega.
        * unfold Zvec_nondecb in Hal.
          simpl_destruct Hal as [Haz _].
          omega.
  Qed.
  Theorem thm_mrev_inverse :
    forall l, l = map Z.opp (rev (rev (map Z.opp l))).
  Proof.
    intros l.
    rewrite rev_involutive, map_map.
    induction l.
    - trivial.
    - simpl.
      rewrite Z.opp_involutive, <- IHl.
      trivial.
  Qed.
  Theorem thm_Zvec_leb_mrev :
    forall lambda mu : list Z,
      length lambda = length mu
      -> Zvec_short_allb Z.leb mu lambda = true
      -> Zvec_short_allb
           Z.leb (rev (map Z.opp lambda)) (rev (map Z.opp mu)) = true.
  Proof.
    intros lambda mu.
    set (rlambda := rev (map Z.opp lambda)).
    set (rmu := rev (map Z.opp mu)).
    assert (lambda = map Z.opp (rev rlambda)) as Hlambda.
    { apply thm_mrev_inverse. }
    assert (mu = map Z.opp (rev rmu)) as Hmu.
    { apply thm_mrev_inverse. }
    rewrite Hlambda, Hmu.
    tac_length.
    generalize rlambda, rmu.
    clear.
    induction rlambda.
    - trivial.
    - destruct rmu; simpl.
      + firstorder.
      + simpl_extra.
        intros Hlength H.
        assert (length (map Z.opp (rev rmu))
                = length (map Z.opp (rev rlambda)))
          as Hlength2.
        { tac_length. }
        rewrite thm_Zvec_leb_app in H.
        simpl_destruct H as [H1 H2].
        simpl_extra in H2.
        split.
        * clear -H2. omega.
        * refine (IHrlambda rmu Hlength H1).
        * exact Hlength2.
  Qed.
  Theorem thm_Zvec_leb_mrev1 :
    forall lambda mu : list Z,
      length lambda = S (S (length mu))
      -> Zvec_short_allb Z.leb mu (tl (tl lambda)) = true
      -> Zvec_short_allb
           Z.leb (rev (map Z.opp lambda)) (rev (map Z.opp mu)) = true.
  Proof.
    destruct lambda as [|a [|b lambda]] ; simpl ; firstorder.
    simpl_extra in H.
    rewrite <- app_assoc ; simpl.
    rewrite (app_nil_end (rev (map Z.opp mu))).
    rewrite thm_Zvec_leb_app.
    - simpl_extra.
      apply thm_Zvec_leb_mrev ; trivial.
    - tac_length.
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
  Theorem thm_Zvec_leb_mrev2 :
    forall lambda mu : list Z,
      length lambda = S (S (length mu))
      -> Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb
           Z.leb (rev (map Z.opp mu))
           (tl (tl (rev (map Z.opp lambda)))) = true.
  Proof.
    intros lambda mu Hlength.
    rewrite thm_tl_rev, thm_removelast_map.
    rewrite thm_tl_rev, thm_removelast_map.
    assert (lambda <> nil) as H ; tac_length.
    rewrite (app_removelast_last 0%Z H) at 1.
    set (a := last lambda 0%Z).
    assert (removelast lambda <> nil) as H0 ; tac_length.
    rewrite (app_removelast_last 0%Z H0) at 1.
    set (b := last (removelast lambda) 0%Z).
    set (l := removelast (removelast lambda)).
    rewrite <- app_assoc.
    simpl.
    rewrite (app_nil_end mu) at 1.
    intros H1.
    assert (length mu = length l) as H2 ; unfold l ; tac_length.
    refine (thm_Zvec_leb_mrev mu l _ _).
    - assumption.
    - rewrite thm_Zvec_leb_app in H1 ; firstorder.
  Qed.
  Theorem thm_Zvec_total_mul :
    forall m lambda,
      (Zvec_total (Zvec_mul m lambda) = m * Zvec_total lambda)%Z.
  Proof.
    unfold Zvec_mul.
    induction lambda ; simpl.
    - omega.
    - rewrite IHlambda.
      rewrite Z.mul_add_distr_l.
      trivial.
  Qed.
  Theorem thm_Z_of_nat_S :
    forall n, Z.of_nat (S n) = (1 + Z.of_nat n)%Z.
  Proof.
    intros.
    rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    trivial.
  Qed.
  Theorem thm_Zvec_total_repeat :
    forall m a,
      (Zvec_total (repeat a m) = (Z.of_nat m) * a)%Z.
  Proof.
    intros.
    induction m.
    - trivial.
    - simpl repeat.
      simpl Zvec_total.
      rewrite IHm, thm_Z_of_nat_S.
      rewrite Z.mul_add_distr_r.
      omega.
  Qed.
  Theorem thm_Zvec_nondecb_repeat :
    forall a n, Zvec_nondecb (repeat a n) = true.
  Proof.
    destruct n ; simpl ; firstorder.
    induction n ; simpl ; firstorder.
    apply thm_Zvec_nondecb_join2.
    omega.
    assumption.
  Qed.
End list_thm.

Hint Rewrite
     thm_Zvec_total_app
     thm_Zvec_total_repeat
     thm_Z_of_nat_S
     Z.mul_add_distr_r
     Z.add_assoc
     Z.mul_1_l
     Z.mul_1_r
: rewritetotal.
Tactic Notation "simpl_total" :=
  repeat (simpl || autorewrite with rewritetotal).
Tactic Notation "simpl_total" "in" hyp(H) :=
  repeat (simpl in H || autorewrite with rewritetotal in H).
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

Section lie.
  Inductive lie_types : Set :=
  | lie_A_type
  | lie_B_type
  | lie_C_type
  | lie_D_type
  | lie_E6_type
  | lie_E7_type
  | lie_E8_type
  | lie_F4_type
  | lie_G2_type.
  Inductive lie_algebra : Set :=
  | lie_A : {n | n > 0} -> lie_algebra
  | lie_B : {n | n > 1} -> lie_algebra
  | lie_C : {n | n > 2} -> lie_algebra
  | lie_D : {n | n > 3} -> lie_algebra
  | lie_E6
  | lie_E7
  | lie_E8
  | lie_F4
  | lie_G2.
  Definition lie_algebra_type g :=
    match g with
      | lie_A _ => lie_A_type
      | lie_B _ => lie_B_type
      | lie_C _ => lie_C_type
      | lie_D _ => lie_D_type
      | lie_E6 => lie_E6_type
      | lie_E7 => lie_E7_type
      | lie_E8 => lie_E8_type
      | lie_F4 => lie_F4_type
      | lie_G2 => lie_G2_type
    end.
  Definition lie_rank g :=
    match g with
      | lie_A (exist _ n _) => n
      | lie_B (exist _ n _) => n
      | lie_C (exist _ n _) => n
      | lie_D (exist _ n _) => n
      | lie_E6 => 6
      | lie_E7 => 7
      | lie_E8 => 8
      | lie_F4 => 4
      | lie_G2 => 2
    end.
  Definition lie_dimension g :=
    match g with
      | lie_A (exist _ n _) => n*(2+n)
      | lie_B (exist _ n _) => n*(1+2*n)
      | lie_C (exist _ n _) => n*(1+2*n)
      | lie_D (exist _ n _) => n*(2*n-1)
      | lie_E6 => 78
      | lie_E7 => 133
      | lie_E8 => 248
      | lie_F4 => 52
      | lie_G2 => 14
    end.
  Definition lie_embedding_dim g :=
    match g with
      | lie_A (exist _ n _) => 1+n
      | _ => lie_rank g
    end.
  Definition lie_is_dominant_wt_type type mu :=
    match type with
      | lie_A_type => (Zvec_nonincb mu) && (Zvec_total mu =? 0)%Z
      | lie_B_type => (Zvec_nonincb mu) && (0 <=? last mu 0)%Z
      | lie_C_type => (Zvec_nonincb mu) && (0 <=? last mu 0)%Z
      | lie_D_type => (Zvec_nonincb mu) && (- last mu 0 <=? last (removelast mu) 0)%Z
      | lie_E6_type => (length mu =? 6) && (Zvec_all_nonnegb mu)
      | lie_E7_type => (length mu =? 7) && (Zvec_all_nonnegb mu)
      | lie_E8_type => (length mu =? 8) && (Zvec_all_nonnegb mu)
      | lie_F4_type => (length mu =? 4) && (Zvec_all_nonnegb mu)
      | lie_G2_type => (length mu =? 2) && (Zvec_all_nonnegb mu)
    end.
  Definition lie_is_dominant_wt_alg g mu :=
    ((length mu) =? (lie_embedding_dim g))
      && (lie_is_dominant_wt_type (lie_algebra_type g) mu).
  Definition lie_is_radical_wt_type type mu :=
    match type with
      | lie_A_type => (Zvec_nonincb mu) && (Zvec_total mu =? 0)%Z
      | lie_B_type => (Zvec_nonincb mu) && (0 <=? last mu 0)%Z
      | lie_C_type => (Zvec_nonincb mu) && (0 <=? last mu 0)%Z && (Z.even (Zvec_total mu))
      | lie_D_type => (Zvec_nonincb mu) && (- last mu 0 <=? last (removelast mu) 0)%Z
                                        && (Z.even (Zvec_total mu))
      | lie_E6_type => match mu with
                         | a1::a2::a3::a4::a5::a6::nil
                           => (Zvec_all_nonnegb mu)
                                && (Z.modulo (a1 - a3 + a5 - a6) 3 =? 0)%Z
                         | _ => false
                       end
      | lie_E7_type => match mu with
                         | a1::a2::a3::a4::a5::a6::a7::nil
                           => (Zvec_all_nonnegb mu) && (Z.even (a2 + a5 + a7))%Z
                         | _ => false
                       end
      | lie_E8_type => (length mu =? 8) && (Zvec_all_nonnegb mu)
      | lie_F4_type => (length mu =? 4) && (Zvec_all_nonnegb mu)
      | lie_G2_type => (length mu =? 2) && (Zvec_all_nonnegb mu)
    end.
  Definition lie_is_radical_wt_alg g mu :=
    ((length mu) =? (lie_embedding_dim g))
      && (lie_is_radical_wt_type (lie_algebra_type g) mu).
  (*radical multiple of fundamental weight i of g if 1<=i<=n, otherwise zero weight*)
  Definition lie_radical_fundamental_wt g i :=
    if (i =? 0) || (lie_rank g <? i)
    then repeat 0%Z (lie_embedding_dim g)
    else
      match g with
        | lie_A (exist _ n _)
          => let d := Z.gcd (Z.of_nat i) (1 + Z.of_nat n) in
             (repeat (Z.of_nat (S n - i) / d)%Z i)
               ++ (repeat (- Z.of_nat i / d)%Z (S n - i))
        | lie_B (exist _ n _)
          => (repeat 1%Z i) ++ (repeat 0%Z (n - i))
        | lie_C (exist _ n _)
          => (repeat (if even i then 1%Z else 2%Z) i)
               ++ repeat 0%Z (n - i)
        | lie_D (exist _ n _)
          => if i =? n-1
             then if even n
                  then (repeat 1%Z (n - 1)) ++ (-1)%Z::nil
                  else (repeat 2%Z (n - 1)) ++ (-2)%Z::nil
             else (repeat (if even i then 1%Z else 2%Z) i)
                    ++ (repeat 0%Z (n - i))
        | _ => basic_list
                 _
                 match g, i with
                   | lie_E6, 1 => 3%Z
                   | lie_E6, 3 => 3%Z
                   | lie_E6, 5 => 3%Z
                   | lie_E6, 6 => 3%Z
                   | lie_E7, 2 => 2%Z
                   | lie_E7, 5 => 2%Z
                   | lie_E7, 7 => 2%Z
                   | _     , _ => 1%Z
                 end
                 i
                 0%Z
                 (lie_rank g)
      end.
  (*revwt stands for reversed weight*)
  Definition lie_is_dominant_revwt_type type mu :=
    match type with
      | lie_A_type => (Zvec_nondecb mu) && (Zvec_total mu =? 0)%Z
      | lie_B_type => (Zvec_nondecb mu) && (0 <=? hd 0 mu)%Z
      | lie_C_type => (Zvec_nondecb mu) && (0 <=? hd 0 mu)%Z
      | lie_D_type => (Zvec_nondecb mu) && (- hd 0 mu <=? hd 0 (tl mu))%Z
      | lie_E6_type => (length mu =? 6) && (Zvec_all_nonnegb mu)
      | lie_E7_type => (length mu =? 7) && (Zvec_all_nonnegb mu)
      | lie_E8_type => (length mu =? 8) && (Zvec_all_nonnegb mu)
      | lie_F4_type => (length mu =? 4) && (Zvec_all_nonnegb mu)
      | lie_G2_type => (length mu =? 2) && (Zvec_all_nonnegb mu)
    end.
  Definition lie_is_dominant_revwt_alg g mu :=
    ((length mu) =? (lie_embedding_dim g))
      && (lie_is_dominant_revwt_type (lie_algebra_type g) mu).
  Definition lie_is_radical_revwt_type type mu :=
    match type with
      | lie_A_type => (Zvec_nondecb mu) && (Zvec_total mu =? 0)%Z
      | lie_B_type => (Zvec_nondecb mu) && (0 <=? hd 0 mu)%Z
      | lie_C_type => (Zvec_nondecb mu) && (0 <=? hd 0 mu)%Z && (Z.even (Zvec_total mu))
      | lie_D_type => (Zvec_nondecb mu) && (- hd 0 mu <=? hd 0 (tl mu))%Z
                                        && (Z.even (Zvec_total mu))
      | lie_E6_type => match mu with
                         | a6::a5::a4::a3::a2::a1::nil
                           => (Zvec_all_nonnegb mu)
                                && (Z.modulo (a1 - a3 + a5 - a6) 3 =? 0)%Z
                         | _ => false
                       end
      | lie_E7_type => match mu with
                         | a7::a6::a5::a4::a3::a2::a1::nil
                           => (Zvec_all_nonnegb mu) && (Z.even (a2 + a5 + a7))%Z
                         | _ => false
                       end
      | lie_E8_type => (length mu =? 8) && (Zvec_all_nonnegb mu)
      | lie_F4_type => (length mu =? 4) && (Zvec_all_nonnegb mu)
      | lie_G2_type => (length mu =? 2) && (Zvec_all_nonnegb mu)
    end.
  Definition lie_is_radical_revwt_alg g mu :=
    ((length mu) =? (lie_embedding_dim g))
      && (lie_is_radical_revwt_type (lie_algebra_type g) mu).
  Definition lie_radical_fundamental_revwt_alg g i :=
    if (i =? 0) || (lie_rank g <? i)
    then repeat 0%Z (lie_embedding_dim g)
    else
      match g with
        | lie_A (exist _ n _)
          => let d := Z.gcd (Z.of_nat i) (1 + Z.of_nat n) in
             (repeat (- Z.of_nat i / d)%Z (S n - i))
               ++ (repeat (Z.of_nat (S n - i) / d)%Z i)
        | lie_B (exist _ n _)
          => (repeat 0%Z (n - i)) ++ (repeat 1%Z i)
        | lie_C (exist _ n _)
          => (repeat 0%Z (n - i))
               ++ (repeat (if even i then 1%Z else 2%Z) i)
        | lie_D (exist _ n _)
          => if i =? n-1
             then if even n
                  then (-1)%Z::(repeat 1%Z (n - 1))
                  else (-2)%Z::(repeat 2%Z (n - 1))
             else (repeat 0%Z (n - i))
                    ++ (repeat (if even i then 1%Z else 2%Z) i)
        | _ => basic_list_rev
                 _
                 match g, i with
                   | lie_E6, 1 => 3%Z
                   | lie_E6, 3 => 3%Z
                   | lie_E6, 5 => 3%Z
                   | lie_E6, 6 => 3%Z
                   | lie_E7, 2 => 2%Z
                   | lie_E7, 5 => 2%Z
                   | lie_E7, 7 => 2%Z
                   | _     , _ => 1%Z
                 end
                 i
                 0%Z
                 (lie_rank g)
      end.
End lie.

Section data.
  Definition is_exceptional_multiplier g i m :=
    if (m <? 0)%Z
    then false
    else
      if (m =? 0) %Z
      then true
      else
        if (i =? 0) || (lie_rank g <? i)
        then false
        else
          match g with
            | lie_A (exist _ n _)
              => (n =? 3)
                   || (i =? 1)
                   || (i =? n)
            | lie_B (exist _ n _)
              => (n =? 2)
                   || (i =? 1)
                   || (i =? 2) && (m <=? 2)%Z
                   || (m <=? 1)%Z
            | lie_C (exist _ n _)
              => (n =? 2)
                   || (n =? 3) && (i =? 3) && (m <=? 1)%Z
                   || (n =? 4) && (i =? 4) && (m <=? 2)%Z
                   || (i =? 1)
                   || (i =? 2) && (m <=? 2)%Z
                   || (even i) && (m <=? 1)%Z
            | lie_D (exist _ n _)
              => (n =? 3)
                   || (n =? 4) && ((i =? 3) || (i =? 4))
                   || (i =? 1)
                   || (even n) && (((i =? 2) && (m <=? 2)%Z)
                                     || ((even i) && (m <=? 1)%Z)
                                     || ((1 + i =? n) && (m <=? 1)%Z))
            | lie_E6
              => false
            | lie_E7
              => ((i =? 1) && (m <=? 2)%Z)
                   || ((i =? 6) && (m <=? 1)%Z)
                   || ((i =? 7) && (m <=? 1)%Z)
            | lie_E8
              => ((i =? 1) && (m <=? 1)%Z) || ((i =? 8) && (m <=? 8)%Z)
            | lie_F4
              => ((i =? 1) || (i =? 4)) && (m <=? 2)%Z
            | lie_G2
              => (m <=? 2)%Z
          end.
  Definition is_mixed_by_hand_revwt_alg g lambda :=
    (lie_is_radical_revwt_alg g lambda)
      && match g, lambda with
           | lie_A (exist _ 2 _), (-1::0::1::nil)%Z => true
           | lie_A (exist _ 3 _), (-1::0::0::1::nil)%Z => true
           | lie_A (exist _ 3 _), (-2::0::1::1::nil)%Z => true
           | lie_A (exist _ 3 _), (-1::-1::0::2::nil)%Z => true
           | lie_B (exist _ 2 _), (0::1::2::nil)%Z => true
           | lie_B (exist _ 3 _), (0::1::2::nil)%Z => true
           | lie_B (exist _ 3 _), (0::3::3::nil)%Z => true
           | lie_B (exist _ 3 _), (1::1::2::nil)%Z => true
           | lie_B (exist _ 3 _), (1::2::2::nil)%Z => true
           | lie_B (exist _ 3 _), (2::2::2::nil)%Z => true
           | lie_B (exist _ 4 _), (0::1::2::2::nil)%Z => true
           | lie_B (exist _ 4 _), (0::0::3::3::nil)%Z => true
           | _, _ => false
         end.
  (*TODO: add more mixed representations shown "by_hand".*)
End data.

Section branching.
  (*w0 of sl(n+1) coincides with w0 of sl(2)xsl(n-1)*)
  (*Branching of radical representation of sl(n+1) to sl(n-1),
    restricting to zero weight of sl(2).  This criterion is complete.*)
  Definition radical_branching_A_two_revwt_b lambda mu :=
    (length lambda =? S (S (length mu)))
      && (lie_is_radical_revwt_type lie_A_type lambda)
      && (lie_is_radical_revwt_type lie_A_type mu)
      && (Zvec_short_allb Z.leb lambda mu)
      && (Zvec_short_allb Z.leb mu (tl (tl lambda))).
  Definition Is_known_w0_branching_A_revwt lambda mu :=
    radical_branching_A_two_revwt_b lambda mu = true.
  (*w0 of so(2n+1) coincides with w0 of so(4)xso(2n-3)*)
  (*Partial criterion for branching from so(2n+1) to so(2n-1)
    with zero so(2) charge.  Then do it twice.*)
  Definition known_radical_branching_B_one_revwt_b lambda mu :=
    (length lambda =? S (length mu))
      && (lie_is_radical_revwt_type lie_B_type lambda)
      && (lie_is_radical_revwt_type lie_B_type mu)
      && (Zvec_short_allb (fun a b => Z.even (Z.sub a b))
                          (Zvec_short_max lambda mu)
                          (Zvec_long_min (tl lambda) (tl mu))).
  Definition Is_known_w0_branching_B_revwt lambda nu :=
    exists mu,
      known_radical_branching_B_one_revwt_b lambda mu = true
      /\ known_radical_branching_B_one_revwt_b mu nu = true.
  (*TODO: add more known branchings that preserve w0*)
  (*w0 of E8 coincides with w0 of D8*)
  (*Partial criterion for branching from E8 to D8.*)
  Definition Is_known_w0_branching_E8_D8_revwt (lambda mu : list Z) :=
    (lambda = mu)
      /\ lie_is_radical_revwt_type lie_E8_type lambda = true
      /\ lie_is_radical_revwt_type lie_D_type mu = true.
  (*Put together all known branchings preserving w0.*)
  (*No need to check ranks of g and h as it is done by the Is_known_... functions.*)
  Definition Is_known_w0_branching_revwt_alg g lambda h mu :=
    lie_is_radical_revwt_alg g lambda = true
    /\ lie_is_radical_revwt_alg h mu = true
    /\ match lie_algebra_type g, lie_algebra_type h with
         | lie_A_type, lie_A_type => Is_known_w0_branching_A_revwt lambda mu
         | lie_B_type, lie_B_type => Is_known_w0_branching_B_revwt lambda mu
         | lie_E8_type, lie_D8_type => Is_known_w0_branching_E8_D8_revwt lambda mu
         | _, _ => False
       end.
End branching.

Section main.
  Definition Is_exceptional_revwt_alg g lambda :=
    exists i m,
      (is_exceptional_multiplier g i m = true)
      /\ lambda = Zvec_mul m (lie_radical_fundamental_revwt_alg g i).
  Inductive Is_mixed_revwt_alg : lie_algebra -> list Z -> Prop :=
  | mixed_by_hand :
      forall g lambda,
        is_mixed_by_hand_revwt_alg g lambda = true
        -> Is_mixed_revwt_alg g lambda
  | mixed_by_ideal :
      forall g lambda mu,
        Is_mixed_revwt_alg g mu
        /\ lie_is_dominant_revwt_alg g (Zvec_short_sub lambda mu) = true
        -> Is_mixed_revwt_alg g lambda
  | mixed_by_induction :
      forall g lambda h mu,
        Is_mixed_revwt_alg h mu
        /\ Is_known_w0_branching_revwt_alg g lambda h mu
        -> Is_mixed_revwt_alg g lambda.
End main.


Section theorems_for_A_type.
  Ltac show_mixed_by_ideal g lambda mu :=
    match goal with
      | [Hg : g = _ |- _]
        =>
        (right;
         refine (mixed_by_ideal g lambda mu _) ;
         split ;
         [
           refine (mixed_by_hand g mu _) ;
           rewrite Hg ;
           simpl ; trivial
         |
         rewrite Hg ;
           unfold Zvec_short_sub, lie_is_dominant_revwt_alg ;
           simpl ;
           unfold Zvec_nondecb ;
           simpl_extra ;
           omega
        ])
    end.
  Ltac show_exceptional g i m :=
    match goal with
      | [Hg : g = _ |- _]
        =>
        (
          left;
          exists i, m;
          rewrite Hg;
          unfold is_exceptional_multiplier;
          split;
          [
            assert (m <? 0 = false)%Z as H4;
            [apply Z.ltb_nlt; omega|];
            rewrite H4;
            destruct (m =? 0)%Z ; firstorder
          |
            set (t := lie_radical_fundamental_revwt_alg _ _);
            compute in t;
            unfold t;
            simpl_extra ;
            firstorder
          ]
        )
    end.
  Theorem thm_radical_length :
    forall g lambda,
      lie_is_radical_revwt_alg g lambda = true
      -> length lambda = lie_embedding_dim g.
  Proof.
    intros g lambda H.
    unfold lie_is_radical_revwt_alg in H.
    autorewrite with rewritesome in H.
    firstorder.
  Qed.
  Theorem thm_main_A1 :
    forall g lambda Hn,
      g = (lie_A (exist (fun n : nat => n > 0) 1 Hn))
      -> lie_is_radical_revwt_alg g lambda = true
      -> (Is_exceptional_revwt_alg g lambda) \/ (Is_mixed_revwt_alg g lambda).
  Proof.
    intros g lambda Hn Hg H.
    rewrite Hg in H.
    unfold lie_is_radical_revwt_alg in H.
    simpl in H.
    unfold Zvec_nondecb in H.
    autorewrite with rewritesome in H.
    destruct lambda as [|a [|b [|]]] ; simpl in H ; try omega.
    simpl_extra in H.
    (*All representations of A1 are exceptional.*)
    show_exceptional g 1 b.
  Qed.
  Theorem thm_main_A2 :
    forall g lambda Hn,
      g = (lie_A (exist (fun n : nat => n > 0) 2 Hn))
      -> lie_is_radical_revwt_alg g lambda = true
      -> (Is_exceptional_revwt_alg g lambda) \/ (Is_mixed_revwt_alg g lambda).
  Proof.
    intros g lambda Hn Hg H.
    rewrite Hg in H.
    unfold lie_is_radical_revwt_alg in H.
    simpl in H.
    unfold Zvec_nondecb in H.
    simpl_extra in H.
    destruct lambda as [|a [|b [|c [|]]]] ; simpl in H ; try omega.
    simpl_extra in H.
    destruct H as [_ [[Hab Hbc] Hsum]].
    destruct (Z_le_lt_eq_dec _ _ Hab).
    - destruct (Z_le_lt_eq_dec _ _ Hbc).
      + (*a<b<c implies (a,b,c) dominates (-1,0,1), mixed "by hand"*)
        show_mixed_by_ideal g (a::b::c::nil) (-1::0::1::nil)%Z.
      + (*a<b=c implies (a,b,c) = c (-2,1,1) exceptional.*)
        show_exceptional g 2 c.
    - (*a=b<=c implies (a,b,c) = -a (-1,-1,2) exceptional.*)
      show_exceptional g 1 (-a)%Z.
  Qed.
  Theorem thm_main_A3 :
    forall g lambda Hn,
      g = (lie_A (exist (fun n : nat => n > 0) 3 Hn))
      -> lie_is_radical_revwt_alg g lambda = true
      -> (Is_exceptional_revwt_alg g lambda) \/ (Is_mixed_revwt_alg g lambda).
  Proof.
    intros g lambda Hn Hg H.
    rewrite Hg in H.
    unfold lie_is_radical_revwt_alg in H.
    simpl in H.
    unfold Zvec_nondecb in H.
    simpl_extra in H.
    destruct lambda as [|a [|b [|c [|d [|]]]]] ; simpl in H ; try omega.
    simpl_extra in H.
    destruct H as [_ [[Hab [Hbc Hcd]] Hsum]].
    destruct (Z_le_lt_eq_dec _ _ Hab).
    - (*a<b*)
      destruct (Z_le_lt_eq_dec _ _ Hcd).
      + (*a<b/\c<d implies (a,b,c,d) dominates (-1,0,0,1), mixed*)
        show_mixed_by_ideal g (a::b::c::d::nil) (-1::0::0::1::nil)%Z.
      + (*a<b/\c=d implies a<=b-2 by parity*)
        assert (a <= b - 1)%Z as Hab1. omega.
        assert (a <= b - 2)%Z as Hab2. destruct (Z_le_lt_eq_dec _ _ Hab1) ; omega.
        destruct (Z_le_lt_eq_dec _ _ Hbc).
        {
          (*a<b<c=d implies (a,b,c,d) dominates (-2,0,1,1), mixed*)
          show_mixed_by_ideal g (a::b::c::d::nil) (-2::0::1::1::nil)%Z.
        }
        {
          (*a<b=c=d implies (a,b,c,d) = b (-3,1,1,1) exceptional*)
          show_exceptional g 3 d.
        }
    - (*a=b*)
      destruct (Z_le_lt_eq_dec _ _ Hbc).
      + (*a=b<c*)
        destruct (Z_le_lt_eq_dec _ _ Hcd).
        * (*a=b<c<d implies (a,b,c,d) dominates (-1,-1,0,2), mixed*)
          show_mixed_by_ideal g (a::b::c::d::nil) (-1::-1::0::2::nil)%Z.
        * (*a=b<c=d implies (a,b,c,d)=d(-1,-1,1,1) exceptional*)
          show_exceptional g 2 d.
      + (*a=b=c<=d implies (a,b,c,d)=-a(-1,-1,-1,3) exceptional*)
        show_exceptional g 1 (-a)%Z.
  Qed.
  Local Fixpoint tmp_A_pred (lambda mu : list Z) :=
    match lambda with
      | nil => nil
      | a :: lambda' =>
        match mu with
          | nil => nil
          | b :: mu' =>
            if (a <? b)%Z then (b - 1)%Z :: mu' else b :: tmp_A_pred lambda' mu'
        end
    end.
  Local Fixpoint tmp_A_get_repeat (lambda mu : list Z) (n : nat) :=
    match n with
      | 0 => mu
      | S n' => tmp_A_pred lambda (tmp_A_get_repeat lambda mu n')
    end.
  Local Definition tmp_A_get (lambda : list Z) :=
    let mu := tl (tl lambda) in
    tmp_A_get_repeat lambda mu (Z.abs_nat (Zvec_total mu)).
  Theorem thm_A_pred_length0 :
    forall lambda0 mu0, length (tmp_A_pred lambda0 mu0) <= length mu0.
  Proof.
    intros lambda0 mu0.
    generalize lambda0 as lambda1.
    induction mu0 ; destruct lambda1 as [|z lambda1] ; simpl ; firstorder.
    destruct (z <? a)%Z ; simpl ; firstorder.
  Qed.
  Theorem thm_A_pred_length1 :
    forall lambda0 mu0,
      length mu0 <= length lambda0
      -> length (tmp_A_pred lambda0 mu0) = length mu0.
  Proof.
    intros lambda0 mu0.
    generalize lambda0 as lambda1.
    induction mu0 ; destruct lambda1 as [|z lambda1] ; simpl ; firstorder.
    destruct (z <? a)%Z ; simpl ; firstorder.
  Qed.
  Theorem thm_A_pred_leb :
    forall lambda mu,
      Zvec_short_allb Z.leb (tmp_A_pred lambda mu) mu = true.
  Proof.
    intros lambda mu.
    generalize lambda as lambda1.
    induction mu ; destruct lambda1 ; simpl ; firstorder.
    destruct (z <? a)%Z ; simpl_extra ; firstorder.
    apply thm_Zvec_leb_refl.
  Qed.
  Theorem thm_A_pred_leb2 :
    forall lambda mu,
      Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb lambda (tmp_A_pred lambda mu) = true.
  Proof.
    induction lambda.
    - simpl ; firstorder.
    - destruct mu.
      + simpl ; firstorder.
      + simpl.
        intros H.
        simpl_destruct H as [H H0].
        destruct (Z_le_lt_eq_dec _ _ H) as [H1|H1].
        * pose (H2 := H1).
          rewrite Zlt_is_lt_bool in H2.
          rewrite H2.
          rewrite H0.
          simpl_extra.
          omega.
        * rewrite H1.
          rewrite (Z.ltb_irrefl z).
          rewrite (Z.leb_refl z).
          firstorder.
  Qed.
  Theorem thm_A_pred_tot :
    forall lambda0 mu0,
      Zvec_short_allb Z.leb lambda0 mu0 = true
      -> length mu0 <= length lambda0
      -> Zvec_short_allb Z.eqb lambda0 mu0 = false
      -> Zvec_total (tmp_A_pred lambda0 mu0) = (Zvec_total mu0 - 1)%Z.
  Proof.
    intros lambda0 mu0.
    generalize lambda0 as lambda1.
    induction mu0 ; destruct lambda1 ; simpl ;
    try (intros H1 H2 H3 ; contradiction (diff_true_false H3)).
    intros H1 H3 H4.
    simpl_destruct H1 as [H1 H2].
    destruct (Z_le_lt_eq_dec _ _ H1) as [H5|H5].
    - rewrite Zlt_is_lt_bool in H5.
      rewrite H5.
      simpl.
      omega.
    - rewrite H5.
      rewrite (Z.ltb_irrefl a).
      simpl.
      rewrite H5 in H4.
      rewrite (Z.eqb_refl a) in H4.
      simpl in H4.
      assert (forall b c, a + b = a + c - 1 <-> b = c - 1)%Z as Hsum.
      { firstorder ; omega. }
      rewrite Hsum.
      apply le_S_n in H3.
      exact (IHmu0 lambda1 H2 H3 H4).
  Qed.
  (*Here Zvec_short_map_zip is used to pick the first (length mu) components of lambda*)
  Theorem thm_Zvec_leb_total :
    forall mu lambda,
      length mu <= length lambda
      -> Zvec_short_allb Z.leb lambda mu = true
      -> (Zvec_total (Zvec_short_map_zip (fun _ a => a) mu lambda)
          <= Zvec_total mu)%Z.
  Proof.
    induction mu.
    - simpl ; firstorder.
    - destruct lambda.
      + simpl ; firstorder.
      + simpl.
        intros H H0.
        simpl_destruct H0 as [H0 H1].
        pose (H2 := (IHmu _ (le_S_n _ _ H) H1)).
        omega.
  Qed.
  Theorem thm_A_leb_eqb_tot :
    forall lambda mu,
      length mu <= length lambda
      -> Zvec_short_allb Z.leb lambda mu = true
      -> (Zvec_short_allb Z.eqb lambda mu = true
          <-> Zvec_total mu
              = Zvec_total (Zvec_short_map_zip (fun _ a => a) mu lambda)).
  Proof.
    intros lambda mu Hlength Hleb.
    split.
    - generalize mu as mu0, lambda as lambda0, Hlength.
      induction mu0.
      + simpl ; firstorder.
      + destruct lambda0.
        * simpl ; firstorder.
        * simpl.
          intros H H0.
          simpl_destruct H0 as [H0 H1].
          rewrite H0.
          rewrite <- (IHmu0 _ (le_S_n _ _ H) H1).
          trivial.
    - generalize mu as mu0, lambda as lambda0, Hlength, Hleb.
      induction mu0.
      + simpl ; firstorder.
        destruct lambda0 ; firstorder.
      + destruct lambda0.
        * simpl ; firstorder.
        * simpl.
          intros H H0 H2.
          simpl_destruct H0 as [H0 H1].
          pose (H3 := le_S_n _ _ H).
          pose (H4 := thm_Zvec_leb_total _ _ H3 H1).
          simpl_extra.
          split ; [|refine (IHmu0 _ H3 H1 _)] ; omega.
  Qed.
  Theorem thm_A_nondec_total_short_map :
    (forall lambda mu,
       Zvec_nondecb lambda = true
       -> Zvec_total lambda = 0
       -> Zvec_total (Zvec_short_map_zip (fun _ a : Z => a) mu lambda) <= 0)%Z.
  Proof.
    pose (tmp := (fix tmp (lambda mu : list Z) :=
                    match mu with
                      | nil => lambda
                      | _::mu' => match lambda with
                                    | nil => nil
                                    | _::lambda' => tmp lambda' mu'
                                  end
                    end)).
    assert (forall mu lambda,
              (Zvec_short_map_zip (fun _ a : Z => a) mu lambda)++(tmp lambda mu)
              = lambda) as H.
    {
      induction mu ; simpl.
      - destruct lambda ; simpl ; trivial.
      - destruct lambda ; simpl ; trivial.
        rewrite (IHmu lambda).
        trivial.
    }
    intros lambda mu Hnondec Htot.
    pose (thm1 :=
            thm_Zvec_nondecb_total_app
              (Zvec_short_map_zip (fun _ a : Z => a) mu lambda)
              (tmp lambda mu)).
    rewrite H in thm1.
    firstorder.
  Qed.
  Theorem thm_A_get_hd_leb :
    (forall lambda mu n,
       lambda <> nil
       -> mu <> nil
       -> hd 0 lambda <= hd 0 mu
       -> hd 0 lambda <= hd 0 (tmp_A_get_repeat lambda mu n))%Z.
  Proof.
    destruct lambda, mu ; simpl ; intros ; firstorder.
    induction n.
    - simpl ; trivial.
    - simpl.
      destruct (tmp_A_get_repeat (z :: lambda) (z0 :: mu) n).
      + assumption.
      + simpl in IHn.
        destruct (Z_le_lt_eq_dec _ _ IHn) as [H2|H2].
        * pose (H3 := H2).
          rewrite <- Z.ltb_lt in H3.
          rewrite H3.
          simpl.
          omega.
        * rewrite <- H2.
          rewrite (Z.ltb_irrefl z).
          simpl.
          omega.
  Qed.
  Theorem thm_A_get_repeat_nil :
    forall lambda n, tmp_A_get_repeat lambda nil n = nil.
  Proof.
    induction n.
    - simpl ; trivial.
    - simpl. rewrite IHn.
      destruct lambda ; simpl ; firstorder.
  Qed.
  Theorem thm_A_get_repeat_leb :
    forall n lambda mu,
      Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb lambda (tmp_A_get_repeat lambda mu n) = true.
  Proof.
    induction n.
    - simpl ; trivial.
    - intros lambda mu H.
      simpl.
      refine (thm_A_pred_leb2 _ _ _).
      exact (IHn _ _ H).
  Qed.
  Theorem thm_A_get_leb :
    forall lambda,
      Zvec_nondecb lambda = true
      -> Zvec_short_allb Z.leb lambda (tmp_A_get lambda) = true.
  Proof.
    unfold Zvec_nondecb, tmp_A_get.
    intros lambda H.
    destruct lambda as [|a lambda].
    - simpl ; trivial.
    - simpl tl in H.
      pose (H0 := thm_Zvec_nondecb_cons a lambda H).
      simpl tl.
      refine (thm_A_get_repeat_leb _ _ _ _).
      refine (thm_Zvec_leb_trans32 _ _ _ _ H H0).
      destruct lambda ; simpl ; omega.
  Qed.
  Theorem thm_A_get_repeat_length0 :
    forall lambda mu n,
      length mu <= length lambda
      -> length (tmp_A_get_repeat lambda mu n) <= length lambda.
  Proof.
    intros lambda mu n H.
    induction n.
    - simpl ; trivial.
    - simpl.
      pose (H0 := thm_A_pred_length0 lambda (tmp_A_get_repeat lambda mu n)).
      exact (le_trans _ _ _ H0 IHn).
  Qed.
  Theorem thm_A_get_repeat_length1 :
    forall lambda mu n,
      length mu <= length lambda
      -> length (tmp_A_get_repeat lambda mu n) = length mu.
  Proof.
    intros lambda mu n H.
    induction n.
    - simpl ; trivial.
    - simpl.
      pose (H0 := thm_A_pred_length1 lambda (tmp_A_get_repeat lambda mu n)).
      rewrite IHn in H0.
      firstorder.
  Qed.
  Theorem thm_A_get_total :
    forall lambda,
      (lie_is_radical_revwt_type lie_A_type lambda) = true
      -> (Zvec_total (tmp_A_get lambda) = 0)%Z.
  Proof.
    intros lambda Hrad.
    destruct lambda as [|a [|b lambda2]] ; simpl ; trivial.    
    unfold lie_is_radical_revwt_type in Hrad.
    simpl_destruct Hrad as [Hinc Htot].
    unfold tmp_A_get, tl.
    assert (Zvec_total lambda2 >= 0)%Z.
    {
      pose (H := thm_Zvec_nondecb_total_app (a::b::nil) lambda2).
      unfold app in H.
      firstorder.
    }
    set (n := Z.abs_nat (Zvec_total lambda2)).
    assert (Z.of_nat n = Zvec_total lambda2)%Z as H0.
    {
      unfold n.
      rewrite (Zabs2Nat.id_abs (Zvec_total lambda2)).
      rewrite Z.ge_le_iff in H.
      exact (Z.abs_eq _ H).
    }
    assert (forall m,
              Z.of_nat m <= Zvec_total lambda2
              -> Zvec_total (tmp_A_get_repeat (a :: b :: lambda2) lambda2 m)
                 = Zvec_total lambda2 - Z.of_nat m)%Z as H1.
    {
      set (lambda := (a::b::lambda2)).
      induction m.
      - simpl ; firstorder.
      - intros H1.
        rewrite thm_Z_of_nat_S in H1.
        assert (Z.of_nat m <= Zvec_total lambda2)%Z as Htmp.
        { omega. }
        pose (H2 := IHm Htmp). clearbody H2. clear Htmp IHm.
        cut (Zvec_total (tmp_A_get_repeat lambda lambda2 (S m))
             = Zvec_total (tmp_A_get_repeat lambda lambda2 m) - 1)%Z.
        {
          intros H4.
          rewrite H4.
          rewrite thm_Z_of_nat_S.
          omega.
        }
        assert (Zvec_short_allb
                  Z.leb lambda (tmp_A_get_repeat lambda lambda2 m) = true) as H3.
        {
          exact (thm_A_get_repeat_leb m lambda lambda2
                               (thm_Zvec_nondecb_fact3 a b lambda2 Hinc)).
        }
        assert (length (tmp_A_get_repeat lambda lambda2 m) <= length lambda) as H4.
        {
          assert (length lambda2 <= length lambda) as H5.
          { simpl. firstorder. }
          exact (thm_A_get_repeat_length0 lambda lambda2 m H5).
        }
        refine (thm_A_pred_tot lambda (tmp_A_get_repeat lambda lambda2 m) H3 H4 _).
        rewrite <- not_true_iff_false.
        intros H5.
        pose (H6 := thm_A_leb_eqb_tot lambda (tmp_A_get_repeat lambda lambda2 m) H4 H3).
        rewrite H6 in H5.
        rewrite H2 in H5.
        pose (H7 := thm_A_nondec_total_short_map
                      lambda (tmp_A_get_repeat lambda lambda2 m) Hinc Htot).
        rewrite <- H5 in H7.
        omega.
    }
    pose (H2 := H1 n).
    rewrite H0 in H2.
    firstorder.
  Qed.
  Theorem thm_A_get_length :
    forall lambda,
      length (tmp_A_get lambda) = length lambda - 2.
  Proof.
    destruct lambda as [|a [|b lambda2]] ; simpl ; firstorder.
    unfold tmp_A_get, tl.
    rewrite Nat.sub_0_r.
    refine (thm_A_get_repeat_length1 (a::b::lambda2) lambda2 _ _).
    simpl.
    firstorder.
  Qed.
  Theorem thm_A_get_repeat_S :
    forall lambda mu m,
      tmp_A_get_repeat lambda mu (S m)
      = tmp_A_pred lambda (tmp_A_get_repeat lambda mu m).
  Proof.
    trivial.
  Qed.
  Theorem thm_A_pred_nondecb :
    forall lambda mu,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb mu = true
      -> Zvec_nondecb (tmp_A_pred lambda mu) = true.
  Proof.
    intros lambda.
    induction lambda as [|x lambda].
    - trivial.
    - destruct mu as [|z mu].
      + simpl. trivial.
      + simpl.
        destruct_bool (x <? z)%Z Hxz.
        {
          intros _.
          destruct mu as [|z0 [|z1 mu]] ; unfold Zvec_nondecb ; simpl_extra.
          - trivial.
          - omega.
          - intros Hzz.
            destruct Hzz as [Hzz0 Hzz].
            split.
            + omega.
            + assumption.
        }
        {
          intros Hlambda Hmu.
          pose (Hlambda0 := thm_Zvec_nondecb_cons _ _ Hlambda).
          pose (Hmu0 := thm_Zvec_nondecb_cons _ _ Hmu).
          generalize (IHlambda mu Hlambda0 Hmu0).
          destruct lambda as [|x0 lambda].
          - trivial.
          - destruct mu as [|z0 mu].
            + trivial.
            + simpl.
              destruct (Sumbool.sumbool_of_bool (x0 <? z0)%Z) as [Hx0z0|Hx0z0] ;
                rewrite Hx0z0.
              {
                refine (thm_Zvec_nondecb_join2 _ _ _ _).
                pose (Hxx0 := thm_Zvec_nondecb_01_geq _ _ _ Hlambda).
                rewrite <- Zlt_is_lt_bool in Hx0z0.
                rewrite Z.ltb_ge in Hxz.
                omega.
              }
              {
                refine (thm_Zvec_nondecb_join2 _ _ _ _).
                exact (thm_Zvec_nondecb_01_geq _ _ _ Hmu).
              }
        }
  Qed.
  Theorem thm_A_get_nondecb :
    forall lambda,
      Zvec_nondecb lambda = true
      -> Zvec_nondecb (tmp_A_get lambda) = true.
  Proof.
    destruct lambda as [|a [|b lambda2]].
    - firstorder.
    - firstorder.
    - unfold tmp_A_get, tl.
      set (n := Z.abs_nat (Zvec_total lambda2)).
      intros H.
      generalize n as p.
      induction p.
      + simpl.
        exact (thm_Zvec_nondecb_cons _ _ (thm_Zvec_nondecb_cons _ _ H)).
      + rewrite thm_A_get_repeat_S.
        refine (thm_A_pred_nondecb _ _ H IHp).
  Qed.
  Theorem thm_An_branching_fact1 :
    forall lambda,
      lie_is_radical_revwt_type lie_A_type lambda = true
      -> length lambda >= 2
      -> Is_known_w0_branching_A_revwt lambda (tmp_A_get lambda).
  Proof.
    intros lambda Hrad Hlength.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b, tl.
    rewrite thm_A_get_length.
    destruct lambda as [|a [|b lambda]] ; simpl in Hlength ; try omega.
    autorewrite with rewritesome.
    firstorder.
    - simpl ; rewrite Nat.sub_0_r ; trivial.
    - simpl_extra.
      firstorder.
      + refine (thm_A_get_nondecb _ _).
        unfold lie_is_radical_revwt_type in Hrad.
        autorewrite with rewritesome in Hrad.
        firstorder.
      + refine (thm_A_get_total _ Hrad).
    - refine (thm_A_get_leb (a::b::lambda) _).
      unfold lie_is_radical_revwt_type in Hrad.
      autorewrite with rewritesome in Hrad.
      firstorder.
    - unfold tmp_A_get, tl.
      set (n := Z.abs_nat (Zvec_total lambda)).
      generalize n as n0.
      induction n0.
      + apply thm_Zvec_leb_refl.
      + rewrite thm_A_get_repeat_S.
        refine (thm_Zvec_leb_trans12 _ _ _ _ _ IHn0).
        * exact (thm_A_pred_length0 _ _).
        * exact (thm_A_pred_leb _ _).
  Qed.
  Theorem thm_A_radical_mrev :
    forall lambda,
      lie_is_radical_revwt_type lie_A_type lambda = true
      -> lie_is_radical_revwt_type
           lie_A_type (rev (map Z.opp lambda)) = true.
  Proof.
    unfold lie_is_radical_revwt_type.
    intros lambda.
    autorewrite with rewritesome.
    firstorder.
    - apply thm_Zvec_nondecb_mrev. assumption.
    - rewrite thm_Zvec_total_mrev. omega.
  Qed.
  Theorem thm_An_branching_fact2 :
    forall lambda mu,
      Is_known_w0_branching_A_revwt lambda mu
      -> Is_known_w0_branching_A_revwt
           (rev (map (Z.opp) lambda))
           (rev (map (Z.opp) mu)).
  Proof.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b.
    intros lambda mu.
    autorewrite with rewritesome.
    firstorder.
    - tac_length.
    - apply thm_A_radical_mrev. assumption.
    - apply thm_A_radical_mrev. assumption.
    - apply thm_Zvec_leb_mrev1. assumption. assumption.
    - apply thm_Zvec_leb_mrev2. assumption. assumption.
  Qed.
  Theorem thm_repeat_map :
    forall {A B} (f : A -> B) a n, map f (repeat a n) = repeat (f a) n.
  Proof.
    induction n.
    - trivial.
    - simpl.
      rewrite IHn.
      trivial.
  Qed.
  Theorem thm_repeat_plus :
    forall {A} (a : A) p q,
      repeat a (p + q) = repeat a p ++ repeat a q.
  Proof.
    intros.
    induction p.
    - trivial.
    - simpl.
      rewrite IHp.
      trivial.
  Qed.
  Theorem thm_Zvec_mul_0 :
    forall l, Zvec_mul 0%Z l = repeat 0%Z (length l).
  Proof.
    induction l.
    - trivial.
    - simpl ; rewrite IHl ; firstorder.
  Qed.
  Theorem thm_A_zero_exceptional :
    forall g,
      lie_algebra_type g = lie_A_type
      -> Is_exceptional_revwt_alg g (repeat 0%Z (lie_embedding_dim g)).
  Proof.
    intros g Hgtype.
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    exists 1, 0%Z.
    unfold is_exceptional_multiplier, lie_radical_fundamental_revwt_alg.
    simpl.
    rewrite thm_Zvec_mul_0.
    destruct (n <? 1) ;
      simpl_length ; firstorder.
    assert (n - 0 + 1 = 1 + n) as H0.
    { omega. }
    rewrite H0.
    simpl.
    trivial.
  Qed.
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
  Theorem thm_gcd_pos :
    forall m n, (m >= 0 -> n > 0 -> Z.gcd m n > 0)%Z.
  Proof.
    intros.
    destruct m ; destruct n.
    all : simpl.
    all : try apply Zgt_pos_0.
    trivial.
  Qed.
  Theorem thm_gcd_nat1 :
    forall i n, (Z.gcd (Z.of_nat i) (1 + Z.of_nat n) > 0)%Z.
  Proof.
    intros.
    apply thm_gcd_pos ; omega.
  Qed.
  Theorem thm_A_exceptional_twoval :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           Is_exceptional_revwt_alg g lambda
           -> exists a b p q,
                (a <= b)%Z /\ lambda = repeat a p ++ repeat b q.
  Proof.
    intros g Hgtype lambda [i [m [H H0]]].
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    unfold lie_radical_fundamental_revwt_alg, lie_rank, lie_embedding_dim in H0.
    unfold Zvec_mul in H0.
    destruct ((i =? 0) || (n <? i)).
    - rewrite thm_repeat_map, Zmult_0_r in H0.
      rewrite H0.
      autorewrite with rewritelength.
      rewrite thm_repeat_plus.
      exists 0%Z, 0%Z, 1, n.
      pose (H1 := Z.le_refl 0%Z).
      firstorder.
    - rewrite map_app, thm_repeat_map, thm_repeat_map in H0.
      set (a := (m * _)%Z) in H0.
      set (b := (m * _)%Z) in H0.
      set (p := S n - i) in H0.
      set (q := i) in H0.
      exists a, b, p, q.
      split.
      + unfold a, b.
        pose (H0m := thm_exceptional_multiplier_nonneg _ _ _ H).
        refine (Zmult_le_compat_l _ _ _ _ H0m).
        refine (Z_div_le _ _ _ (thm_gcd_nat1 i n) _).
        refine (Z.le_trans _ 0%Z _ _ _) ; omega.
      + assumption.
  Qed.
  Theorem thm_A_exceptional_total :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           Is_exceptional_revwt_alg g lambda
           -> Zvec_total lambda = 0%Z.
  Proof.
    intros g Hgtype lambda [i [m [H H0]]].
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    rewrite H0.
    rewrite thm_Zvec_total_mul.
    unfold lie_radical_fundamental_revwt_alg, lie_embedding_dim, lie_rank.
    destruct_bool (n <? i) Hni.
    - rewrite orb_true_r.
      simpl.
      rewrite thm_Zvec_total_repeat, Zmult_0_r, Zmult_0_r.
      trivial.
    - destruct_bool (i =? 0) Hi.
      + rewrite orb_true_l.
        simpl.
        rewrite thm_Zvec_total_repeat, Zmult_0_r, Zmult_0_r.
        trivial.
      + assert (forall x y : list Z, (if false || false then x else y) = y) as H1.
        { trivial. }
        rewrite H1.
        rewrite thm_Zvec_total_app.
        rewrite thm_Zvec_total_repeat.
        rewrite thm_Zvec_total_repeat.
        rewrite Nat.ltb_ge in Hni.
        assert (i <= S n) as H2.
        { omega. }
        rewrite (Nat2Z.inj_sub (S n) i H2).
        rewrite thm_Z_of_nat_S.
        pose (Hd := thm_gcd_nat1 i n).
        set (d := Z.gcd (Z.of_nat i) (1 + Z.of_nat n)) in *.
        assert (d <> 0%Z) as Hdneq.
        { clear -Hd. omega. }
        assert (d | Z.of_nat i)%Z as [i_d Hid].
        { apply Z.gcd_divide_l. }
        assert (d | 1 + Z.of_nat n)%Z as [Sn_d HSnd].
        { apply Z.gcd_divide_r. }
        rewrite Hid, HSnd, <- Z.mul_sub_distr_r, Zopp_mult_distr_l.
        rewrite (Z.div_mul _ _ Hdneq), (Z.div_mul _ _ Hdneq).
        rewrite Z.mul_sub_distr_r, Z.mul_sub_distr_r, Z.mul_sub_distr_l.
        rewrite Z.add_sub_assoc.
        rewrite <- Zopp_mult_distr_r, <- Zopp_mult_distr_r.
        rewrite Z.mul_shuffle0, (Z.mul_comm Sn_d), Z.mul_shuffle0.
        assert (forall m n, n = 0 -> (m * n = 0))%Z as H3.
        { intros m0 n0 H7. rewrite H7, Zmult_0_r. trivial. }
        apply H3.
        omega.
  Qed.
  Theorem thm_A_exceptional_radical :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           Is_exceptional_revwt_alg g lambda
           -> lie_is_radical_revwt_type lie_A_type lambda = true.
  Proof.
    intros g Hgtype lambda Hexc.
    destruct (thm_A_exceptional_twoval g Hgtype lambda Hexc)
      as [a [b [p [q [Hab Hlambda]]]]].
    pose (Htot := thm_A_exceptional_total g Hgtype lambda Hexc).
    unfold lie_is_radical_revwt_type.
    rewrite Htot.
    rewrite Hlambda.
    autorewrite with rewritesome.
    rewrite thm_Zvec_nondecb_app_iff.
    repeat try split.
    - exact (thm_Zvec_nondecb_repeat a p).
    - exact (thm_Zvec_nondecb_repeat b q).
    - destruct q ; simpl ; trivial.
      rewrite thm_last_repeat.
      destruct (p =? 0) ; omega.
  Qed.
  Theorem thm_mul_nonpos_cancel_l :
    forall n m : Z, (0 < n)%Z -> (n * m <= 0)%Z <-> (m <= 0)%Z.
  Proof.
    intros.
    rewrite Z.opp_le_mono, <- Z.mul_opp_r.
    simpl.
    rewrite (Z.mul_nonneg_cancel_l _ _ H).
    omega.
  Qed.
  Theorem thm_repeat_mul_0 :
    forall a p, (Z.of_nat p * a = 0 -> repeat a p = repeat 0 p)%Z.
  Proof.
    intros a p H.
    rewrite Z.eq_mul_0 in H.
    destruct H as [H|H].
    - assert (p = 0) as H0.
      { omega. }
      rewrite H0.
      simpl.
      trivial.
    - rewrite H.
      trivial.
  Qed.
  Theorem thm_0_eq_Z_of_nat :
    forall n, 0%Z = Z.of_nat n <-> 0 = n.
  Proof.
    firstorder ; omega.
  Qed.
  Theorem thm_0_lt_Z_of_nat :
    forall n, (0 < Z.of_nat n)%Z <-> 0 < n.
  Proof.
    firstorder ; omega.
  Qed.
  Theorem thm_A_exceptional_structure :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           Is_exceptional_revwt_alg g lambda
           -> lambda = repeat 0%Z (length lambda)
              \/ (exists a b p q,
                    a < 0
                    /\ 0 < b
                    /\ (0 < p)%nat
                    /\ (0 < q)%nat
                    /\ Z.of_nat q * b = - (Z.of_nat p * a)
                    /\ lambda = repeat a p ++ repeat b q)%Z.
  Proof.
    intros g Hgtype lambda Hexc.
    destruct (thm_A_exceptional_twoval g Hgtype lambda Hexc)
      as [a [b [p [q [Hab Hlambda]]]]].
    pose (Htot := thm_A_exceptional_total g Hgtype lambda Hexc).
    rewrite Hlambda, thm_Zvec_total_app,
      thm_Zvec_total_repeat, thm_Zvec_total_repeat in Htot.
    assert (0 <= Z.of_nat p)%Z as Hp.
    { clear. omega. }
    assert (0 <= Z.of_nat q)%Z as Hq.
    { clear. omega. }
    pose (Hpapb := Zmult_le_compat_l a b (Z.of_nat p) Hab Hp).
    pose (Hqaqb := Zmult_le_compat_l a b (Z.of_nat q) Hab Hq).
    pose (Ha := Zplus_le_compat_l _ _ (Z.of_nat p * a) Hqaqb).
    pose (Hb := Zplus_le_compat_r _ _ (Z.of_nat q * b) Hpapb).
    rewrite Htot, <- Z.mul_add_distr_r in Ha, Hb.
    assert (
        ((a < 0)%Z /\ (0 < b)%Z /\ 0 < p /\ 0 < q)
        \/ (lambda = repeat 0 (p + q))%Z) as H.
    {
      destruct (Z_le_lt_eq_dec _ _ Hp) as [H0ltp|H0].
      destruct (Z_le_lt_eq_dec _ _ Hq) as [H0ltq|H0].
      all : try (rewrite thm_0_eq_Z_of_nat in H0 ;
                 rewrite <- H0 in * ;
                 right ;
                 simpl in * ;
                 try rewrite Nat.add_0_r, Z.add_0_r, app_nil_r in *).
      all : try (rewrite (thm_repeat_mul_0 _ _ Htot) in Hlambda ; assumption).
      assert (0 < Z.of_nat p + Z.of_nat q)%Z as H0ltpq.
      { clear -H0ltp H0ltq. omega. }
      rewrite (thm_mul_nonpos_cancel_l  _ a H0ltpq) in Ha.
      rewrite (Z.mul_nonneg_cancel_l _ b H0ltpq) in Hb.
      destruct (Z_le_lt_eq_dec _ _ Ha) as [Halt0|Ha0].
      destruct (Z_le_lt_eq_dec _ _ Hb) as [H0ltb|H0b].
      rewrite thm_0_lt_Z_of_nat in *.
      left ; repeat (try split ; try assumption).
      all : try rewrite <- H0b in *.
      all : try rewrite Ha0 in *.
      all : rewrite Z.mul_0_r in Htot.
      all : try rewrite Z.add_0_l in Htot.
      all : try rewrite Z.add_0_r in Htot.
      all : rewrite (thm_repeat_mul_0 _ _ Htot), <- thm_repeat_plus in Hlambda.
      all : right ; assumption.
    }
    destruct H as [[H1 [H2 [H3 H4]]]|H].
    - right.
      exists a, b, p, q.
      repeat try split ; try assumption.
      clear -Htot. omega.
    - left.
      rewrite H.
      autorewrite with rewritelength.
      trivial.
  Qed.
  Definition twovalA (a b : Z) (p q : nat) :=
    repeat a p ++ repeat b q.
  Theorem thm_Zvec_leb_leb_eq :
    forall lambda mu,
      length lambda = length mu
      -> Zvec_short_allb Z.leb lambda mu = true
      -> Zvec_short_allb Z.leb mu lambda = true
      -> lambda = mu.
  Proof.
    induction lambda.
    - destruct mu.
      + trivial.
      + simpl ; intros H ; discriminate H.
    - destruct mu.
      + simpl ; intros H ; discriminate H.
      + simpl_extra.
        firstorder.
  Qed.
  Theorem thm_Zvec_leb_nth :
    forall n lambda mu a b,
      n < length lambda
      -> n < length mu
      -> Zvec_short_allb Z.leb lambda mu = true
      -> (nth n lambda a <= nth n mu b)%Z.
  Proof.
    induction n.
    all : destruct lambda, mu ; simpl in * ; firstorder ; try omega.
    all : autorewrite with rewritesome in *.
    all : try (apply IHn ; try omega).
    all : firstorder.
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
  Theorem thm_twovalA_ntha :
    forall a b p q k lambda,
      2 <= k
      -> k < p
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> nth k lambda a = a.
  Proof.
    intros a b p q k lambda Hk H H0.
    destruct k as [|[|k]] ; simpl; try omega.
    unfold Is_known_w0_branching_A_revwt,
      radical_branching_A_two_revwt_b, lie_is_radical_revwt_type in H0.
    autorewrite with rewritesome in H0.
    firstorder.
    destruct lambda as [|l0 [|l1 lambda]] ; simpl; trivial.
    destruct p as [|[|p]] ; simpl; try (clear -H ; omega).
    unfold twovalA in H1.
    simpl tl in H1.
    assert (S (S p) = p + 2) as H7.
    { omega. }
    rewrite H7, thm_repeat_plus, <- app_assoc in H1.
    simpl_extra in H2.
    firstorder.
    simpl in H0.
    autorewrite with rewritelength rewritesome in H0.
    generalize H1, H9.
    rewrite (thm_hdn_tln Z p lambda) ; [| clear -H0 ; omega].
    set (lam1 := hdn p lambda).
    set (lam2 := tln p lambda).
    assert (length lam1 = length (repeat a p)) as H14.
    {
      unfold lam1.
      autorewrite with rewritelength.
      clear -H0.
      simpl_length in H0.
      apply min_l.
      omega.
    }
    rewrite thm_Zvec_leb_app, thm_Zvec_leb_app ; firstorder.
    rewrite (thm_Zvec_leb_leb_eq _ _ H14 H11 H10).
    rewrite app_nth1.
    - generalize k, p, a.
      induction k0 ; destruct p0 ; simpl ; trivial.
    - autorewrite with rewritelength.
      apply lt_S_n, lt_S_n in H.
      assumption.
  Qed.
  (*Revise the proof of thm_twovalA_ntha to look more like thm_twovalA_nthb.*)
  Theorem thm_twovalA_nthb :
    forall a b p q k lambda,
      2 + p <= k
      -> k < p + q
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> nth k lambda b = b.
  Proof.
    unfold twovalA.
    intros.
    unfold Is_known_w0_branching_A_revwt,
      radical_branching_A_two_revwt_b, lie_is_radical_revwt_type in *.
    autorewrite with rewritesome in *.
    firstorder.
    assert (k - 2 < length (repeat a p ++ repeat b q)
            /\ k - 2 < length (tl (tl lambda))
            /\ k < length lambda
            /\ k < length (repeat a p ++ repeat b q))
      as [H8 [H9 [H10 H11]]].
    { autorewrite with rewritelength in *. omega. }
    pose (Hlower := thm_Zvec_leb_nth (k - 2) _ _ b b H8 H9 H2).
    pose (Hupper := thm_Zvec_leb_nth k _ _ b b H10 H11 H3).
    rewrite thm_nth_tl_tl, thm_nth_app_repeat in *.
    exact (Z.le_antisymm _ _ Hupper Hlower).
    all : clear -H H0 ; omega.
  Qed.

  Theorem thm_twovalA_branching : (*Probably useless*)
    forall lambda a b p q,
      2 <= p
      -> 2 <= q
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> exists l0 l1 l2 l3 l4 l5,
           lambda = l0::l1::(repeat a (p - 2))
                      ++ l2::l3::(repeat b (q - 2))
                      ++ l4::l5::nil.
  Proof.
    intros lambda a b p q Hp Hq H.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b in H.
    autorewrite with rewritesome in H.
    destruct H as [[[[Hlength Hradl] Hradm] Hlm] Hml].
    unfold twovalA in Hlength.
    autorewrite with rewritelength in Hlength.
    assert (length lambda >= 6) as Hlength2.
    {
      rewrite Hlength.
      clear - Hp Hq Hlength. omega.
    }
    destruct lambda as [|l0 [|l1 lambda]] ; simpl in Hlength2 ; try omega.
    autorewrite with rewritelength rewritesome in Hlength.
    exists l0, l1.
    unfold twovalA in Hlm, Hml.
    assert (p = 2 + (p - 2)) as Hp2.
    { clear -Hp. omega. }
    assert (p = (p - 2) + 2) as Hp3.
    { clear -Hp. omega. }
    rewrite Hp2 in Hlm.
    rewrite Hp3 in Hml.
    rewrite thm_repeat_plus in Hlm, Hml.
    rewrite <- app_assoc in Hml.
    simpl_destruct Hlm as [_ [_ Hlm]].
    assert ((p - 2) <= length lambda) as Hp4.
    { clear -Hq Hlength. omega. }
    pose (Hlsplit := thm_hdn_tln _ _ _ Hp4).
    set (mu := hdn _ _) in *.
    set (nu := tln _ _) in *.
    rewrite Hlsplit in *.
    assert (length mu = length (repeat a (p - 2))) as Hmulength.
    {
      unfold mu.
      autorewrite with rewritelength.
      exact (Min.min_l _ _ Hp4).
    }
    rewrite (thm_Zvec_leb_app _ _ _ _ Hmulength) in Hlm.
    destruct Hlm as [Hlm1 Hlm2].
    simpl in Hml.
    rewrite (thm_Zvec_leb_app _ _ _ _ (eq_sym Hmulength)) in Hml.
    destruct Hml as [Hml1 Hml2].
    pose (Hmu := thm_Zvec_leb_leb_eq _ _ Hmulength Hlm1 Hml1).
    clearbody Hmu.
    rewrite Hmu in *.
    simpl_length in Hlength.
    clearbody nu.
    clear Hlm1 Hml1 Hmulength mu Hmu Hp4 Hlsplit lambda.
    assert (length nu >= 2) as Hnu2.
    { omega. }
    destruct nu as [|l2 [|l3 nu]] ; simpl in Hnu2 ; try omega.
    clear Hnu2.
    exists l2, l3.
    assert (q = 2 + (q - 2)) as Hq2.
    { clear -Hq. omega. }
    assert (q = (q - 2) + 2) as Hq3.
    { clear -Hq. omega. }
    rewrite Hq2 in Hlm2.
    rewrite Hq3 in Hml2.
    rewrite thm_repeat_plus in Hlm2, Hml2.
    simpl_destruct Hlm2 as [_ [_ Hlm2]].
    simpl_destruct Hml2 as [_ [_ Hml2]].
    simpl in Hlength.
    assert (q - 2 <= length nu) as Hq4.
    { clear - Hp Hq Hlength. omega. }
    pose (Hnsplit := thm_hdn_tln _ _ _ Hq4).
    set (rho := hdn _ _) in *.
    set (sigma := tln _ _) in *.
    rewrite Hnsplit in *.
    assert (length rho = length (repeat b (q - 2))) as Hrholength.
    {
      unfold rho.
      autorewrite with rewritelength.
      exact (Min.min_l _ _ Hq4).
    }
    rewrite (app_nil_end (repeat b (q - 2))) in Hlm2.
    rewrite (thm_Zvec_leb_app _ _ _ _ Hrholength) in Hlm2.
    destruct Hlm2 as [Hlm1 Hlm2].
    rewrite (thm_Zvec_leb_app _ _ _ _ (eq_sym Hrholength)) in Hml2.
    destruct Hml2 as [Hml1 Hml2].
    pose (Hrho := thm_Zvec_leb_leb_eq _ _ Hrholength Hlm1 Hml1).
    clearbody Hrho.
    rewrite Hrho in *.
    simpl_length in Hlength.
    simpl_length in Hlength2.
    clearbody sigma.
    clear Hlm1 Hml1 Hrholength rho Hrho Hq4 Hnsplit nu.
    assert (length sigma = 2) as Hsigma2.
    { clear - Hp Hq Hlength. omega. }
    destruct sigma as [|l4 [|l5 [|l6 sigma]]] ;
      simpl in Hsigma2 ; try (clear -Hsigma2; omega).
    exists l4, l5.
    trivial.
  Qed.

  (*duA stands for "down-up for A-type reversed weights"
    namely starting from repeat a p ++ repeat b q with a<=b,
    decrement one entry and increment another one,
    to keep total = 0, namely keep a (radical) weight.
    Various indices correspond to which entry is increased:
    1 means an entry in repeat a p, 2 in repeat b q.
    If there are not enough entries do nothing.*)
  Definition d1u1A (a b : Z) (p q : nat) :=
    match p with
      | 0 => twovalA a b p q
      | 1 => twovalA a b p q
      | S (S p'') => (a-1)%Z::(repeat a p'') ++ (a+1)%Z::(repeat b q)
    end.
  Definition d1u2A (a b : Z) (p q : nat) :=
    match p with
      | 0 => twovalA a b p q
      | S p' => match q with
                  | 0 => twovalA a b p q
                  | S q' => (a-1)%Z::(repeat a p')
                                 ++ (repeat b q') ++ (b+1)%Z::nil
                end
    end.
  Definition d2u1A (a b : Z) (p q : nat) :=
    match p with
      | 0 => twovalA a b p q
      | S p' => match q with
                  | 0 => twovalA a b p q
                  | S q' => (repeat a p')
                              ++ (a+1)%Z::(b-1)%Z::(repeat b q')
                end
    end.
  Definition d2u2A (a b : Z) (p q : nat) :=
    match q with
      | 0 => twovalA a b p q
      | 1 => twovalA a b p q
      | S (S q'') => repeat a p ++ (b-1)%Z::(repeat b q'') ++ (b+1)%Z::nil
    end.
  Ltac tac_du_repeat :=
    repeat (simpl ;
            match goal with
              | [ |- _ /\ _] => split
              | [ |- Zvec_nondecb (_::_) = true]
                => refine (thm_Zvec_nondecb_join _ _ _ _)
              | [ |- Zvec_nondecb (_++_) = true]
                => rewrite thm_Zvec_nondecb_app_iff
              | [ |- Zvec_nondecb (repeat _ _) = true]
                => (rewrite thm_Zvec_nondecb_repeat ; trivial)
              | [ |- context[hd _ (repeat _ _)]]
                => try rewrite thm_hd_repeat
              | [ |- context[hd _ (_++_)]]
                => try rewrite thm_hd_app
              | [ |- context[last (repeat _ _)]]
                => try rewrite thm_last_repeat
              | [ |- context[if ?p=?0 then _ else _]]
                => (destruct p ; simpl ; firstorder) (*Possibly dangerous loop?*)
              | [ |- context[match ?p with 0 => _ | S _ => _ end]]
                => (destruct p ; simpl ; firstorder)
              | [ Htot : context[Zvec_total] |- context[Zvec_total]]
                => (simpl_total ; simpl_total in Htot ; try omega)
              | [ |- _] => (simpl ; try omega ; firstorder)
            end).
  Ltac tac_du fn :=
    unfold lie_is_radical_revwt_type ;
    intros a b p q ;
    autorewrite with rewritesome ;
    intros Ha Hb [Hinc Htot] ;
    unfold fn, twovalA in * ;
    tac_du_repeat.
  Theorem thm_d1u1A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (twovalA a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d1u1A a b p q) = true.
  Proof.
    tac_du d1u1A.
  Qed.
  Theorem thm_d1u2A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (twovalA a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d1u2A a b p q) = true.
  Proof.
    tac_du d1u2A.
    destruct q ; simpl.
    all : tac_du_repeat.
  Qed.
  Theorem thm_d2u1A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (twovalA a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d2u1A a b p q) = true.
  Proof.
    tac_du d2u1A.
  Qed.
  Theorem thm_d2u2A_radical :
    forall a b p q,
      (a < 0)%Z
      -> (0 < b)%Z
      -> lie_is_radical_revwt_type lie_A_type (twovalA a b p q) = true
      -> lie_is_radical_revwt_type lie_A_type (d2u2A a b p q) = true.
  Proof.
    tac_du d2u2A.
  Qed.
  Theorem thm_Zvec_nondecb_nth :
    forall lambda p r a b,
      Zvec_nondecb lambda = true
      -> p < r
      -> r < length lambda
      -> (nth p lambda a <= nth r lambda b)%Z.
  Proof.
    intros.
    destruct (nth_split lambda b H1) as [l2 [l5 [H2 H5]]].
    rewrite H2 at 1.
    rewrite app_nth1 at 1.
    rewrite <- H5 in H0.
    destruct (nth_split l2 a H0) as [l3 [l4 [H3 H4]]].
    set (aa := nth p _ _) in *.
    set (bb := nth r _ _) in *.
    rewrite H2, H3, <- app_assoc in H.
    destruct (thm_Zvec_nondecb_app _ _ H) as [_ H6].
    simpl in H6.
    exact (thm_Zvec_nondecb_app_hd _ _ _ _ H6).
    omega.
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
  Theorem thm_d1u1A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (1 < p)%nat
      -> (0 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> Is_known_w0_branching_A_revwt lambda (d1u1A a b p q)
         \/ (nth 0 lambda a = a)
         \/ (nth (1 + p) lambda a = a).
  Proof.
    unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b in *.
    intros.
    autorewrite with rewritesome in *.
    assert (lie_is_radical_revwt_type lie_A_type (d1u1A a b p q) = true) as H4.
    { apply thm_d1u1A_radical ; firstorder ; omega. }
    rewrite H4.
    autorewrite with rewritesome.
    destruct p as [|[|p]] ; try omega.
    firstorder.
    unfold twovalA in *.
    assert (nth 0 lambda a <= a)%Z as H9.
    {
      clear -H6.
      destruct lambda.
      - simpl ; omega.
      - unfold Zvec_short_allb in H6.
        simpl in *.
        autorewrite with rewritesome in *.
        firstorder.
    }
    destruct (Z_le_lt_eq_dec _ _ H9) as [Hhda|Hhda] ; [|firstorder].
    assert (a <= nth (3 + p) lambda a)%Z as H10.
    {
      clear - H3 H5.
      destruct lambda as [|x0 [|x1 lambda]] ; simpl ; try omega.
      simpl tl in *.
      assert (S p < length (repeat a (S (S p)) ++ repeat b q)
              /\ S p < length lambda) as [H1 H2].
      {
        autorewrite with rewritelength in *.
        firstorder.
      }
      pose (H6 := thm_Zvec_leb_nth (S p) _ lambda a a H1 H2 H5).
      clearbody H6.
      rewrite app_nth1, thm_nth_repeat1 in H6.
      exact H6.
      autorewrite with rewritelength.
      firstorder.
    }
    simpl add in *.
    destruct (Z_le_lt_eq_dec _ _ H10) as [Hap|Hap] ; [|firstorder].
    left.
    unfold d1u1A.
    repeat try split.
    - clear -H3.
      autorewrite with rewritelength in *.
      omega.
    - assumption.
    - destruct lambda ; [trivial|].
      simpl_extra.
      split.
      + clear -Hhda.
        simpl in Hhda.
        omega.
      + rewrite thm_repeat_fact1 in H6.
        simpl_destruct H6 as [_ H6].
        refine (thm_Zvec_leb_trans32 _ _ _ _ H6 _).
        autorewrite with rewritelength ; omega.
        rewrite thm_Zvec_leb_app.
        split.
        * apply thm_Zvec_leb_refl.
        * simpl_extra.
          split.
          omega.
          apply thm_Zvec_leb_refl.
        * trivial.
    - destruct lambda as [|z [|z0 lambda]]; trivial.
      simpl in H10, Hap.
      simpl tl in *.
      assert (S p < length lambda) as Hl.
      {
        clear -H3.
        simpl_length in H3.
        omega.
      }
      destruct (nth_split lambda a Hl) as [l1 [l2 [H11 H12]]].
      rewrite H11.
      rewrite H11 in H5, H6, H3, H9, H8, Hl, H10, Hhda.
      rewrite app_comm_cons.
      rewrite thm_repeat_fact1 in H5, H7.
      rewrite thm_Zvec_leb_app in *.
      firstorder.
      all : try solve [clear -H3 H12 ; autorewrite with rewritelength in *; omega].
      + refine (thm_Zvec_leb_trans32 _ _ _ _ _ H5).
        clear -H3 H12 ; autorewrite with rewritelength in *; omega.
        simpl.
        rewrite thm_Zvec_leb_refl.
        simpl_extra.
        omega.
      + simpl_extra.
        split.
        * omega.
        * clear -H13.
          simpl_extra in H13.
          firstorder.
  Qed.
  Theorem thm_d1u2A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (0 < p)%nat
      -> (0 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> Is_known_w0_branching_A_revwt lambda (d1u2A a b p q)
         \/ (nth 0 lambda a = a)
         \/ (nth (1 + p + q) lambda b = b).
  Proof.
    admit.
  Admitted.
  Theorem thm_d2u1A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (0 < p)%nat
      -> (0 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> Is_known_w0_branching_A_revwt lambda (d2u1A a b p q)
         \/ (nth p lambda b = b)
         \/ (nth (1 + p) lambda a = a).
  Proof.
    admit.
  Admitted.
  Theorem thm_d2u2A :
    forall a b p q lambda,
      (a < 0)%Z
      -> (0 < b)%Z
      -> (0 < p)%nat
      -> (1 < q)%nat
      -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
      -> Is_known_w0_branching_A_revwt lambda (d2u2A a b p q)
         \/ (nth p lambda b = b)
         \/ (nth (1 + p + q) lambda b = b).
  Proof.
    admit.
  Admitted.

  Theorem thm_d1u1A_not_exceptional :
    forall a b p q g,
      lie_algebra_type g = lie_A_type
      -> 1 < p
      -> ~ (Is_exceptional_revwt_alg g (d1u1A a b p q)).
  Proof.
    admit.
  Admitted.
  (*TODO: also do d1u2 etc.*)

  Theorem thm_duA :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           lie_is_radical_revwt_alg g lambda = true
           -> forall a b p q,
                (a < 0)%Z
                -> (0 < b)%Z
                -> 0 < p
                -> 0 < q
                -> Is_known_w0_branching_A_revwt lambda (twovalA a b p q)
                -> (exists mu,
                      Is_known_w0_branching_A_revwt lambda mu
                      /\ ~ (Is_exceptional_revwt_alg g mu))
                   (* (Is_known_w0_branching_A_revwt lambda (d1u1A a b p q)
          /\ (2 <= p))
         \/ Is_known_w0_branching_A_revwt lambda (d1u2A a b p q)
         \/ Is_known_w0_branching_A_revwt lambda (d2u1A a b p q)
         \/ (Is_known_w0_branching_A_revwt lambda (d2u2A a b p q)
             /\ (2 <= q))*)
                   \/ (nth 0 lambda a = a /\ nth p lambda b = b)
                   \/ (nth (1 + p) lambda a = a /\ nth (1 + p + q) lambda b = b).
  Proof.
    admit.
  Admitted.
  Theorem thm_A_impossible_total: (*TODO: actually wrong: misses some cases*)
    forall a b p q lambda,
      lie_is_radical_revwt_type lie_A_type lambda = true
      -> (Z.of_nat p * a + Z.of_nat q * b = 0)%Z
      -> (nth 0 lambda a = a /\ nth p lambda b = b)
         \/ (nth (1 + p) lambda a = a /\ nth (1 + p + q) lambda b = b)
      -> False.
  Proof.
    admit.
  Admitted.

  Theorem thm_main_A :
    forall g,
      lie_algebra_type g = lie_A_type
      -> forall lambda,
           lie_is_radical_revwt_alg g lambda = true
           -> (Is_exceptional_revwt_alg g lambda)
              \/ (Is_mixed_revwt_alg g lambda).
  Proof.
    intros g Hgtype.
    destruct g as [[n Hn]| | | | | | | | ] ;
      try (simpl in Hgtype; discriminate Hgtype).
    generalize n, Hn. clear n Hn Hgtype.
    refine (nat_ind2 _ _ _ _).
    - intros Hn. contradiction (gt_irrefl 0 Hn).
    - intros Hn lambda.
      exact (thm_main_A1 _ lambda Hn (eq_refl _)).
    - intros n IHn Hn2 lambda.
      destruct n as [|[|n]].
      + exact (thm_main_A2 _ lambda Hn2 (eq_refl _)).
      + exact (thm_main_A3 _ lambda Hn2 (eq_refl _)).
      + intros Hrad.
        unfold lie_is_radical_revwt_alg in Hrad.
        autorewrite with rewritesome in Hrad.
        destruct Hrad as [Hlength Hrad].
        simpl in Hlength.
        assert (length lambda >= 2) as Hl2.
        { rewrite Hlength. omega. }
        assert (S (S n) > 0) as Hn.
        { firstorder. }
        pose (Hmu := thm_An_branching_fact1 _ Hrad Hl2).
        set (mu := tmp_A_get lambda) in Hmu.
        unfold Is_known_w0_branching_A_revwt, radical_branching_A_two_revwt_b in Hmu.
        autorewrite with rewritesome in Hmu.
        destruct Hmu as [[[[Hlenlm Hradl] Hradm] Hllebm] Hmlebtltl].
        pose (g := lie_A (exist (fun n : nat => n > 0) (S (S (S (S n)))) Hn2)).
        pose (h := lie_A (exist (fun n : nat => n > 0) (S (S n)) Hn)).
        assert (lie_is_radical_revwt_alg h mu = true) as Hradmg.
        {
          unfold lie_is_radical_revwt_alg.
          simpl.
          rewrite Hlenlm in Hlength.
          autorewrite with rewritesome in Hlength.
          simpl in Hradm.
          rewrite Hradm.
          autorewrite with rewritesome.
          trivial.
        }
        destruct (IHn Hn mu Hradmg) as [H|H].
        {
          (*mu is exceptional*)
          simpl in H.
          destruct H as [i [m [H Hmu]]].
          unfold is_exceptional_multiplier in H.
          admit.
        }
        admit.
  Admitted.

End theorems_for_A_type.

Theorem thm_main_B :
  forall g,
    lie_algebra_type g = lie_B_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_C :
  forall g,
    lie_algebra_type g = lie_C_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_D :
  forall g,
    lie_algebra_type g = lie_D_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_E6 :
  forall g,
    lie_algebra_type g = lie_E6_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_E7 :
  forall g,
    lie_algebra_type g = lie_E7_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_E8 :
  forall g,
    lie_algebra_type g = lie_E8_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_F4 :
  forall g,
    lie_algebra_type g = lie_F4_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.
Theorem thm_main_G2 :
  forall g,
    lie_algebra_type g = lie_G2_type
    -> forall lambda,
         lie_is_radical_revwt_alg g lambda = true
         -> (Is_exceptional_revwt_alg g lambda)
            \/ (Is_mixed_revwt_alg g lambda).
Admitted.


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
  - (*A-type Lie algebras*)
    simpl in Hlength.
    clearbody Hlength.
    destruct n as [|[|[|[|n]]]].
    + (*A_0*)
      omega.
    + (*A_1*)
      destruct lambda as [|a [|b [|]]] ; simpl in Hlength ; try omega.
      exact (thm_main_A1 _ _ _ (eq_refl _) Hrad).
    + (*A_2*)
      destruct lambda as [|a [|b [|c [|]]]] ; simpl in Hlength ; try omega.
      exact (thm_main_A2 _ _ _ (eq_refl _) Hrad).
    + (*A_3*)
      destruct lambda as [|a [|b [|c [|d [|]]]]] ; simpl in Hlength ; try omega.
      exact (thm_main_A3 _ _ _ (eq_refl _) Hrad).
    + (*A_n, n>=4*)
      refine (thm_main_A _ _ _ Hrad) ; firstorder.
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
