Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
Open Scope nat_scope.

Section list_helpers.
  Variable A : Type.
  Fixpoint constant_list (x : A) n :=
    match n with
      | 0 => nil
      | S n' => x::(constant_list x n')
    end.
  Definition basic_list (x : A) i (y : A) n :=
    if (1 <=? i) && (i <=? n)
    then (constant_list y (i - 1))++x::(constant_list y (n - i))
    else constant_list y n.
  Definition basic_list_rev (x : A) i (y : A) n :=
    if (1 <=? i) && (i <=? n)
    then (constant_list y (n - i))++x::(constant_list y (i - 1))
    else constant_list y n.
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
  Definition Zvec_mul_nat m := map (Z.mul (Z_of_nat' m)).
  Definition Zvec_short_sub := Zvec_short_map_zip Z.sub.
  Definition Zvec_short_max := Zvec_short_map_zip Z.max.
  Definition Zvec_long_min := Zvec_long_map_zip Z.min.
  Definition Zvec_nondecb lambda := Zvec_short_allb Z.leb lambda (tl lambda).
  Definition Zvec_nonincb lambda := Zvec_short_allb Z.leb (tl lambda) lambda.
  Definition Zvec_all_nonnegb := Zvec_allb (Z.leb 0).
End list_helpers.

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
    then constant_list _ 0%Z (lie_embedding_dim g)
    else
      match g with
        | lie_A (exist _ n _)
          => let d := Z_of_nat' (Nat.gcd i (S n)) in
             (constant_list _ (Z_of_nat' (S n - i) / d)%Z i)
               ++ (constant_list _ (- Z_of_nat' i / d)%Z (S n - i))
        | lie_B (exist _ n _)
          => (constant_list _ 1%Z i) ++ (constant_list _ 0%Z (n - i))
        | lie_C (exist _ n _)
          => (constant_list _ (if even i then 1%Z else 2%Z) i)
               ++ constant_list _ 0%Z (n - i)
        | lie_D (exist _ n _)
          => if i =? n-1
             then if even n
                  then (constant_list _ 1%Z (n - 1)) ++ (-1)%Z::nil
                  else (constant_list _ 2%Z (n - 1)) ++ (-2)%Z::nil
             else (constant_list _ (if even i then 1%Z else 2%Z) i)
                    ++ (constant_list _ 0%Z (n - i))
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
    then constant_list _ 0%Z (lie_embedding_dim g)
    else
      match g with
        | lie_A (exist _ n _)
          => let d := Z_of_nat' (Nat.gcd i (S n)) in
             (constant_list _ (- Z_of_nat' i / d)%Z (S n - i))
               ++ (constant_list _ (Z_of_nat' (S n - i) / d)%Z i)
        | lie_B (exist _ n _)
          => (constant_list _ 0%Z (n - i)) ++ (constant_list _ 1%Z i)
        | lie_C (exist _ n _)
          => (constant_list _ 0%Z (n - i))
               ++ (constant_list _ (if even i then 1%Z else 2%Z) i)
        | lie_D (exist _ n _)
          => if i =? n-1
             then if even n
                  then (-1)%Z::(constant_list _ 1%Z (n - 1))
                  else (-2)%Z::(constant_list _ 2%Z (n - 1))
             else (constant_list _ 0%Z (n - i))
                    ++ (constant_list _ (if even i then 1%Z else 2%Z) i)
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
    if m =? 0
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
                 || (i =? 2) && (m <=? 2)
                 || (m <=? 1)
          | lie_C (exist _ n _)
            => (n =? 2)
                 || (n =? 3) && (i =? 3) && (m <=? 1)
                 || (n =? 4) && (i =? 4) && (m <=? 2)
                 || (i =? 1)
                 || (i =? 2) && (m <=? 2)
                 || (even i) && (m <=? 1)
          | lie_D (exist _ n _)
            => (n =? 3)
                 || (n =? 4) && ((i =? 3) || (i =? 4))
                 || (i =? 1)
                 || (even n) && (((i =? 2) && (m <=? 2))
                                   || ((even i) && (m <=? 1))
                                   || ((1 + i =? n) && (m <=? 1)))
          | lie_E6
            => false
          | lie_E7
            => ((i =? 1) && (m <=? 2))
                 || ((i =? 6) && (m <=? 1))
                 || ((i =? 7) && (m <=? 1))
          | lie_E8
            => ((i =? 1) && (m <=? 1)) || ((i =? 8) && (m <=? 8))
          | lie_F4
            => ((i =? 1) || (i =? 4)) && (m <=? 2)
          | lie_G2
            => m <=? 2
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
    Is_true (radical_branching_A_two_revwt_b lambda mu).
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
      Is_true (known_radical_branching_B_one_revwt_b lambda mu)
      /\ Is_true (known_radical_branching_B_one_revwt_b mu nu).
  (*TODO: add more known branchings that preserve w0*)
  (*w0 of E8 coincides with w0 of D8*)
  (*Partial criterion for branching from E8 to D8.*)
  Definition Is_known_w0_branching_E8_D8_revwt (lambda mu : list Z) :=
    (lambda = mu)
      /\ Is_true (lie_is_radical_revwt_type lie_E8_type lambda)
      /\ Is_true (lie_is_radical_revwt_type lie_D_type mu).
  (*Put together all known branchings preserving w0.*)
  (*No need to check ranks of g and h as it is done by the Is_known_... functions.*)
  Definition Is_known_w0_branching_revwt_alg g lambda h mu :=
    Is_true (lie_is_radical_revwt_alg g lambda)
    /\ Is_true (lie_is_radical_revwt_alg h mu)
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
      (Is_true (is_exceptional_multiplier g i m))
      /\ lambda = Zvec_mul_nat m (lie_radical_fundamental_revwt_alg g i).
  Inductive Is_mixed_revwt_alg : lie_algebra -> list Z -> Prop :=
  | mixed_by_hand :
      forall g lambda,
        Is_true (is_mixed_by_hand_revwt_alg g lambda)
        -> Is_mixed_revwt_alg g lambda
  | mixed_by_ideal :
      forall g lambda mu,
        Is_mixed_revwt_alg g mu
        /\ Is_true (lie_is_dominant_revwt_alg g (Zvec_short_sub lambda mu))
        -> Is_mixed_revwt_alg g lambda
  | mixed_by_induction :
      forall g lambda h mu,
        Is_mixed_revwt_alg h mu
        /\ Is_known_w0_branching_revwt_alg g lambda h mu
        -> Is_mixed_revwt_alg g lambda.
End main.

Theorem main :
  forall g lambda,
    Is_true (lie_is_radical_revwt_alg g lambda)
    -> (Is_exceptional_revwt_alg g lambda) \/ (Is_mixed_revwt_alg g lambda).
