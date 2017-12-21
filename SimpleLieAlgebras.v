Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Load our files*)
Require Import Rewriting.
Require Import ListExtras.
Require Import Zvec.
Open Scope nat_scope.

Section helpers.
  Local Definition basic_list {A} (x : A) i (y : A) n :=
    if (1 <=? i) && (i <=? n)
    then (repeat y (i - 1))++x::(repeat y (n - i))
    else repeat y n.
  Local Definition basic_list_rev {A} (x : A) i (y : A) n :=
    if (1 <=? i) && (i <=? n)
    then (repeat y (n - i))++x::(repeat y (i - 1))
    else repeat y n.
End helpers.

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


Section thm.
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
End thm.