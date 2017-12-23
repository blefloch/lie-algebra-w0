Require Import Setoid.
Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Nat.
(*Load our files*)
Require Import Tools.
Require Import ListExtras.
Require Import Zvec.
Require Import SimpleLieAlgebras.
Open Scope nat_scope.

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
  (*Put together all known branchings preserving w0.*)
  (*No need to check ranks of g and h as it is done by the Is_known_... functions.*)
  Definition Is_known_w0_branching_revwt_alg g lambda h mu :=
    lie_is_radical_revwt_alg g lambda = true
    /\ lie_is_radical_revwt_alg h mu = true
    /\ match lie_algebra_type g, lie_algebra_type h with
         | lie_A_type, lie_A_type => Is_known_w0_branching_A_revwt lambda mu
         | lie_B_type, lie_B_type => Is_known_w0_branching_B_revwt lambda mu
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
