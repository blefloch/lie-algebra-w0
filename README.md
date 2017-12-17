# lie-algebra-w0

In the study of conjectures by Auslander and by Milnor on flat affine
manifolds, the following problem on irreducible representations of
simple Lie groups (over **C**) shows up.

Let V be an irreducible representation (of highest weight λ) of a simple
Lie group G, and let V_0 be the zero-weight subspace.  Let w_0 be the
longest word of the Weyl group.  For which λ and G does w_0 act as the
identity or minus the identity on V_0?  We call such λ "exceptional",
and call λ "mixed" if w_0 has both +1 and -1 eigenvalues on V_0.  (This
classification only applies of course to radical weights λ, namely when
λ is in the root lattice.)

In an upcoming paper we prove various properties such as the behaviour
under branching from G to subgroups.  We also show that certain
multiples of fundamental weights are exceptional, and for a finite
number of λ we compute by hand that they are mixed.  Starting from this
seed data, the Coq code being developped in this repository performs the
case-by-case analysis proving that all other radical weights are mixed.

Bruno Le Floch (Princeton University) and Ilia Smilga (Yale University)
