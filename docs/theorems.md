# Formalized statements

## Exterior-power Husimi convex order

Fix integers $0\le p\le n$. Put
$\mathcal H=\Lambda^p\mathbb C^n$, with the increasing occupation wedges
orthonormal, and $D=\binom np$. A density operator means an arbitrary
positive semidefinite operator $\rho$ on this whole space with
$\operatorname{Tr}\rho=1$. Mixed and rank-deficient states are included.

Let $\nu$ be normalized unitary-group Haar measure pushed forward to the
actual rank-one Slater-projector orbit. Define

$$
Q_\rho(P)=\operatorname{Tr}(\rho P),\qquad 0\le Q_\rho(P)\le1.
$$

For every pure Slater density $\sigma$ and every $F:\mathbb R\to\mathbb R$
continuous and convex on $[0,1]$,

$$
\int F(Q_\rho(P))\,d\nu(P)
\le \int F(Q_\sigma(P))\,d\nu(P).
$$

For each fixed strictly convex $F$, equality holds if and only if $\rho$
is a pure Slater density. It need not equal the particular comparator
$\sigma$. The coherent comparison integral is independent of the chosen
Slater state.

This statement is **formalized end to end**. The main roots are:

- [HusimiInduction.lean](../Fermionic/HusimiInduction.lean):
  `Fermionic.HusimiInduction.exterior_husimi_convex_order`,
  `exterior_husimi_convex_order_any_slater`, and `exterior_husimi_equality_iff`.
- [SlaterMeasure.lean](../Fermionic/SlaterMeasure.lean):
  `Fermionic.SlaterMeasure.orbit_husimi_convex_order` and
  `orbit_husimi_equality_iff`.

The Lean occupation reference `S : Index n p` enforces $p\le n$.
The cases $p=0$, $p=n$, and $n=0$ are included: the corresponding
one-dimensional sector has its unique density, which is Slater, and
$Q\equiv1$. Higher Cartan powers of a fundamental representation are not
among these quantifiers.

The orbit measure is constructed as a pushforward of the actual $U(n)$
Haar measure. Invariance, reference independence, and complete orbit coverage
are proved. This does not claim a separate implementation of an abstract
Grassmannian manifold and its differential geometry.

## How the end-to-end proof connects

The representation uses the original exterior algebra and an explicit
occupation-coordinate equivalence. The minors defining the exterior-power
action are proved to intertwine this representation. The one-particle matrix
is derived from the same full density and actual infinitesimal action.

Conditioning on one occupied mode gives a compression of the full rotated
density, retaining all off-diagonal terms. Its trace is the actual occupation
weight. A zero weight forces the whole positive compression to vanish;
normalization is used only on positive-weight branches.

One diagonalization of the same one-particle matrix gives a single set of
occupation probabilities. This common mixture controls all directions in the
Haar integral. The conditional Slater state remains a Slater state in the
smaller exterior-power sector. Exact Haar conditioning and induction then
give the convex comparison. Strict Jensen equality, full support, and density
rigidity return a statement about the original whole density.

These steps are in the checked dependency chain. They are not unproved
assumptions supplied to the terminal theorem. The full elaborated types and
transitive axioms appear in
[the declaration audit](../evidence/logs/declaration-types-and-axioms.log).

## Moments and entropy

The conventions are

$$
N_\rho(q)=D\int Q_\rho^q\,d\nu,\qquad
S_q(\rho)=\frac{\log N_\rho(q)}{1-q},\qquad
S_W(\rho)=-D\int Q_\rho\log Q_\rho\,d\nu.
$$

Logarithms are natural, and $0\log0=0$. The density relative to $\nu$
is $DQ_\rho$; the function $Q_\rho$ itself integrates to $1/D$.

[ExteriorEntropy.lean](../Fermionic/ExteriorEntropy.lean) proves:

- $D=\binom np$ and $N_\rho(1)=1$.
- For $q>1$, $N_\rho(q)\le N_\sigma(q)$.
- For $0<q<1$, $N_\rho(q)\ge N_\sigma(q)$.
- For every real $q>0$, $q\ne1$, equality of these moments is equivalent
  to $\rho$ being a pure Slater state. The moments are strictly positive.
- $S_W(\rho)\ge S_W(\sigma)$, with equality exactly at pure Slater states.
- $S_q(\rho)\ge S_q(\sigma)$ for every real $q>0$, $q\ne1$, with
  the same equality characterization.

The entropy roots are `wehrl_minimum`, `wehrl_eq_iff_slater`,
`renyiWehrl_minimum`, and `renyiWehrl_eq_iff_slater`, in namespace
`Fermionic.ExteriorEntropy`.

These minimizer theorems are **formalized end to end with their coherent
constants expressed as integrals**. Explicit Beta/Gamma and harmonic-number
evaluations are TODO. The $q\to1$ limit of Rényi–Wehrl entropy has not been
formalized; the total Lean definition at $q=1$ is not asserted to be Wehrl
entropy.

## Gaussian rank: the exact current scope

In the original eight-mode exterior algebra, let

$$
\Psi=1+e_0e_1e_2e_3+e_4e_5e_6e_7+e_0e_1\cdots e_7.
$$

The dictionary consists of nonzero complex scalar multiples of the vacuum
orbit under the actual real Euclidean Spin action. It is the even branch;
arbitrary complex coefficients and operations mixing the two blocks are
allowed. The minimum is defined from a proved four-term decomposition of this
same vector, rather than from an assumed existence theorem.

The code proves

$$
2\le\chi_G(\Psi)\le4.
$$

The upper root is
`Fermionic.PhysicalGaussianRank.targetGaussianRank_le_four`; the lower root is
`Fermionic.PureVacuumRigidity.two_le_targetGaussianRank`. Scaling by a nonzero
complex scalar preserves the available decomposition lengths. A separate
Hilbert tensor-product identification with normalized magic states is not
part of that scalar-invariance theorem.

The complete coordinate certificate is proved for all complex normal-family
parameters, including zero parameters. The actual original Fock-to-coordinate
dictionary and all-three-term reduction are still TODO, so the coordinate
certificate does not yet give a formalized lower bound of four. The complete
paper-level argument and remaining obligations are in
[gaussian-rank-proof.md](gaussian-rank-proof.md).
