# Formalization TODO

The basic exterior-power Husimi comparison, its strict equality cases, and
the entropy minimizer theorems are complete. The entries below are not
claimed as Lean-verified results. A paper-level derivation explains a route
to a theorem; it does not discharge that theorem's formalization obligations.

## Gaussian rank four

The current bound for the original even-Spin-orbit target is
$2\le\chi_G(\Psi)\le4$. The coordinate polynomial is nonzero at the
encoded target and vanishes throughout the full normal family. To obtain
$\chi_G(\Psi)=4$, complete the following steps in order:

- [ ] Identify the original eight-mode occupation basis with the 256 masks,
  intertwining creation, contraction, the second-leg-reversal Chevalley
  pairing, and the full 120-dimensional bivector Gram construction.
- [ ] Realize the matrix covariance theorem by the actual common Clifford
  operations and exterior $GL$ action, including nonzero similarity factors.
- [ ] Reconstruct every nonzero-vacuum pure spinor with the common product
  of 28 elementary two-creation units. The annihilator graph and joint
  contraction kernel are already formalized.
- [ ] Normalize a transverse pair by operations on the entire three-term
  sum. Put the third term into the nondegenerate chart and construct the
  required alternating-form basis change.
- [ ] Construct the actual two-parameter polynomial deformation and prove
  its discriminant is nonzero. Apply the already-formalized polynomial
  boundary lemma to include degenerate third terms.
- [ ] Deduce certificate vanishing for every sum of at most three original
  pure spinors, contradict the target certificate, and combine with the
  original four-term Gaussian decomposition.
- [ ] Formalize any additional dictionary comparison allowing odd Gaussian
  terms, and the normalized four-mode tensor identification, before stating
  those equivalent physical formulations as verified roots.

The [self-contained paper proof](docs/gaussian-rank-proof.md) gives the
formulas, signs, common transformations, boundary argument, and Lean status
of each step. It does not assume the missing three-term exclusion as a
certificate input.

## Rank multiplicativity for two arbitrary four-mode even vectors

- [ ] Identify the coordinate Chevalley quadric with the actual four-mode
  physical Gaussian cone, in both directions.
- [ ] Prove the complex Spin action and its orbit classification on nonzero
  four-mode even vectors, including preservation of the physical cone.
- [ ] Construct the ordered tensor-to-exterior identification and the common
  local-group action on eight modes.
- [ ] Prove that successive vacuum conditioning takes each Gaussian summand
  to zero or a Gaussian vector on the remaining modes.

The intended statement, for nonzero even vectors $\psi,\phi$ on four modes,
is $\chi_G(\psi\otimes\phi)=\chi_G(\psi)\chi_G(\phi)$.
[FourMode.lean](Fermionic/FourMode.lean) already proves the rank-one/rank-two
classification for its explicit eight-coordinate quadratic cone. The
identification of that cone with the physical dictionary remains separate.

The paper route uses the four-mode complex Spin action on its invariant
quadric. After multiplication by nonzero scalars, nonisotropic vectors can
be brought to $1+\mathrm{vol}_4$. When both factors are non-Gaussian, apply
their two changes of coordinates to the same full eight-mode space and use
the pending rank-four result for $\Psi$. The natural local Spin-group
homomorphism has a diagonal central kernel; no injective group embedding is
needed, but its induced action and cone preservation must be proved.

If one factor is Gaussian, send it to the vacuum and condition any proposed
decomposition on that block. Conditional closure gives a decomposition of
the other factor with no more terms. The tensor product of known
decompositions gives the opposite inequality. Both-Gaussian inputs form the
remaining case. This argument needs the listed physical and tensor bridges;
the coordinate quadratic-cone theorem alone does not prove multiplicativity.

## Explicit exterior-power constants

- [ ] Derive the distribution of the first coherent conditional weight from
  the original Haar measurement.
- [ ] Formalize the Beta product law, all positive real moments, and the
  required positivity and boundary cases.
- [ ] Evaluate the Wehrl constant through logarithmic moments or justified
  differentiation under the integral.

For $0<p<n$, the paper route uses a uniform complex unit vector represented
by a normalized complex Gaussian vector. The sum of its first $p$ squared
coordinates is $X/(X+Y)$, where $X\sim\mathrm{Gamma}(p,1)$ and
$Y\sim\mathrm{Gamma}(n-p,1)$ are independent. It therefore has law
$\mathrm{Beta}(p,n-p)$. Exact coherent
conditioning then gives, for $q>0$,

$$
m_{p,n}(q)=\mathbb E[A^q]m_{p-1,n-1}(q)
=\prod_{j=0}^{p-1}
\frac{\Gamma(p-j+q)\Gamma(n-j)}
{\Gamma(p-j)\Gamma(n-j+q)}.
$$

Here $m$ is the unnormalized moment $\int Q^q$; the entropy uses
$N(q)=\binom np\,m(q)$. The empty and filled sectors are handled separately
with $Q\equiv1$, not with a Beta distribution having a zero shape parameter.
Using $\binom np\,m(1)=1$ and the logarithmic derivative gives

$$
S_W^{\min}=\sum_{j=0}^{p-1}(H_{n-j}-H_{p-j}),\qquad
H_k=\sum_{r=1}^k\frac1r.
$$

These explicit evaluations are paper-level here. The minimizer and strict
equality theorems do not depend on having formalized these evaluations.

## Half-spin and odd-spin measurements

- [ ] Construct the finite Fock Hilbert structure, continuous unitary compact
  Spin action, and both parity sectors as the actual measurement spaces.
- [ ] Prove the common covariance decomposition from one rotation of the
  same full density, normalized conditional Gaussian closure, and the
  smaller-group intertwining.
- [ ] Assemble Haar conditioning, convex-order induction, and full-density
  equality rigidity.
- [ ] For odd Spin, identify the restricted representation, the same coherent
  orbit, and equality of the Haar pushforward measures.

The paper mechanism parallels the exterior proof but has new geometric
obligations. One $SO(2n)$ block diagonalization of the Majorana covariance
matrix gives a rotated full density. Its occupation-basis diagonal entries
provide one probability vector for every measured direction; the common
weights must not depend on the later Haar variable. Gaussian conditional
states must stay in the smaller parity-appropriate coherent class. With
those facts and the actual subgroup action, conditional Jensen can be
iterated. Strict equality must then return to the original whole density.

For odd Spin, restricting a half-spin representation is not sufficient by
itself: transitivity on the same projective orbit and equality of the
invariant probability measures are essential. Existing algebraic Spin,
CAR, and parity lemmas in this repository do not yet establish these analytic
measurement theorems.

## Entropy refinements and measurement information

- [ ] Prove the $q\to1$ Rényi–Wehrl limit in the original integral
  convention, including the behavior at zeros of $Q$.
- [ ] Formalize quantitative entropy-deficit bounds.
- [ ] Define the actual coherent POVM, ensemble mutual information, and the
  capacity-achieving Haar coherent ensemble.
- [ ] For repeated measurements, construct conditional density matrices of
  the same potentially entangled input and prove the entropy chain rule.

For a quantitative bound, the proposed route combines the conditional
second-moment comparison with the complex-sphere identity

$$
\mathbb E\langle u,Au\rangle^2
=\frac{(\operatorname{Tr}A)^2+\operatorname{Tr}(A^2)}{n(n+1)}
$$

for Hermitian $A$, $n\ge1$, and $u$ uniform on the complex unit sphere, and applies convex order to
$x\log x-\tfrac12x^2$. The moment identity and final quantitative bound
are additional formalization tasks.

For the measurement output density $f_\rho=DQ_\rho$, the paper identity
is $h_\nu(f_\rho)=S_W(\rho)-\log D$. Combining the ensemble
mutual-information identity with the entropy minimum suggests capacity
$\log D-S_W^{\min}$, attained by the Haar ensemble of coherent states.
This requires a formal definition of the measurement channel and proof of
attainment. The repeated-use claim additionally needs genuine conditional
states and the chain rule; a scalar entropy inequality alone does not prove
it. These TODOs concern this specified measurement channel, not arbitrary
quantum channels.
