# Fermionic Coherent States in Lean

Lean 4 proofs for fermionic Husimi convex order, entropy minimization, and
eight-mode Gaussian rank.

**The basic exterior-power Husimi and entropy theorems are formalized end to
end. The Gaussian-rank-four theorem is not yet formalized end to end.**

| Result | Status | Main source |
| --- | --- | --- |
| Husimi convex order for every basic exterior power, with strict equality exactly at pure Slater states | End-to-end formalized | [HusimiInduction.lean](Fermionic/HusimiInduction.lean) |
| The actual Slater projector-orbit measure and its Haar correspondence | End-to-end formalized | [SlaterMeasure.lean](Fermionic/SlaterMeasure.lean) |
| Wehrl and all positive-order Rényi–Wehrl entropy minima, including equality cases | End-to-end formalized; coherent constants are expressed as integrals | [ExteriorEntropy.lean](Fermionic/ExteriorEntropy.lean) |
| The original eight-mode target satisfies $2\leq\chi_G(\Psi)\leq4$ | Formalized for the even Spin-vacuum-orbit dictionary | [PhysicalGaussianRank.lean](Fermionic/PhysicalGaussianRank.lean), [PureVacuumRigidity.lean](Fermionic/PureVacuumRigidity.lean) |
| The full normal-family polynomial certificate, for arbitrary complex parameters | Formalized coordinate identity | [RankCertificateFullNormal.lean](Fermionic/RankCertificateFullNormal.lean) |
| $\chi_G(\Psi)=4$, half-spin/odd-spin entropy theorems, and explicit entropy constants | TODO | [TODO.md](TODO.md) |

## Main theorem

Let $\rho$ be any density operator on $\Lambda^p\mathbb C^n$, with
$0\leq p\leq n$. Fix a unit Slater vector $\Omega$. Use the actual
exterior-power representation, writing $U\Omega=(\Lambda^pU)\Omega$, and
normalized Haar measure to define
$Q_\rho(U)=\langle U\Omega,\rho U\Omega\rangle$.
For every function $F$ continuous and convex on $[0,1]$, and every pure
Slater projector $P$,

$$
\int F(Q_\rho(U))\,dU\leq\int F(Q_P(U))\,dU.
$$

For each strictly convex $F$, equality holds if and only if $\rho$ is a
pure Slater state. The proof includes the representation, Haar conditioning,
conditional states, common mixture, and equality argument. It does not assume
these steps as interfaces. Wehrl entropy and Rényi–Wehrl entropy for every
real $q>0$, $q\ne1$, follow with the same equality characterization.

See [the precise statements and proof structure](docs/theorems.md).

## Verification

Pinned versions: **Lean 4.29.0** and mathlib
`8a178386ffc0f5fef0b77738bb5449d50efeea95`.

Three recorded runs passed clean project compilation, complete declaration
type and transitive-axiom audits, and a fresh replay of the imported proof
environment by the Lean kernel. Their shared source files are byte-identical.

| Verified suite | Modules | Theorems | Recorded result |
| --- | ---: | ---: | --- |
| Exterior powers and entropy | 20 | 309 | [result.json](evidence/result.json) |
| Gaussian-rank foundations and coordinate certificate | 33 | 257 | [result.json](rank_evidence/result.json) |
| Vacuum-chart rigidity and the rank-two lower bound | 12 | 150 | [result.json](rank_geometry_evidence/result.json) |

The suites overlap; these are three separate verification runs. No `sorry`,
`admit`, new mathematical axiom, or `native_decide` is used. The disclosed
logical axioms are `propext`, `Classical.choice`, and `Quot.sound`. Fresh replay
uses the same Lean kernel, not an independently implemented proof checker.

The supplied runners execute on **CAB17 over SSH**, using the pinned read-only
dependency cache. In the configured remote checkout:

```sh
python3 verify_remote.py
python3 verify_rank_remote.py
python3 verify_rank_geometry_remote.py
```

[Reproduction instructions](docs/verification.md) explain the setup, evidence,
trust boundary, and source-integrity check. No local Lean or Lake execution is
required or permitted by this project's execution policy.

## Work in progress

The rank certificate vanishes on the entire three-parameter normal family and
is nonzero at the encoded target. Completing the rank-four proof requires the
original Fock-to-coordinate dictionary, covariance under the actual common
operations, and reduction of every three-term pure-spinor sum, including
degenerate cases.

[The Gaussian-rank proof notes](docs/gaussian-rank-proof.md) give the paper-level
derivation and identify the exact Lean obligations. [TODO.md](TODO.md) also
covers the remaining entropy and spin-representation results. Paper-level
arguments are not counted as kernel-checked theorems.
