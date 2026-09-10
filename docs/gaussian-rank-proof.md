# The eight-mode Gaussian-rank problem

This document explains the proposed polynomial proof of Gaussian rank four for two copies of the four-mode magic state, and identifies exactly which parts are formalized.

**The repository does not yet contain an end-to-end Lean proof of Gaussian rank four.** It proves the bound

$$
2\leq\chi_G^+(\Psi)\leq4
$$

for the actual eight-mode target and the even Euclidean-Spin Gaussian dictionary. It also proves complete finite-coordinate polynomial certificates for the target and a three-parameter normal family. Connecting those certificates to every possible three-term physical Gaussian decomposition remains TODO.

The labels below have the following meanings:

- **Lean proved:** a declaration in the linked source proves the stated result, with its actual definitions and hypotheses.
- **Paper argument:** the mathematical derivation is given here, but the corresponding complete Lean bridge has not been implemented.
- **TODO:** an implementation obligation needed for the original rank-four theorem. It is not an assumption of a completed rank-four theorem.

All Lean names below begin with `Fermionic.` unless stated otherwise.

## 1. The target and the physical dictionary

Let $E=\mathbb C^8$, with its standard Hermitian inner product and ordered basis $e_0,\ldots,e_7$. The full Fock space is the actual exterior algebra

$$
\mathcal S=\Lambda E,
\qquad \mathcal S^+=\Lambda^{\mathrm{even}}E.
$$

Write

$$
v_A=e_0e_1e_2e_3,\qquad
v_B=e_4e_5e_6e_7,\qquad
\mathrm{vol}=e_0\cdots e_7,
$$

where juxtaposition denotes the exterior product. The unnormalized target is

$$
\Psi=(1+v_A)(1+v_B)=1+v_A+v_B+\mathrm{vol}.
\tag{1}
$$

In the usual occupation identification, if
$M=(|0000\rangle+|1111\rangle)/\sqrt2$, then $M^{\otimes2}=\Psi/2$.

The physical dictionary is the nonzero complex cone over the vacuum orbit of the **real, positive Euclidean** group $\operatorname{Spin}(16)$:

$$
\widehat{\mathcal G}^{+}
=\{c\,U_x1:x\in\operatorname{Spin}(16),\ c\in\mathbb C\setminus\{0\}\}.
$$

The group acts on the whole Fock representation. No condition is imposed that an individual Gaussian term respect the two four-mode blocks. Arbitrary cross-block pairing and arbitrary complex decomposition coefficients are allowed. The latter are absorbed into the nonzero cone elements.

For $\psi\neq0$, define

$$
\chi_G^+(\psi)=\min\{r:\psi=g_1+\cdots+g_r,
\quad g_i\in\widehat{\mathcal G}^{+}\}.
\tag{2}
$$

**Lean proved.** [`PhysicalGaussian.lean`](../Fermionic/PhysicalGaussian.lean) defines this actual Spin-orbit cone as `PhysicalGaussian.IsGaussian`. [`SpinorTransport.lean`](../Fermionic/SpinorTransport.lean) constructs its representation from the real quadratic form $v\mapsto\|v\|^2$, embedded by

$$
v\longmapsto(\langle v,\cdot\rangle,v)
$$

in the complex split Clifford space. The dictionary is not defined by declaring vectors to be algebraically pure.

[`PureDecomposition.lean`](../Fermionic/PureDecomposition.lean) defines (1) using the standard basis of `EuclideanSpace ℂ (Fin 8)` and its induced full exterior-algebra basis. [`PhysicalOccupancy.lean`](../Fermionic/PhysicalOccupancy.lean), in `target_has_gaussian_decomposition`, proves that its four original occupation terms are physical Gaussian vectors. Thus the minimum in [`PhysicalGaussianRank.lean`](../Fermionic/PhysicalGaussianRank.lean) exists without a conjectural lower-bound hypothesis, and `targetGaussianRank_le_four` proves the upper bound.

[`GaussianScaling.lean`](../Fermionic/GaussianScaling.lean) proves `decomposition_smul_iff` for every nonzero complex scalar and every term count. Its `normalizedTarget_minimum` applies the same minimum to the coefficient-rescaled target $\Psi/2$. This is an exact coefficient statement; the file does not separately construct the Hilbert tensor-product identification with two normalized four-mode states.

**Paper argument / TODO for the enlarged dictionary.** If odd Gaussian vectors are also admitted, each dictionary vector has definite parity. In a decomposition of an even target, the sum of the odd terms is zero. Removing all odd terms preserves the vector and cannot increase the number of terms. Therefore the even and enlarged-dictionary minima agree. The current physical rank definition uses the even orbit. [`FockParity.lean`](../Fermionic/FockParity.lean) proves that this orbit is even, but does not implement the enlarged dictionary and this deletion argument.

## 2. Algebraic purity and the currently proved lower bound

Use the split space $U=E^*\oplus E$, ordered as in the Lean implementation. Its quadratic form and Clifford action are

$$
q(f,v)=f(v),\qquad
c(f,v)=\iota_f+\varepsilon_v,
$$

where $\varepsilon_v s=v\wedge s$. The polar form is

$$
b((f,v),(g,w))=f(w)+g(v).
$$

The original canonical anticommutation relations are

$$
c(u)^2=q(u)I,\qquad
c(u)c(w)+c(w)c(u)=b(u,w)I.
\tag{3}
$$

A nonzero $s\in\mathcal S$ is algebraically pure if its full annihilator

$$
\operatorname{Ann}(s)=\{u\in U:c(u)s=0\}
$$

has complex dimension eight. This condition retains every Clifford direction, not a selected collection of tests.

**Lean proved.** [`Fock.lean`](../Fermionic/Fock.lean) constructs creation, contraction, and the Clifford representation on `ExteriorAlgebra`; `action_square` and `action_car` prove (3). [`Spinor.lean`](../Fermionic/Spinor.lean) defines `IsPure` by this annihilator condition. `PhysicalGaussian.gaussian_isPure` proves the physical-to-algebraic inclusion, and `decomposition_implies_pure` keeps the same summands, coefficients, and exact sum equation.

The present lower bound two comes from a separate complete argument, not from assuming the pending polynomial bridge. For a pure vector with nonzero vacuum coefficient, its annihilator is a graph over $E^*$. If all vacuum coefficients after two contractions vanish, that graph is zero. Every contraction then kills the vector, so it is a scalar vacuum. For $\Psi$, the vacuum coefficient is one and all two-contraction vacuum coefficients are zero, but its $v_A$-coefficient is one. Thus $\Psi$ is not pure and cannot be one physical Gaussian term.

The relevant proved declarations are:

- [`PureVacuumChart.graphDirection_two_contractions`](../Fermionic/PureVacuumChart.lean);
- [`FockVacuumKernel.joint_annihilation_kernel`](../Fermionic/FockVacuumKernel.lean);
- [`PureVacuumRigidity.target_not_pure`](../Fermionic/PureVacuumRigidity.lean);
- [`PureVacuumRigidity.two_le_targetGaussianRank`](../Fermionic/PureVacuumRigidity.lean).

Together with the actual physical four-term construction, these prove exactly the stated end-to-end interval $2\leq\chi_G^+(\Psi)\leq4$.

## 3. The polynomial obstruction

### 3.1 Fixing the Chevalley convention

On the whole exterior algebra, use the bilinear form

$$
\mathcal B(s,t)=[s\wedge\operatorname{rev}(t)]_{\mathrm{vol}},
\qquad
\operatorname{rev}|_{\Lambda^kE}=(-1)^{k(k-1)/2}I.
\tag{4}
$$

**Reversal acts on the second argument.** There is no complex conjugation in (4).

For $S=\{s_1<\cdots<s_k\}\subseteq\{0,\ldots,n-1\}$, the sign in
$[e_S\wedge\operatorname{rev}(e_{S^c})]_{\mathrm{vol}}$ has exponent

$$
\sum_i s_i-\frac{k(k-1)}2+rac{(n-k)(n-k-1)}2
=\sum_i s_i+\frac{n(n-1)}2-(n-1)k.
$$

For $n=8$, this is congruent modulo two to $\sum_i(s_i+1)$. Hence

$$
\mathcal B(e_S,e_{S^c})=(-1)^{\sum_{i\in S}(i+1)}.
\tag{5}
$$

This matches `RankCertificate.chevalleySign` in every degree, including odd degree. A first-argument reversal would give a different odd-degree sign and must not be substituted for (4).

### 3.2 All 120 bivector directions

Let $W=\Lambda^2U$, of dimension 120. Its nondegenerate induced bilinear form is

$$
G(u\wedge v,w\wedge z)=b(u,w)b(v,z)-b(u,z)b(v,w).
$$

Define the bivector action and its source map by

$$
\rho_2(u\wedge v)=\tfrac12[c(u),c(v)],
\qquad \mathcal J_\psi(p)=\rho_2(p)\psi.
$$

The full bilinear Gram and its associated endomorphism are

$$
H_\psi(p,q)=\mathcal B(\mathcal J_\psi(p),\mathcal J_\psi(q)),
\qquad A_\psi=G^{-1}H_\psi.
\tag{6}
$$

In coordinates, $A_\psi=G^{-1}\mathcal J_\psi^{\mathsf T}\mathcal B\mathcal J_\psi$. This uses the ordinary transpose, not the conjugate transpose. The operator $A_\psi$ must not be confused with a positive Hermitian Gram matrix.

Set

$$
s_\psi=\tfrac12\mathcal B(\psi,\psi),\qquad
t_j(\psi)=\operatorname{Tr}(A_\psi^j),
$$

and define

$$
\begin{aligned}
F_{16}(s,t_4,t_6)
&=576s^2t_6-7t_4^2-18960s^4t_4+4205376s^8,\\
P_{18}(s,t_4,t_6)&=sF_{16}(s,t_4,t_6).
\end{aligned}
\tag{7}
$$

When evaluated through (6), these have degrees 16 and 18 in the source vector. The proposed obstruction is that $P_{18}$ vanishes on every sum of three even pure spinors, whereas it is nonzero at $\Psi$.

### 3.3 What the coordinate certificates prove

**Lean proved, in explicit finite coordinates.** Directions 0–7 create and 8–15 annihilate. The code uses all ordered pairs $i<j$, with proved bijections onto all 120 directions. Its `bivectorCoefficient2` represents twice the bivector action, so the final Gram includes a factor $1/4$.

For the four-mask target, [`RankCertificateTrace.lean`](../Fermionic/RankCertificateTrace.lean) proves

$$
s_\Psi=2,\qquad t_4(\Psi)=3648,\qquad t_6(\Psi)=57408
$$

in its explicit coordinate definitions, and the root is

```lean
RankCertificate.full_coordinate_target_certificate :
  invariant18 actualTargetHalfPair
    (Matrix.trace (actualTargetGram ^ 4))
    (Matrix.trace (actualTargetGram ^ 6)) = 18063360
```

The corresponding nonzero theorem is also proved. No trace value or Gram-entry identity is an assumption of this root.

Now put

$$
Q_0=(1+e_0e_1)(1+e_2e_3)(1+e_4e_5)(1+e_6e_7),
\qquad \eta(a,b,c)=a\,1+b\,\mathrm{vol}+cQ_0.
\tag{8}
$$

Write $x=ab$, $y=ac$, $z=bc$, $s=x+y+z$, and $p=xyz$. The full coordinate Gram has a common block decomposition whose positive-power trace is

$$
\operatorname{Tr}(A_{\eta}^j)=27\operatorname{Tr}(T^j)+\operatorname{Tr}(R^j),
\qquad j>0,
$$

where

$$
T=\begin{pmatrix}
s&z&z&2z\\-y&0&0&-z\\-y&0&0&-z\\2y&y&y&s
\end{pmatrix},\qquad
R=\begin{pmatrix}
s&-3z&-3z&-6z\\3y&2s&2s&3z\\3y&2s&2s&3z\\-6y&-3y&-3y&s
\end{pmatrix}.
$$

The zero block has dimension eight; the remaining decomposition contains 24 copies of $T$ and a 16-dimensional common block contributing three further copies of $T$ and one of $R$. This retains the entire 120-dimensional matrix. It yields

$$
\begin{aligned}
t_4&=312s^4-1728sp,\\
t_6&=4152s^6-69984s^3p+36288p^2.
\end{aligned}
\tag{9}
$$

Substitution in (7) gives $F_{16}=0$. The relevant sources are [`RankCertificateCompression.lean`](../Fermionic/RankCertificateCompression.lean), [`RankCertificateNormalTrace.lean`](../Fermionic/RankCertificateNormalTrace.lean), and [`RankCertificateFullNormal.lean`](../Fermionic/RankCertificateFullNormal.lean). The final root is

```lean
RankCertificate.full_coordinate_normal_certificate (a b c : ℂ) :
  invariant18 (actualNormalHalfPair a b c)
    (Matrix.trace (actualNormalFullGram a b c ^ 4))
    (Matrix.trace (actualNormalFullGram a b c ^ 6)) = 0
```

It includes all complex parameters, including zero and degenerate values. The original square terms and both orders of every mixed term are proved from the full source sum before this root is assembled. They are not removed by definition.

**TODO: the semantic identification.** These are complete proofs of the displayed coordinate definitions, but a separate theorem must identify them with (4)–(6) on mathlib's actual exterior algebra. That theorem must intertwine the original occupation basis, every creation and contraction operator, the Chevalley form, and the inverse bivector metric. Names such as `actualTargetGram` do not supply this bridge.

[`RankBitDomain.lean`](../Fermionic/RankBitDomain.lean) already proves that every mask read by the target and normal-family formulas remains below 256 and has the required low-eight-bit parity. This matters because `pairedGaussianCoefficient : ℕ → ℤ` only tests the lowest eight bits; its values outside the byte domain are not a finite-support coefficient function. The bit-domain module does not yet identify its parity predicate with the exterior-algebra grading.

## 4. Reconstructing the vacuum chart using 28 elementary units

The following construction avoids a prerequisite theory of general exterior exponentials.

### 4.1 The graph already available in Lean

Let $s$ be pure with nonzero vacuum coefficient $s_0$. Projection of $\operatorname{Ann}(s)$ to $E^*$ is injective: a creator that kills $s$ has zero degree-one contribution $s_0v$, hence is zero. Both spaces have dimension eight, so the projection is an isomorphism. Its inverse defines a linear map $D:E^*\to E$ such that

$$
(\iota_f+\varepsilon_{Df})s=0\quad\text{for every }f\in E^*.
\tag{10}
$$

The CAR give

$$
f(Dg)+g(Df)=0.
\tag{11}
$$

**Lean proved.** These are `PureVacuumChart.graphDirection_annihilates` and `graphDirection_skew`. The same file gives

$$
f_j(Df_i)=-\frac{[\iota_{f_j}\iota_{f_i}s]_0}{s_0}.
\tag{12}
$$

### 4.2 An elementary shear

**Paper argument / TODO.** For $i<j$, set $N_{ij}=\varepsilon_i\varepsilon_j$. The creation CAR imply

$$
N_{ij}^2=0,\qquad [N_{ij},\varepsilon_v]=0,
\qquad [N_{ij},N_{k\ell}]=0.
$$

These include shared-index cases, in which the relevant exterior products vanish. Hence

$$
U_{ij}(a)=I+aN_{ij},\qquad U_{ij}(a)^{-1}=I-aN_{ij}.
$$

The original mixed CAR also give

$$
[\iota_f,N_{ij}]
=\varepsilon_{f(e_i)e_j-f(e_j)e_i}.
$$

The right-hand side times $N_{ij}$ is zero. Consequently, on the entire Fock space,

$$
U_{ij}(a)^{-1}\iota_fU_{ij}(a)
=\iota_f+a\varepsilon_{f(e_i)e_j-f(e_j)e_i}.
\tag{13}
$$

All creators are fixed by this conjugation. Both $U_{ij}(a)$ and its inverse preserve the vacuum coefficient.

### 4.3 Recovering every degree of the original vector

Choose

$$
a_{ij}=f_i(Df_j)=-f_j(Df_i),\qquad i<j,
$$

and define

$$
h_a(f)=\sum_{i<j}a_{ij}\bigl(f(e_i)e_j-f(e_j)e_i\bigr).
$$

Equation (11), including its diagonal consequence in characteristic zero, gives $h_a=-D$ on the whole dual space. Form one fixed product

$$
T_a=\prod_{i<j}U_{ij}(a_{ij}),\qquad
Q_a=T_a1=\prod_{i<j}(1+a_{ij}e_ie_j).
\tag{14}
$$

Composing (13) gives

$$
T_a^{-1}\iota_fT_a=\iota_f+\varepsilon_{h_a(f)},
\qquad
\iota_f(T_a^{-1}s)=T_a^{-1}(\iota_f+\varepsilon_{Df})s=0.
$$

The **proved** `FockVacuumKernel.joint_annihilation_kernel` says that the common kernel of all original contractions is precisely the scalar vacuum line. Therefore the paper construction yields

$$
T_a^{-1}s=s_0\,1,\qquad s=s_0Q_a.
\tag{15}
$$

This recovers the whole vector, including every higher-degree coefficient. There is no truncation followed by an unproved reconstruction step. The missing Lean work is the elementary-unit construction and its simultaneous intertwining, not the final common-kernel lemma.

The same proof establishes uniqueness: any two vectors killed by the same complete graph (10) and having the same vacuum coefficient are equal. This uniqueness does not require a separate purity assumption on those two vectors.

### 4.4 General linear covariance by uniqueness

**Paper argument / TODO.** For $g\in\operatorname{GL}(E)$, the original exterior map satisfies

$$
\iota_f\Lambda g=\Lambda g\,\iota_{f\circ g},\qquad
\varepsilon_{gv}\Lambda g=\Lambda g\,\varepsilon_v.
$$

The transported graph is

$$
D^g(f)=g\bigl(D(f\circ g)\bigr).
\tag{16}
$$

Both $\Lambda g Q_D$ and $Q_{D^g}$ are annihilated by this graph and have vacuum coefficient one. Uniqueness therefore gives

$$
\Lambda g Q_D=Q_{D^g}.
\tag{17}
$$

This avoids expanding all transformed factors of (14). If the alternating graph is nondegenerate, an ordinary alternating-form basis reduction sends it to the standard graph associated with $Q_0$. Such a basis is obtained by choosing a pair with nonzero pairing, normalizing that pairing to one, splitting off its two-dimensional nondegenerate span, and repeating on its orthogonal complement. The complement is nondegenerate because a vector orthogonal to it and to the selected pair is orthogonal to the whole space. After four steps the standard form is reached. This finite-dimensional reduction remains a Lean TODO; it is not a supplied hypothesis asserting that a suitable $g$ exists.

## 5. Covariance of the complete polynomial

Suppose actual invertible maps $T:\mathcal S\to\mathcal S$ and $R:U\to U$ satisfy

$$
Tc(z)T^{-1}=c(Rz),\qquad
b(Rz,Rw)=b(z,w),\qquad
\mathcal B(Ts,Tt)=\lambda\mathcal B(s,t),
\quad\lambda\neq0.
\tag{18}
$$

Let $L=\Lambda^2R$. Then

$$
\mathcal J_{T\psi}=T\mathcal J_\psi L^{-1},\qquad
A_{T\psi}=\lambda L A_\psi L^{-1}.
$$

Thus all moments transform together:

$$
s_{T\psi}=\lambda s_\psi,\quad
t_j(T\psi)=\lambda^j t_j(\psi),\quad
F_{16}(T\psi)=\lambda^8F_{16}(\psi),\quad
P_{18}(T\psi)=\lambda^9P_{18}(\psi).
\tag{19}
$$

**Lean proved, as a matrix theorem.** [`RankGramTransport.lean`](../Fermionic/RankGramTransport.lean) proves `gram_relative_covariance`, `trace_pow_relative`, and `complete_gram_certificate_zero_iff`, with the explicit two form identities as hypotheses. Every cross entry uses the same source and direction maps. This theorem does not establish (18) for the concrete Clifford operations by itself.

**Paper argument / TODO for the concrete operations.** For (4), each Clifford generator is skew-adjoint in the bilinear sense:

$$
\mathcal B(c(z)s,t)=-\mathcal B(s,c(z)t).
$$

Let $\tau_i=\varepsilon_i+\iota_{f_i}$. Then $\tau_i^2=I$, and its form multiplier is $-1$. An even product has multiplier one. Two-creation and two-contraction elementary units have multiplier one: their generators are bilinearly skew-adjoint, square to zero, and the quadratic term in the transformed form vanishes. For $\Lambda g$, the multiplier is $\det g$, since (4) reads the top exterior degree. This determinant factor must be retained; an arbitrary $\Lambda g$ is not an isometry of $\mathcal B$.

The CAR show that these operations act by orthogonal shears or reflections on the full split space, and hence preserve algebraic purity. Once these facts and the coordinate identification are formalized, the existing matrix theorem supplies (19).

## 6. One common normalization of a nonorthogonal pair

**Paper argument / TODO.** First, every nonzero even pure spinor can be sent to a nonzero scalar vacuum by allowed operations. Choose a nonzero occupation coefficient indexed by an even set $I$. The product $\tau_I$ sends that coefficient to the vacuum coefficient, up to a nonzero sign: its action toggles exactly the set $I$. The vacuum chart (15) then removes the remaining graph by one inverse product of two-creation units.

These maps preserve $\mathcal B$, so every even pure spinor has zero self-pairing, as the vacuum does.

Now let $g_1,g_2$ be nonzero even pure spinors with $\mathcal B(g_1,g_2)\neq0$. Apply the preceding operations to the **entire proposed decomposition**, not just to $g_1$. The first term becomes $\alpha1$. The second term then has nonzero top coefficient $\beta$, because

$$
\mathcal B(\alpha1,g_2')=\alpha\beta\neq0.
$$

Put $C=\tau_0\cdots\tau_7$. In the fixed order, $C$ exchanges vacuum and volume and $C^2=I$. Apply the vacuum chart to $Cg_2'$. Conjugating its two-creation units by $C$ gives two-contraction units, so

$$
g_2'=\beta V\,\mathrm{vol}
$$

for an invertible product $V$ of such units. Its inverse fixes the vacuum. Applying the same $V^{-1}$ to all terms yields

$$
\alpha1,\qquad\beta\mathrm{vol},\qquad s,
\tag{20}
$$

where the third term remains an arbitrary nonzero even pure spinor. No block symmetry or special graph condition has been imposed on that term.

The signs in the two-contraction factors can be fixed by the explicit conjugation $CUC$; they need not be guessed from an exponential convention.

## 7. Extending the normal-family identity to every third term

This is an algebraic specialization argument. It does not assume that the third term already lies in the nondegenerate vacuum chart.

### 7.1 A polynomial deformation with nonzero vacuum coefficient

**Paper argument / TODO.** For the third term $s$ in (20), choose a nonzero even occupation coefficient $s_I$. Write the increasing set $I$ as $k$ successive ordered pairs $(i_r,j_r)$, and define

$$
D_r=\iota_{f_{j_r}}\iota_{f_{i_r}},\qquad
h(t)=\prod_{r=1}^{k}(I+tD_r)s,
\qquad a(t)=[h(t)]_0.
\tag{21}
$$

Each factor has inverse $I-tD_r$; the factors commute. Every $h(t)$ is therefore nonzero and pure. This deforms the third term to construct a polynomial family; it does not claim to preserve the polynomial value of the original three-term sum. To produce a vacuum term using all $k$ contractions, the original support must be exactly $I$. With the displayed ordered-pair convention, the coefficient of $t^k$ in $a(t)$ is $s_I\neq0$. Thus $a(t)$ is a nonzero polynomial. This also covers $k=0$, when $a(t)=s_\varnothing\neq0$.

### 7.2 Making the graph nondegenerate

Use the four standard two-creation units

$$
W(u)=\prod_{r=0}^{3}(I+u\varepsilon_{2r}\varepsilon_{2r+1}),
\quad r(t,u)=W(u)h(t),
\quad r(0,0)=s.
\tag{22}
$$

Let $\omega_0=e_0e_1+e_2e_3+e_4e_5+e_6e_7$, and let $K(\omega):E^*\to E$ denote contraction into a two-form: $K(\omega)f=\iota_f\omega$. Then

$$
[r(t,u)]_0=a(t),\qquad
[r(t,u)]_2=[h(t)]_2+u\,a(t)\omega_0.
$$

Put $J=K(\omega_0)$, which is invertible, and define the polynomial

$$
\Delta(t,u)=a(t)\det\bigl(K([h(t)]_2)+u\,a(t)J\bigr).
\tag{23}
$$

Its coefficient of $u^8$, as a polynomial over $\mathbb C[t]$, is
$a(t)^9\det J\neq0$. Hence $\Delta$ is not the zero polynomial.

Whenever $\Delta(t,u)\neq0$, the vacuum coefficient is nonzero and the alternating graph of $r(t,u)$ is nondegenerate. Indeed, (12) identifies that graph as minus contraction into $[r]_2/a(t)$. The graph reconstruction and GL reduction in Section 4 therefore send the whole vector

$$
\alpha1+\beta\mathrm{vol}+r(t,u)
$$

by one common $\Lambda g$ to the normal family (8). Vacuum is fixed, the volume coefficient acquires $\det g$, and the third term becomes a scalar multiple of $Q_0$. The normal identity and (19) give

$$
P(t,u):=F_{16}\bigl(\alpha1+\beta\mathrm{vol}+r(t,u)\bigr)=0
\quad\text{whenever }\Delta(t,u)\neq0.
\tag{24}
$$

Here evaluation of $F_{16}$ means (6)–(7), so $P$ is a polynomial in $t,u$. The same $g$ acts on all three summands at a given parameter value. No transformation chosen solely for the third summand is substituted into an unchanged sum.

### 7.3 Returning to the exact original vector

At every point, $P\Delta=0$: either $\Delta=0$, or (24) applies. Evaluation of multivariate polynomials over the infinite field $\mathbb C$ is injective, so $P\Delta$ is the zero polynomial. The polynomial ring is an integral domain and $\Delta\neq0$, hence $P=0$. Evaluation at $(0,0)$ gives

$$
F_{16}(\alpha1+\beta\mathrm{vol}+s)=0
\tag{25}
$$

for the exact original third term, including all degenerate cases.

**Lean proved, as the general algebraic step.** [`PolynomialBoundary.lean`](../Fermionic/PolynomialBoundary.lean) proves `eq_zero_of_vanish_off_zero` and `eval_eq_zero_at_boundary`. The concrete $P$, $\Delta$, their coefficient identities, and the implication (24) remain TODO. The general lemma does not provide those geometric hypotheses automatically.

## 8. How the remaining pieces would imply rank four

**Paper argument; the combined Lean theorem is TODO.** For a sum $x=g_1+g_2+g_3$ of nonzero even pure spinors, all self-pairings vanish.

If $s_x=\mathcal B(x,x)/2=0$, then $P_{18}(x)=0$ directly from (7). Otherwise at least one pair has nonzero Chevalley pairing. Relabel that pair, apply the common normalization of Section 6, and use (25). Relative covariance gives $F_{16}(x)=0$, and therefore $P_{18}(x)=0$.

Thus the paper argument covers all three-term sums, not merely a generic chart. A decomposition with one or two terms can be refined to three by splitting a nonzero cone term into two nonzero scalar multiples. Therefore vanishing on all three-term sums also excludes every decomposition with at most three terms whenever $P_{18}$ is nonzero.

After the coordinate-to-Fock bridge, the target certificate would give $P_{18}(\Psi)=18063360\neq0$. Every physical Gaussian term is algebraically pure, so no physical decomposition with at most three terms would exist. The already proved physical four-term construction would then establish

$$
\chi_G^+(\Psi)=4,
\qquad\chi_G^+(\Psi/2)=4.
$$

This is the intended completed proof. The repository currently proves its separate components only to the extent marked above; it does not export this rank-four conclusion.

## 9. TODO dependency checklist

The following are genuine missing implementations, rather than optional exposition:

| TODO | Required result | Existing source to connect |
|---|---|---|
| Coordinate semantics | A concrete occupation-basis/byte equivalence; all 16 creation and contraction intertwining formulas; second-leg-reversal pairing; inverse metric on all 120 bivectors | [`Fock`](../Fermionic/Fock.lean), [`PureDecomposition`](../Fermionic/PureDecomposition.lean), [`RankBitDomain`](../Fermionic/RankBitDomain.lean), [`RankCertificateTrace`](../Fermionic/RankCertificateTrace.lean) |
| One full source polynomial | Define (6)–(7) for every original Fock vector and identify both target and normal-family specializations with the certified matrices | [`RankCertificateFullNormal`](../Fermionic/RankCertificateFullNormal.lean) |
| Elementary graph reconstruction | Prove (13)–(15) using one simultaneous product, including coefficient signs and augmentation preservation | [`PureVacuumChart`](../Fermionic/PureVacuumChart.lean), [`FockVacuumKernel`](../Fermionic/FockVacuumKernel.lean) |
| Concrete common covariance | Original CAR conjugation, second-leg Chevalley multipliers, all bivector directions, and the hypotheses of (18) for elementary units, particle-hole products, and $\Lambda g$ | [`SpinorTransport`](../Fermionic/SpinorTransport.lean), [`RankGramTransport`](../Fermionic/RankGramTransport.lean) |
| Full chart normalization | Same-graph/same-vacuum uniqueness, actual GL intertwining, and nondegenerate alternating-form reduction | The graph and kernel lemmas above; no assumed normal-form interface |
| Every third term | Construct (21)–(23) in the original space; prove the nonzero leading coefficient; obtain (24) at every nondegenerate point | [`PolynomialBoundary`](../Fermionic/PolynomialBoundary.lean) supplies only the last extension step |
| Final lower bound | Combine three-term vanishing with the original target's nonzero polynomial and transfer the unchanged physical decomposition term by term | [`PhysicalGaussian`](../Fermionic/PhysicalGaussian.lean), [`PhysicalGaussianRank`](../Fermionic/PhysicalGaussianRank.lean) |
| Enlarged parity dictionary | If claiming the original dictionary with both parities, define it and formalize deletion of all odd terms for an even target | [`FockParity`](../Fermionic/FockParity.lean) proves the present even-orbit membership |

None of these TODO results is to be introduced as an axiom or as an unexplained premise of a purported final root. In particular, neither “the normal family has a certificate” nor “polynomial identities extend across a boundary” by itself proves that all legal three-term Gaussian decompositions are covered.
