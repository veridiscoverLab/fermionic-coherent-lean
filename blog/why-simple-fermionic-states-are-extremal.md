# Why Simple Fermionic States Are Extremal

*A probability law, a two-copy rank theorem, and the shared structures that make both proofs work.*

Some quantum states have an enormous description even when they are built from only a few modes. Others have a compact structure: specify which one-particle modes are occupied, or how pairs of modes are coupled, and the whole state follows. Understanding the boundary between these classes matters both for quantum physics and for the mathematics of classical simulation.

Our preprint, [*Fermionic coherent states: convex order and Gaussian rank*](https://github.com/veridiscoverLab/fermionic-coherent-lean/blob/a7ce34b2c31eacb378780d9ce6027b065b969a50/paper/output/pdf/fermionic-coherent-states.pdf), studies two ways in which simple fermionic states are extremal. It compares their entire distributions of overlaps, yielding entropy minima for several infinite families of representations. It also proves that two copies of a particular four-mode state require exactly four Gaussian summands, even when the summands can couple the two copies.

The useful mathematics lies in the proofs. In the distribution problem, one set of probability weights works for every measurement direction at a given stage. In the decomposition problem, one change of coordinates acts on every summand together. Both constructions preserve the relations that make a local simplification relevant to the original question.

Start with two fermions and four available modes, labeled $1,2,3,4$. A state occupying modes $1$ and $2$ is written $e_1\wedge e_2$. The wedge records antisymmetry: exchanging the two factors changes the sign. More generally, occupying any two orthogonal one-particle modes gives a **Slater state**. These are the coherent reference states for the fixed-particle problem.

Now consider

$$
\psi=\frac{e_1\wedge e_2+e_3\wedge e_4}{\sqrt2}.
$$

This is a coherent superposition of two occupation patterns. No change of one-particle basis turns it into a single Slater state. A short algebraic test already detects the difference: the exterior square of a decomposable two-vector is zero, whereas $\psi\wedge\psi\ne0$.

There is also a probabilistic way to examine the difference. Choose a reference Slater state $\Omega$ at random by applying a uniformly random unitary rotation to its modes. For a unit input $\psi$, record its squared overlap with that reference, $Q_\psi=|\langle\Omega,\psi\rangle|^2$. More generally, a density operator $\rho$ is the matrix describing a quantum state, including probabilistic mixtures. Its corresponding quantity is $Q_\rho=\langle\Omega,\rho\Omega\rangle$. This is the **Husimi measurement value**. Repeating the random choice produces a distribution of numbers between zero and one.

The average is the same for every input: it is $1/D$, where $D$ is the dimension of the state space. The shape of the distribution contains the interesting information. Already for one particle in two modes, a pure input gives a uniform distribution on $[0,1]$, while the maximally mixed input gives the constant value $1/2$. Both have mean $1/2$, but their second moments are $1/3$ and $1/4$.

Our distribution theorem extends this comparison to every continuous convex test function:

$$
\mathbb E\,\Phi$Q_\rho$
\le
\mathbb E\,\Phi$Q_{\mathrm{coherent}}$.
$$

A convex function rewards spread around a fixed mean; $\Phi(t)=t^2$ is the simplest example. Requiring this inequality for every such function is called **convex order**. The theorem compares the full distributions through this collection of tests. Their tail probabilities can still cross: in the uniform-versus-constant example, the constant exceeds $1/4$ more often, while only the uniform variable can exceed $3/4$. For each strictly convex test, equality identifies the input completely: it must be a pure coherent state.

This also explains a potentially confusing use of “concentration.” The normalized outcome density on the reference space is $f_\rho=DQ_\rho$. A localized density takes large values in some places and small values elsewhere; its values fluctuate when the reference space is sampled uniformly. A flat density has no such fluctuations.

Wehrl entropy measures the spread of this outcome density. In the paper's convention it is

$$
S_W(\rho)=-D\,\mathbb E[Q_\rho\log Q_\rho],
$$

where the expectation uses the uniform reference measure, logarithms are natural, and $0\log0=0$. This differs from the usual differential entropy of $f_\rho$ by the fixed additive constant $\log D$. Thus it is the distribution of measurement outcomes whose entropy is minimized; the random numerical values $Q_\rho$ enter through a convex test.

That test is $t\log t$. The same theorem also handles every positive real-order Rényi–Wehrl entropy, which is defined from the moment $\mathbb E Q_\rho^q$: use $t^q$ when $q>1$, and $-t^q$ when $0<q<1$. The change of sign agrees with the change of sign in the entropy's normalization. One comparison therefore gives a continuum of entropy inequalities, with the same equality cases.

The entropy question has a substantial history. Gnutzmann and Życzkowski formulated a generalized Rényi–Wehrl conjecture in 2001. In 2002, Sugita proved coherent-state optimality for integer orders $q=2,3,\ldots$ in the compact semisimple-group setting, including mixed inputs and the characterization of equality. Lieb and Solovej subsequently established a full convex-function comparison for symmetric $\mathrm{SU}(N)$ representations in their 2015–2016 work. [Gnutzmann–Życzkowski](https://arxiv.org/abs/quant-ph/0106016), [Sugita](https://arxiv.org/html/nlin/0208007v4), [Lieb–Solovej](https://arxiv.org/html/1506.07633v2).

The present paper proves the full distribution comparison for **all basic exterior powers**, the state spaces of $p$ fermions in $n$ modes, for every $0\le p\le n$. It also proves the corresponding statements for both fundamental half-spin representations and the fundamental odd-spin representations. These spin families allow a larger class of coherent reference states: pure fermionic Gaussian states, which can include pairing and superpositions of different particle numbers. Their parity is fixed: all particle numbers present are even, or all are odd. The results give every positive real-order Rényi–Wehrl minimum, the Wehrl minimum, and their equality cases in the stated families. This settles those basic fermionic cases of the programme dating to 2001–2002. Arbitrary representations and higher multiples of their highest weights are outside the theorem's scope.

The main mechanism can be understood without representation theory. Resolve one occupied mode $u$ in a random Slater reference. The squared overlap factors as $Q_\rho=a(u)Q_{\rho_u}$: the occupation probability $a(u)$ multiplies a Husimi value for the normalized conditional state $\rho_u$ with one fewer particle. The second piece belongs to the same kind of problem in a smaller space. If the occupation probability is zero, the original overlap is zero and that branch contributes nothing.

That observation suggests induction, but it does not finish the proof. The conditional state depends on the direction chosen, and so does the occupation probability. A comparison assembled separately in each direction could lose the compatibility needed to recover one global inequality.

The decisive step is to describe all these occupation probabilities using a single mixture. The input has a one-particle density matrix $\gamma$, whose eigenvalues are occupation numbers between zero and one. In an eigenbasis of $\gamma$, read the probabilities $t_S$ of the full input's occupation patterns. Each pattern $S$ determines an occupied subspace and its orthogonal projection $P_S$. Then

$$
\gamma=\sum_S t_S P_S,
\qquad
a$u$=\sum_S t_S\,\langle u,P_Su\rangle.
$$

The weights $t_S$ are chosen once for the current input and work for every unit mode $u$. At the next induction stage, its conditional input can have different weights. All the projections at a given stage have the same rank, so their readouts have the same distribution under a uniform random direction. Jensen's inequality can now compare the full mixture to a single Slater reference. Conditional Slater states remain Slater, which ensures that the comparison also agrees with the induction in the smaller space.

The one-particle matrix is sufficient for this part of the argument, but the proof retains the full conditional state. This distinction is essential. The superposition $\psi$ above and the equal probabilistic mixture of its two Slater components have the same one-particle matrix, $\gamma=\tfrac12 I$, yet different overlap functions. At the Slater reference occupying $(e_1+e_3)/\sqrt2$ and $(e_2+e_4)/\sqrt2$, their Husimi values are $1/2$ and $1/4$, respectively. The interference survives in the conditional state even though it disappears from the one-particle matrix.

Strict equality provides another useful piece of knowledge. If two different occupation patterns carry positive weights, some open set of measurement directions distinguishes their projections. Strict Jensen then produces a strict gap. Equality leaves only one occupied pattern, and positivity of the original density operator forces every other matrix entry to vanish. A distributional equality has recovered the entire quantum state.

For the spin representations, a Majorana covariance matrix plays the role of $\gamma$. This matrix records quadratic expectations of the fermionic operators. After a suitable rotation, its decomposition again uses probabilities taken from the diagonal of the same full density operator. They represent all rotated-mode occupation probabilities simultaneously, within the specified parity sector. The companion geometric fact is that a nonzero occupation projection of a pure Gaussian state remains Gaussian after the measured mode is removed.

These facts explain why the comparison extends beyond fixed particle number. The reusable mechanism consists of an exact conditional measurement, one common mixture for its normalization probabilities, and a class of reference states closed under conditioning. Jensen's inequality itself is classical. The substantive work is proving that these ingredients fit the original measurement and attain equality together.

The resulting knowledge extends beyond an entropy bound. For coherent inputs, the successive conditional overlap factors are independent and have explicit Beta distributions. A Beta distribution is a probability law on $[0,1]$; its parameters describe how strongly it favors the middle or the ends. In the two-particle, four-mode example, the coherent overlap has the law of a product of independent $\operatorname{Beta}(2,2)$ and $\operatorname{Beta}(1,2)$ variables. This gives its moments at every positive real order and yields a coherent Wehrl entropy of $17/12$, compared with $\log6$ for the maximally mixed state.

The same comparison supplies quantitative consequences. Fractional occupation numbers give an explicit lower bound on the excess Wehrl entropy. It also determines the information capacity of the coherent measurement. When that fixed measurement is repeated, entangled joint inputs do not increase its capacity beyond the sum of the single-use capacities. Here the lower-dimensional conditional object is a density operator for the remaining measurements, so the entropy bound can be applied successively to the actual joint input.

The second main problem concerns exact sums. A pure fermionic **Gaussian state** is generated from an occupation state by transformations arising from quadratic fermionic operations. Such states can contain pairing and superpositions of particle numbers while keeping a definite parity. The **Gaussian rank** of a nonzero vector is the smallest number of Gaussian vectors needed to express it exactly, with arbitrary complex coefficients.

Consider the four-mode state

$$
M=\frac{|0000\rangle+|1111\rangle}{\sqrt2}.
$$

The two terms are Gaussian; their superposition is not. Thus $M$ has rank two, and expanding $M\otimes M$ immediately gives four Gaussian terms. The difficulty is excluding three more complicated eight-mode terms whose unwanted amplitudes cancel. Those terms are allowed to pair a mode in the first copy with one in the second.

Cudby and Strelchuk posed this unrestricted two-copy problem in 2023. Their paper proves rank four under symmetry restrictions on the summands and reports numerical searches for unrestricted decompositions; the conjecture remains explicitly stated in its September 2025 revision. Our paper gives a proof of the exact two-copy statement without those restrictions. This is a specific problem in fermionic quantum information, with a shorter history than the entropy programme. [Original 2023 statement](https://arxiv.org/html/2307.12654v1#S6.SS1), [revised statement](https://arxiv.org/html/2307.12654v4#S6.SS2).

The obstruction is a homogeneous polynomial of degree eighteen, denoted $P_{18}$. A polynomial equation can recognize a limitation that is hard to see from individual amplitudes. For comparison, the determinant vanishes on every $2\times2$ matrix of rank at most one; one nonzero determinant rules out all rank-one factorizations at once. Here $P_{18}$ vanishes on every sum of three eight-mode even pure Gaussian vectors. Its value on the target is nonzero. Allowing odd Gaussian summands cannot evade the test: in a decomposition of an even target, all odd terms sum to zero and can be removed.

The construction uses the algebra of Majorana operators, the elementary fermionic operators whose quadratic combinations generate Gaussian transformations. Eight modes give sixteen Majorana operators, hence $\binom{16}{2}=120$ independent quadratic directions. Apply all of them to the state and retain their pairings in one bilinear Gram operator; traces of its powers produce the polynomial. Under an allowed common change of coordinates, the polynomial is multiplied by a nonzero factor. Whether it vanishes is therefore preserved. This is the precise property needed to simplify a proposed decomposition while retaining the equation it is supposed to satisfy.

There is a further step that matters as much as finding the polynomial. Convenient coordinates can fail at exceptional configurations, and an exact decomposition might occur precisely there. The proof puts two summands into a common normal form, then places the third in a polynomial family passing through its original value. Away from the zero set of a nonzero polynomial, that family lies in a chart where the certificate can be evaluated explicitly. The resulting vanishing identity extends to the exceptional parameters because it is an identity of polynomials. This returns to the original third summand and covers the degenerate configurations as well.

The theorem also gives a broader result: for any two nonzero four-mode even-parity vectors,

$$
\chi_G$\psi\otimes\phi$=\chi_G$\psi$\chi_G$\phi$.
$$

Each factor has rank one or two, so two non-Gaussian factors always require four terms. This includes the alternative four-mode magic state studied in Cudby and Strelchuk's approximation experiments. The conclusion concerns exact representations; it does not determine the best error achievable with three terms. Nor does the two-factor theorem establish rank $2^k$ for $k\ge3$: after combining two factors, one has an eight-mode input, beyond the four-mode hypothesis needed to apply the theorem again.

The [Lean repository](https://github.com/veridiscoverLab/fermionic-coherent-lean) records a separate verification boundary. The exterior-power convex-order theorem, its strict equality cases, and its Wehrl and positive-order Rényi–Wehrl minimizer theorems are verified end to end on the actual exterior-power representations and Haar measurement. Their explicit Beta and Gamma evaluations are currently paper proofs. The spin extensions and applications are also paper proofs. For Gaussian rank, Lean verifies the original eight-mode rank bounds $2\le\chi_G\le4$ and the finite-coordinate certificates; the rank-four conclusion still requires the geometric identifications and reductions to be formalized. The development uses the disclosed standard Lean logical foundations, with no added mathematical axioms or admitted proofs.

The paper contributes two concrete ways to retain the information a proof will need later. Common occupation weights allow a smaller conditional problem to control a complete overlap distribution, while preserving enough information to characterize equality. A common polynomial invariant allows an exact decomposition problem to survive coordinate changes and exceptional configurations. Together, these results give both new extremal theorems for fermionic states and explicit structures for understanding why those theorems hold.
