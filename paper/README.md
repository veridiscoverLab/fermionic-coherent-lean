# Fermionic coherent states: convex order and Gaussian rank

[Read the English paper](output/pdf/fermionic-coherent-states.pdf)
or start with the [LaTeX source](main.tex).

The paper gives the exterior-power and spin-representation distribution
comparisons, their entropy consequences, the two-copy Gaussian-rank proof,
and measurement applications. Section 7 states the exact Lean coverage:
the exterior-power convex-order and entropy minimizer theorems are verified
end to end; the rank-four theorem, spin extensions, and explicit entropy
constants have paper proofs and remaining formalization work.

## Build the PDF

With a standard TeX Live installation containing `latexmk` and the packages
listed in `main.tex`, run from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

The result is `build/main.pdf`. The checked publication copy is
`output/pdf/fermionic-coherent-states.pdf`.
This command builds only the article. Lean and Lake execution must take
place on CAB over SSH as described in the
[verification instructions](../docs/verification.md).

The proof-source snapshot linked in the article is preserved at
[`3164a3`](https://github.com/veridiscoverLab/fermionic-coherent-lean/tree/3164a3243fcc6cd675fa8a7493282a1f650a16d8).
Adding the article does not constitute a new Lean verification run.
