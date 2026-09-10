# Project instructions

This repository contains two related formalization efforts: the completed
basic exterior-power Husimi/entropy theorems and the partial eight-mode
Gaussian-rank proof. Preserve the original objects, full quantifiers, and
equality cases. Do not replace a missing bridge by an assumption or an axiom.

All Lean/Lake execution and compilation must take place over SSH on an
authorized CAB server. The recorded runners are pinned to CAB17, hostname
`CAB-Lab-Server-8`, and directories under `/home/dzheng/remote_builds/`.
Never run Lean/Lake or create build caches on the local machine. Existing
remote package caches are read-only.

The recorded evidence binds exact source and verifier bytes. Preserve those
records; changes to proof sources require new verification evidence. A source
integrity check is not a new kernel replay. Keep paper-level derivations and
unfinished formalization obligations explicit in the English documentation.

No admissions, new mathematical axioms, native-evaluation proofs, or hidden
proof interfaces are permitted. Pinned, kernel-checkable mathlib dependencies
and the disclosed Lean logical axioms are allowed.
