# Seeded closure kernels for a ZFC-inconsistency machine

Research memorandum for Vladimir Reshetnikov — 15 October 2026.

Start with **article/seeded_closure_zfc.pdf**. The self-contained LaTeX source
includes the bibliography. This package extends the supplied
`zfc-consistency.zip` and the closure principle in MathOverflow question 380000.

## Main result

Let `K(y,b)` mean `y in b OR y subset b`. For every definable binary relation
`rho(x,y)` whose outputs at each fixed input have a K-bound, require a set C
such that:

1. Every output from an initial input or an input in C belongs to C.
2. Every member of C is an output of rho at some input.

The initial inputs are either the single object a (the test `x=a`) or all
subsets of a (the test `x subset a`). Both seed tests are reflexive without
any set-existence assumptions.

The report proves that each of the following is deductively equivalent to
ZF_0, explicitly defined as ZF without Foundation and Choice and with
functional Replacement, not unrestricted Collection:

- T_pt: Extensionality + point-seeded bounded-image closure.
- T_sub: Extensionality + subset-seeded bounded-image closure.

Empty Set, singletons, Separation, Power Set, Pairing, Union, Replacement,
and Infinity are all derived. The reverse construction iterates **unique
exact fibers**, avoiding an unjustified choice of local bounds. With the
standard effective Foundation/Choice reductions, these are PA-equiconsistent
with ZFC. They have one fixed axiom and one infinite schema, not a finite
first-order axiomatization.

A direct equality-free competitor Q_sub replaces Extensionality by one
member-profile congruence sentence. Its calibration translates equality
into equality of predecessor profiles and does not require raw bisimulation.
The report also proves two subsidiary closure calibrations and identifies
simplifications that remain open.

## Reproducible comparison

In the explicitly declared formula-tree metric (not TM states):

| Candidate | Nodes |
|---|---:|
| T_pt | 69 |
| T_sub | 72 |
| Extensionality + nonempty membership + iterated subset images | 76 |
| Earlier RCC (container + global-image collection) | 80 |
| Q_sub, equality-free | 83 |
| Extensionality + Separation + subset-bounded root closure | 83 |
| MathOverflow set-seeded control without Foundation/Choice | 107 |
| Earlier Extensionality + Infinity + subset-bounded images | 131 |

Variable payloads, arbitrary parameter closure, logical equality machinery,
proof-engine costs, and TM compilation are excluded. The code reports the
full metric definition and all expanded templates. Close rankings are not
predictions of final state counts.

## Reproduction

From this directory:

```sh
python3 build.py --tests
```

For Python results without a TeX installation:

```sh
python3 build.py --tests --skip-pdf
```

Python 3.10+ and its standard library suffice for the experiments. The PDF
build uses `pdflatex` and standard packages named in the article preamble.
Run without `python -O` or `PYTHONOPTIMIZE`; assertions implement the tests.
No network access is needed. Temporary output is confined to `.build/`.

The deterministic tests include every directed graph on 1–4 vertices,
positive-orbit closure checks, hereditarily finite switching constructions,
singleton decoding, formula expansion checks, and finite deletion
countermodels. Exact executed counts are in `results/experiments.json`.

## Status and limits

The mathematical proofs and their uniform syntactic calibration arguments
are in the article. **This archive does not include a formal PA proof object,
a derivation compiler, a proof assistant development, a newly compiled
Turing machine, or a claimed state-count improvement.** The finite checks
are regressions, not substitutes for the proofs.

The externally reported 254-state construction is discussed with a pinned
commit and an explicit verification boundary. Its Coq build and complete
table hash were not independently rerun here; it does not remove the need
to certify the user's PA endpoint.

See `notes/PA_OBLIGATIONS.md`, `notes/DELTA.md`, and
`provenance/sources.json`. `SHA256SUMS` records the release files; rebuilding
the PDF may change its digest through TeX timestamps or tool versions.
