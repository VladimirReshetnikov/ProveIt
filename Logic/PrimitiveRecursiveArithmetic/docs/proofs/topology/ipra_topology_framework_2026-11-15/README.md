# Certified Observation Towers for iPRA

Research package prepared for Vladimir Reshetnikov, 15 November 2026.

## Start here

- `paper/ipra_topology_framework.pdf` - complete 36-page human-readable report.
- `paper/ipra_topology_framework.tex` and `paper/sections/` - full LaTeX source.
- `THEOREM_LEDGER.md` and `PROOF_STATUS.json` - exact claim status.
- `lean/README.md` - ordered Lean/object-iPRA completion plan.
- `code/topology_kernel.py` - exact finite reference implementation.
- `validation/python_tests.txt` - 15 passing unit tests.

## Main contribution

The package extends the repository's finite-contract and finite-observation
methods with **certified observation towers** and **strong simplicial
carriers**.

At each precision, a mathematical object is observed through a finite
simplicial complex. A refinement or map does not have to choose one target
cell at a boundary. It returns a nonempty finite cloud. The strong carrier
condition says that the union of all clouds over a source simplex is a target
simplex. From that condition the report proves:

1. carriers compose by finite relational union;
2. every deterministic selection is simplicial;
3. every two selections are contiguous;
4. an explicit finite prism operator gives `dP + Pd = f + g` over `F_2`;
5. induced homology maps are independent of all finite tie-breaking;
6. coherent tower maps act functorially on inverse systems of finite homology.

This provides a common language for finite covers, maps, compactness data,
chart overlap, Jordan parity, dimension obstructions, root/eigenvalue
clusters, and other choice-sensitive constructions.

## Topology covered

The report gives developed formulations and proof plans for:

- finite topological spaces as preorders, with continuity equivalent to
  monotonicity;
- finite nerves, cover refinement, and pointfree open information;
- products, subspaces, quotients, separation, chain connectedness, and paths;
- mod-2 homology, integer-homology certificates, cohomology, and bounded
  fundamental-group certificates;
- compact metric presentations and finite-cover contracts;
- manifolds through finite charted exhaustions and overlap carriers;
- approximate fixed-point arguments;
- integration with the existing constructive Jordan and dimension-invariance
  packets.

## Formalization status

The report contains complete human proofs of the core finite theorems. The
Python implementation is exact finite regression evidence. It is **not** an
iPRA proof checker.

The two Lean files are **uncompiled blueprints**. The build environment had no
Lean executable. They contain explicit `sorry` obligations and no user-defined
`axiom`. The object-language file targets the repository's actual declarations
`PR`, `PTm`, `PRAAx`, `PRA.qfInd`, `Prf`, `NFm.ofPRA`, and
`pra_iff_native`. No semantic Lean theorem is presented as an object-iPRA
proof.

## Reproduce

```sh
./build.sh checks
./build.sh paper
./build.sh all
```

The Python code uses only the standard library. The PDF build needs a normal
pdfLaTeX installation with AMS, Latin Modern, microtype, TikZ, listings,
booktabs, longtable, xurl, hyperref, and cleveref.

## Repository baseline

The targeted source review is pinned to ProveIt commit
`c88269a745aedaca1235895c4d5e3e97056a1636`. It is a focused audit of the
PRA backend, the principal foundational frameworks, and the two topology
packets; it is not a blanket verification of every proof packet.

## Package boundaries

The framework does not manufacture a missing modulus, separation gap, finite
exhaustion, height bound, good-cover contraction, or ineffective analytic
constant. It does not claim completed object proofs of the Jordan theorem,
dimension invariance, invariance of domain, or a general nerve theorem. Those
are theorem-specific modules built on the common finite kernel.
