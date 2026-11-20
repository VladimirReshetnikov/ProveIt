# Finite observations in intuitionistic primitive recursive arithmetic

Read **report.pdf**. Its seven sections develop the interpretation, cyclic inference and stable quotient, finite finality, geometric and homological nerve comparisons, named-centre residues, square-root monodromy, and a formalization ledger. Section 1 includes the quantitative completion theorem. The table in the final section identifies the exact scope of the Lean files.

## Rebuild the report

Use a usual TeX Live installation with the standard mathematics packages. Run from this directory.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

All files that report.tex includes are beside it.

## Replay the proofs

The 12 Lean files use Lean 4.32.0. The object-derivation files use the ordinary `ConciseIPRA.PR` module of [ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/3ee850b4c2d650cf01263823fd5415963747c5d0/Logic/PrimitiveRecursiveArithmetic). Mathlib is the repository's locked revision `81a5d257c8e410db227a6665ed08f64fea08e997`.

In a checkout of ProveIt at the indicated commit with its Lake dependencies available, substitute the extracted packet's absolute path below.

```sh
lake exe cache get
lake build ConciseIPRA.PR
lake env bash /absolute/path/to/ipra_finite_observations/check_lean.sh
```

The script builds a temporary Merge.olean and removes the temporary directory on exit. It checks every supplied Lean source. During preparation the three imported ProveIt source modules were rebuilt from the pinned GitHub blobs before running the scripts. The file checks/lean.txt records the successful replay. No fully internal proof of a complete application theorem is claimed. The compiled ordinary-iPRA terms include finite rule replay, transport along a fixed path, and an incidence sequent. The remaining Lean implementation obligations appear with the corresponding human proofs.

## Replay the finite examples

The scripts require Python 3.10 or later and the standard library.

```sh
bash check_examples.sh
```

The ground-rule checker enumerates every system on at most two atoms and compares each proposed refinement against all stable partitions of the instance. The category example uses comparison maps and representables. The topology examples verify cycle transfer, dual obstruction functionals and finite naturality tests. The analytic example checks exact chain boundaries and rational enclosures for the residue. The examples are finite checks; the uniform arguments are in the report. See checks/examples.txt for the outputs.

## Contents

- Top-level TeX files and report.pdf make up the paper.
- lean/ contains the common closure, completion and quotient lemmas.
- categorica/ contains the merge, finality, path, and stable-refinement proofs and a diagram example.
- topologica/ contains the polarity, elementary-collapse and transfer proofs and the finite-cover checks.
- analytica/ contains the rational secant estimate, strip cancellation, and the named-pole example.
- examples/ contains the ground-rule generator, verifiers, and square-root graph example.
- checks/ records the exact local replay. SHA256SUMS lists the members of the packet other than the checksum file itself.
