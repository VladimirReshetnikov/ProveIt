# Source and claim audit

## Repository snapshot

The GitHub connector was used to inspect ProveIt at revision
`526c2557f2c6173054794f873a9624ebef616510`.

Inspected source/documentation:

- `README.md`
- `Computability/HilbertTenthProblem/README.md`
- `Computability/HilbertTenthProblem/Lean/MRDP.md`
- `Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`

The public source directly states `Diophantine.mrdp`, `mrdp_iff`, and
`mrdp_dioph_iff`. In particular, it gives one finite integer polynomial and
one fixed finite natural-witness dimension for an enumerable set, including
input zero. The guide explicitly says that this interface does not supply
a practical polynomial generator or numerical degree/witness bounds.
This report uses that boundary and does not claim to have rerun Lean.

The branch advanced during the investigation. Later inspection showed commit
`e18718e837d43e162252f9a314e8cb797fbd1a1f` with the pinned revision above as its
parent. The article's repository citations intentionally remain pinned to the
inspected source revision, rather than referring to an evolving branch.

## External mathematical inputs

1. Minsky, Annals of Mathematics 74 (1961), Theorem Ia, p. 449.
   The original page was inspected as a PDF image. It uses increment and
   conditional decrement of two counters, with source input (2^e,0).
   This is why the report uses the explicit rational family
   (0, 2^(-2^e), 1, 1) and does not claim an efficient binary-input reduction.
2. The classical MRDP theorem, through the inspected ProveIt interface.

The contraction, exact simulation formulas, point-reachability algorithm,
peak-value results, integer scaling, canonical bounded quartics, and
regularity rigidity arguments are proved in the article rather than assumed
from another manuscript.

## Related-work checks

- Moore (1990) and Koiran--Cosnard--Garzon (1994): existing dynamical computation.
- Varonka--Watanabe, arXiv:2502.19923v1 (2025): point-to-point reachability,
  including positive Bellman-operator results. This is not the same target
  specification as the article's half-space problem.
- Bruera--Cardona--Miranda--Peralta-Salas--Salo,
  arXiv:2404.07288v3 (9 April 2026): positive-entropy criteria and examples
  of universal Turing machines with zero entropy. Therefore mere coexistence
  of universality and zero entropy is not presented as a new discovery.
- Korec (1996): small register-machine constructions, cited as a source for
  a proposed explicit-instantiation project, not as an unverified claim that
  a particular small machine has two registers or the exact required syntax.

The literature check is not a proof of historical priority. No claim that
this report solves a named, previously published open problem is made. It
does give full proofs answering the precise structural question formulated
in its introduction.

## Verification performed

Both Python programs ran successfully using exact integer/rational arithmetic.
The independent checker reconstructs the symbolic sum of squares and matches
it term-for-term to the exported quartic. It also verifies the supplied
natural assignment and all 400 one-coordinate witness mutations.

The PDF was compiled repeatedly until cross-references stabilized and rendered
page by page for visual inspection. The final article has no undefined
references or overfull boxes. Minor underfull-box typography warnings, if
present in a local rebuild, do not indicate missing content or formula errors.

No new Lean/Rocq proof was compiled. The universal instruction table is not
instantiated numerically. The displayed example is a finite non-universal
transfer program. The unbounded polynomial is supplied by a stated existence
theorem, not by the explicit bounded exporter.
