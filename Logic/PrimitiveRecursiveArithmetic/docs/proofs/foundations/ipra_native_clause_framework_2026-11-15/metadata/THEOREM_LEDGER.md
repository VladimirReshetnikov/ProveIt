# Theorem ledger

Pinned repository: `VladimirReshetnikov/ProveIt` commit
`8649990597d73657bde480b6c389de7f85bc0cb0`.

Status vocabulary:

- **upstream checked**: theorem is already in the pinned repository's checked
  Lean library;
- **human complete**: a full mathematical proof is in the report;
- **executable evidence**: exact standard-library Python implements and tests
  the finite algorithm;
- **Lean candidate**: source is supplied but was not compiled here;
- **Lean blueprint**: exact definitions/signatures and completion route are
  supplied with explicit proof holes;
- **conditional**: generic verifier/finalizer is settled, but a theorem-specific
  producer remains a hypothesis.

| ID | Claim | Human | Python | Lean status | Notes |
|---|---|---:|---:|---|---|
| U1 | `KPrf.subst` specializes native clause proofs | upstream | n/a | upstream checked | `NativeClausalDiagonal.lean` |
| U2 | `KPrf.cut` discharges retained/proved clauses | upstream | n/a | upstream checked | compiler spine |
| U3 | `KPrf.toNPrf` translates to native kernel | upstream | n/a | upstream checked | export step |
| U4 | `kprf_iff_nprf` and Q-free specialization | upstream | n/a | upstream checked | completeness/equivalence |
| U5 | `native_iff_pra`, `pra_iff_native` | upstream | n/a | upstream checked | ordinary iPRA bridge |
| U6 | `IPRA.ind`, `IPRA.inst`, `ipra_ring` | upstream | n/a | upstream checked | direct derivation backend |
| C1 | finite list cut for generated assumptions | complete | n/a | candidate, no `sorry` | direct application of U2 |
| C2 | topologically ordered native DAG compiler | complete | host analogue | blueprint | induction using C1 |
| C3 | clause-to-iPRA export | complete | n/a | candidate, no `sorry` | U3 then U5 |
| C4 | iPRA-to-clause import | complete | n/a | candidate, no `sorry` | U5/U4 reverse route |
| B1 | characteristic term for fixed QF/bounded formulas | complete | partial analogues | blueprint | restricted AST recommended |
| B2 | clocked finite-trace invariant theorem | complete | tested | partial candidate/blueprint | direct backend uses `IPRA.ind` |
| B3 | least bounded search, positive and negative contracts | complete | tested | blueprint | trace specialization |
| B4 | complete bounded enumeration | complete | tested | blueprint | trace specialization |
| B5 | mixed-radix finite descent fuel | complete | tested | not yet encoded | fixed-dimensional box |
| B6 | common good finite window from exception budgets | complete | tested | not yet encoded | finite union bound |
| D1 | least reverse demand on a DAG | complete | tested | blueprint | monotone edge pullbacks |
| D2 | bounded least prefixed point for cyclic demand | complete | tested | blueprint | rank-sum termination |
| D3 | backward-demand/forward-replay recurrence | complete | demo components | blueprint | combines D1/D2 and B2 |
| R1 | finite backward viability and least path | complete | tested | blueprint | finite-horizon dependent choice |
| R2 | exact observer elimination | complete | tested analog | blueprint | branch invariant output |
| R3 | approximate observer elimination by diameter | complete | tested | blueprint | exact rational distances |
| R4 | coherent Cauchy estimate from motion tails | complete | tested | blueprint | finite triangle inequality |
| R5 | exact finite label recovery from positive gap | complete | tested | blueprint | no claim at collisions |
| H1 | height bound implies list; complete list implies height | complete | tested | not yet encoded | cardinality alone excluded |
| P1 | producer-verifier-finalizer factorization | complete design | host graph tested | compiler blueprint | producer may remain conditional |
| A1 | polynomial identity nodes via `ipra_ring` | upstream method | n/a | upstream checked backend | application adapter blueprint |
| A2 | fixed-dimensional Cayley-Hamilton route | developed outline | no theorem test | blueprint | needs matrix/determinant library |
| A3 | root/spectral cluster observer route | developed outline | cloud algorithms tested | blueprint/conditional | root-count producer required |
| A4 | finite topology/homology certificate route | developed outline | no domain code | conditional | finite bridge to ideal space required |
| A5 | Diophantine enumeration from height | complete generic part | tested | blueprint/conditional | height producer not generic |

## Explicit nonclaims

This package does not claim:

1. compilation of any new Lean module;
2. a checked generic graph compiler;
3. a universal primitive-recursive evaluator;
4. a general effective Faltings or Siegel theorem;
5. uniform Mordell-Weil representatives;
6. effective constants for all analytic-number-theory packets;
7. canonical root/eigenvector selectors through collisions;
8. that Python checks are object-language proofs;
9. verification of the existing proof-packet corpus.
