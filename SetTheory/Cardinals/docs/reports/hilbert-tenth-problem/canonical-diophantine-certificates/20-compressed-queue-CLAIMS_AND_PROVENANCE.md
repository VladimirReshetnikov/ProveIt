# Claims, dependencies, and provenance

## Mathematical claims proved in this manuscript

Theorem 5.1 gives the finite FIFO grammar compiler and its exact dimension,
residual, degree, and empty/singleton-fiber statements. Theorem 7.1 gives the
exact repetition count; Theorem 7.2 gives the finite conjugacy criterion for
indefinite repetition. Theorem 8.2 gives the finite pumping threshold.
Theorem 9.1 gives the ordinary quartic infinite-loop compiler. Theorem 10.2
gives a quasi-Diophantine powered-schema compiler with explicit power predicates.
Theorem 11.1 extends the construction to multiple channels. Theorem 12.2
rules out a total computable bound on accepting trace grammar size, and
Theorem 12.3 rules out completeness of ultimately periodic transition lassos
for universal divergence. Consult the article for every hypothesis.

These are proofs offered for mathematical scrutiny, not independent peer review
or a proof-assistant build. Elementary components intentionally overlap known
queue, word, and arithmetic techniques. Novelty of the exact combined compiler
is proposed, not certified. No claim that loop decidability itself is new is made.

## Precise semantic scope

- Variables range over natural numbers including zero; uniqueness over all
  integers is not asserted.
- Actual queue words or validated word grammars are supplied. Arbitrary numbers
  cannot simply be declared radix encodings.
- A full transition-label grammar is prescribed. Schedule synthesis is not solved.
- Every atomic step reads its complete read word before writing its output.
- Control adjacency is explicitly checked, not inferred from content equations.
- Infinite-loop certificates concern a fixed closed transition macro, including
  read labels. Mere periodicity of the program's phase counter does not suffice.
- The total-read-empty case is separate and always repeats at a closed controller.
- Degree and variable count do not imply small binary natural-number witnesses.
- Powered schemas with variable exponents retain the power predicates explicitly.
  Only fixed-exponent expansion is claimed to give the same kind of ordinary
  unique-witness quartic without additional arithmetic assumptions.

## Repository source audit

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `44983ed7ebfd545de55bfdb50e040c82f3d24295`.
Its commit API endpoint was read and confirmed the object is a commit.
Its root tree is `ecc70fbdbdb6b3b58d7dd8ce4a17b1f944aa39ea`.
Commit timestamp: 2026-10-02T21:30:10Z.

Relevant files inspected through the GitHub connector:

1. `SetTheory/Cardinals/docs/reports/README.md`: collection scope and status.
2. `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md`:
   catalogue and queue-predecessor contribution summary.
3. `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/07-queue-causality-lean_integration.md`:
   word semantics, FIFO reconstruction, polynomial and uniqueness obligations,
   and the explicit notice that that integration proposal is not implemented.
   Blob SHA: `019f1bb2cff40c88f4f7ea93504afdf74eb07c05`.

The directory listing identifies the merged `article.tex` as 1,456,594 bytes
(blob `95f1a6cbd9978a721ec498efcba4a716b72324f1`). Retrieval through the available
interface failed because of size. Its full body was not audited. No exhaustive
repository-wide nonduplication guarantee is made. In particular the new article
explicitly builds on, rather than claims priority over, the described per-step
queue certificates and causal FIFO reconstruction.

No repository write, commit, pull request, Lean build, or modification was made.

## Established external dependencies and prior art

- Huschenbett, Kuske and Zetzsche, *The monoid of queue actions*, arXiv:1404.5479:
  established queue-action algebra and normal-form context.
- Köcher, *Reachability Problems on Reliable and Lossy Queue Automata*,
  Theory of Computing Systems 65 (2021), 1211–1242,
  DOI 10.1007/s00224-021-10031-2: queue universality context and existing
  single-loop and generalized acceleration literature.
- Rankin, *Fine-Wilf graphs and the generalized Fine-Wilf theorem*,
  arXiv:0906.1780: classic two-period theorem and attribution. The article
  supplies a self-contained proof of the version it uses.
- Jeż, *Faster fully compressed pattern matching by recompression*,
  arXiv:1111.3244: external compressed-word algorithmic input to Corollary 12.1.
- Cook, *Universality in Elementary Cellular Automata*, Complex Systems 15
  (2004), 1–40; Woods and Neary, *On the time complexity of 2-tag systems
  and small universal Turing machines*, arXiv:cs/0612089: established universality
  and simulation context, not part of the newly tested compiler.
- The classical MRDP theorem is invoked only to explain existence-level
  uniformization and the danger of inferring fiber preservation from it.

These sources are cited in the article. None supplies a claim that the exact
new compiler constants have been proved optimal or are historically first.

## Validation actually performed

`python code/verify.py`: PASS, 259,025 exact assertions, Python 3.13.5,
fixed random seed 20261002. Counts and domains are recorded in the receipt.
The 17-node doubling grammar represents 65,536 actions; its quartic has 151
variables, 153 residuals, 504 collected monomials, and a 103,873-bit root scale.

Two sparse polynomial exports were independently checked for exact equality to
the sum of the exported residual squares, degree, natural witness validity and
zero evaluation. This independent checker does not import the compiler.

The PDF was compiled with LaTeX and rendered for visual inspection. Numerical
checks and successful compilation are not substitutes for the general proofs.

## Non-claims

No solution of a named longstanding open problem, certified breakthrough
priority, universal single-fold/finite-fold MRDP theorem, complete nontermination
certificate system, polynomial bound on numeric witness bit lengths, or native
compiler for every Turing-equivalent substrate is claimed.
