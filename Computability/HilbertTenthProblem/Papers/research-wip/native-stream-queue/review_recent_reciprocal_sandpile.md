# Scoped review of the batch83 reciprocal sandpile/turmite notes

**PASS; no mathematical finding in the added text.** The patch adds attribution,
provenance and boundary pointers. It neither changes a certificate nor supplies
a new universal loader, a fixed-arity collapse or a lower paid operation bound.

## Exact reviewed revision and scope

Reviewed commit: `8c5831d558cd274ca45dd37c6097216b542bf859`, including its complete
six-file textual patch against its parent. The three accompanying binary PDF
changes were inventoried only; I did not render them or reproduce the reported
LaTeX builds/page counts. No archived or predecessor software was run, no
physical loader graph was rebuilt, and no repository file was edited.

All paths in the tables below are Git blobs at that exact revision, not a
promise about later working-tree bytes. The corresponding checked working-tree
files were byte-identical during this review. Prefix `reports/` abbreviates
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/`.

| Changed text file | SHA256 at the reviewed revision |
|---|---|
| `reports/quadratic-orthant-certificates/README.md` | `9aba292c88d30e71ac79f14f44b43a53b3a306aed2b67818be9d8b57bd0f5a8b` |
| `reports/quadratic-orthant-certificates/article.tex` | `9f1f45218ab034501a76fd40bfec6721bc2ff67d664a81338d83f500565b6015` |
| `reports/group-theoretic-substrates/README.md` | `d39db54cf67c0ded7ec7f9c585026cb06aac209bf87c8a9221c20222bad4d328` |
| `reports/group-theoretic-substrates/article.tex` | `44d86c130478c707833d97e51aeb6a294e8d9e77c79a690a42165090abaf4896` |
| `reports/canonical-diophantine-certificates/README.md` | `02b71df3bc1a1bbb7bcb4e8d79f1650415bcb86bc631a332b80011b25274215d` |
| `reports/canonical-diophantine-certificates/article.tex` | `b42dfaab43febff58dbbac9f3ef081b7b9bf65fc0dde2e1b941b0de46d9db453` |

The mathematical context read was limited to the cited propositions and
local proofs: QOC strong selectors and trace integrality, its parity-ray
obstruction; CDC literal loader statement/domain, real-exactness and finite
predecessor argument, and its real-algebraic restriction; Report38's no-reduction
corollary/proof and open question3. The prior research intake and the U15
provenance/dependency passages were also checked. This does not constitute a
fresh audit of the complete consolidated manuscripts.

## Findings and boundaries

1. **The real-algebraic inference is correct.** For one real free input n and a
   fixed finite semialgebraic witness interface, projection gives a semialgebraic
   subset of the real line. It is eventually constant on positive integers.
   Agreement between real and natural witness existence at every integer input
   therefore yields a finite or cofinite recognized set. Full equality of fibers
   is unnecessary. This is the same standard projection argument as QOC's parity
   ray obstruction. The new attribution does not turn it into an obstruction to
   natural-only packing, integer outer selectors or growing prism arity.

2. **Report36 remains a fixed-prism theorem.** Natural initial heights, exterior
   stability and a nonempty finite prism are retained hypotheses. Binary activity
   plus finite predecessor rigidity forces integral ranks; it does not assume
   them. The complete nonnegative-real zero set then equals the original natural
   zero set. The extra fk/fc terms were already present in the collected support;
   “no new monomial” is correct and does not mean unchanged coefficients or zero
   additional evaluation cost. This does not transfer the theorem to arbitrary
   signed witnesses or to the entire positive real orthant after a minus-one shift.

3. **The U15 pointer is supported.** The provenance literally identifies the table
   as supplied from the prior matrix-semigroup construction. The QOC table has
   SHA256 `0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a`.
   I also compared it directly with the inert archived Report35 member
   `Research_Report35/evidence/loader/data/u15_table.json`: the bytes are equal.
   The archive was read from historical Git revision
   `7f9672c599194e150dee64ebaa0b19f0e035ba15`, path
   `docs/incoming/Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package.zip`,
   SHA256 `3202b1f0430353a3cd05f15ac6f34e9a797ed931d9a86e3580a110d97b01a12d`.
   Neither the identical table nor either finite-tape interface implements the
   imported arbitrary-program-to-U15-tape compiler. The notes say so.

4. **The turmite lower side has the correct quantifiers.** The corollary excludes
   computable undecidable-language reductions whose every output is a globally
   one-visit finite-defect periodic run and whose acceptance query belongs to the
   stated finite observation language. It does not cover unrestricted turmites,
   arbitrary post-revisit observations or a two-visit universal loader. Sandpile
   finite total activity and turmite observation events are different interfaces;
   the sandpile one-shot property does not transfer a turmite theorem. “No shared
   theorem” and the open literal-loader question are accurate.

Consequently the reviewed finite-prism cubic family, its separately paid shared
arithmetic schedules, and the fixed-lane turmite component retain their existing
scope. The sound84 universal polynomial is unaffected. This patch supplies no
new first-hit-minimality certificate, no fixed witness count for unbounded prism
computation, and no newly audited arbitrary-program encoder.

## Additional context pins

| Context file | SHA256 at the reviewed revision |
|---|---|
| `reports/periodic-turmite-first-revisits/article.tex` | `73ddd33558c615c07d95be5e8b29088995e65a79a46a699a14b0f24ca4193d10` |
| `reports/quadratic-orthant-certificates/data/16-universal-membrane-tm_table.json` | `0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a` |
| `reports/canonical-diophantine-certificates/data/22-literal-sandpiles-evidence-loader-PROVENANCE.json` | `340b750ddc359f8f143aa0a433332f93dacb2790d484efb676f59e95a40067c1` |
| `reports/group-theoretic-substrates/08-matrix-semigroup-core-loader-audit-U15_DEPENDENCY_AUDIT.md` | `e8121b79d24eabb025bf74b144cc6517f084b26992b2b9c4b4ace47c62f070f5` |
| `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_sandpile35_36_intake.md` | `31469beadaded552603a77e6c3db2876e812ffd2f465f7017be6001c3c2bce97` |

No broader publication, priority, release-integrity or executable audit is
claimed. The result is a read-only mathematical/provenance check of this patch.
