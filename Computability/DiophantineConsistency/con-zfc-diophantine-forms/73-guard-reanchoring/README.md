# Reanchored sign constraints and adaptive Pell carriers

This contribution gives explicit Diophantine equations whose unsolvability
is equivalent in ZFC to the repository's syntactic `Con(ZFC)`, by ordinary
mathematics composed with the identified inherited compiler/refutation
proofs. The primary proposal is a **sextic in 34 unrestricted integers**.
Two companion constructions improve the degree of the current equations
in thirteen and twelve strictly positive integers.

**Start with [report.pdf](report.pdf)**. Its self-contained source is
[report.tex](report.tex). The report includes every polynomial definition,
proofs of the new reductions, the compact coefficient recipe, exact degree
certificates, proof dependencies, and reusable research lemmas.
No new end-to-end Lean/Rocq certificate or internally encoded ZFC
derivation is claimed.

## Results

The comparison is pinned to ProveIt commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4` (23 October 2026), including
proposal directories 60–67, rather than only the older overview frontier.

| Equation | Domain | Unknowns | Exact degree | Live binary operations | Change |
|---|---|---:|---:|---:|---|
| Compact S34 | unrestricted integers | **34** | **6** | not optimized | 35 → 34 integers at degree six |
| Adaptive P13 | strictly positive integers | **13** | **30** | **92** | degree 34 → 30; operations 93 → 92 |
| Centered P12 product | strictly positive integers | **12** | **110** | **105** | degree 118 → 110; one more operation |
| Centered P12 SOS | strictly positive integers | **12** | **164** | **104** | degree 172 → 164; one more operation |

An operation is a live binary `+`, `-`, or `*`, including multiplication by
a fixed numeral and each squaring. Register reuse and numeral leaves are
free. This is a literal circuit ledger, not a minimal-circuit claim.

The collection already has nine-positive-variable and
ten-unrestricted-integer equations of much higher degree, as well as
a quartic in 41 integers. These remain distinct tradeoffs. This work
does not establish a global minimum or a fewest-variable record.

## Preferred exact equation

Use **[integer34/sextic34_compact.json](integer34/sextic34_compact.json)**.
It lists the 34 integer coordinates, nineteen residuals, the single
sum-of-squares finalizer, and the complete fixed-port binding.

Every residual has degree at most three. The exact coefficient
`[r^2*c^4] S34 = 4` proves degree six independently of all fixed ports.
The full symbolic expansion has 437 monomials when the ports are
independent symbols.

The key reduction reanchors the common-sign guards:

    F*alpha > 0 and F*C > 0
       iff
    C*alpha > 0 and F*C > 0.

After replacing `alpha` by `C=q-F-alpha`, the transport equation becomes
monic in `F`. Eliminating `F` now leaves cubic guards. Retaining the
independent radix-cube coordinate `N` instead of its radix-square
predecessor, and shifting the first Pell root, permit six more
eliminations without exceeding cubic residual degree.

The positivity witnesses are reselected. The reduction is an existential
equivalence, not a claim that the old triples represent the new products.

## Two separately bound fixed coefficient tuples

The preferred compact S34 and both positive companions use the **whole**
compact tuple with `beta=2^590069-1`:

| Polynomial port | Payload |
|---|---|
| `beta` | `compact_coefficients/native/coefficients/beta.bin.gz` |
| `K0` | `compact_coefficients/native/coefficients/K.bin.gz` |
| `MC` | `compact_coefficients/native/coefficients/MC.bin.gz` |
| `MF` | `compact_coefficients/native/coefficients/MF_source.bin.gz` |

Each payload is gzip of minimal unsigned little-endian integer bytes.
`MF_source` is already shifted by `beta`; insert it directly.
The four raw payloads occupy **295,388 bytes**, compressed to 9,445 bytes.
The largest port has 592,884 bits.

The directly inherited source34 instance is retained separately as
[integer34/sextic34.json](integer34/sextic34.json), with the complete
`integer_coefficients/` tuple and `beta=2^1064921-1`.
Its raw payloads total 532,479 bytes. The compact adapter reduces
coefficient bytes by 237,091 (44.5259%), without changing the skeleton.

Read [integer34/COMPACT_S34_ADAPTER.md](integer34/COMPACT_S34_ADAPTER.md)
for the complete native soundness and canonical parity adapter. It is
not justified merely by coefficient inequalities. Never mix ports
from the two tuples.

## Reproduce

Requirements: Python 3.10 or later, standard library only; no network
access is needed. The PDF uses ordinary TeX Live with `latexmk` and
`pdflatex`.

```sh
python3 verify_all.py
python3 -O verify_all.py
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Eleven phases rebuild the literal equations, run independent sparse
algebra checks, rebuild and independently audit both coefficient tuples,
check compact-adapter data, and verify reusable-lemma examples and
identities. Builders must reproduce the delivered polynomial bytes.
Logs and top-level receipts are under `validation/`.

The semantic statements are proved in the report and identified source
proofs. Finite checks do not decide consistency or replace an unbounded
Pell or compiler theorem.

## Package layout

| Path | Contents |
|---|---|
| `report.tex`, `report.pdf` | Complete mathematical report |
| `EQUATIONS.json` | Exact entry-point index and whole coefficient bindings |
| `integer34/` | Both bound sextics, expansion, builder, independent checker, local proof, compact adapter |
| `positive/` | P13/P12 graphs, builders, independent sparse checker, degree certificates, proof and review |
| `compact_coefficients/` | Exact compact tuple, original builder and independent auditor, literal data, inherited proofs and provenance |
| `integer_coefficients/` | Original source34 tuple, raw/compressed numerals, finite recipe, independent decoder, inherited proofs |
| `research/` | Proved syntax-retraction/local-inference and Pell-power lemmas; exploratory Pell-jet note |
| `provenance/` | Immediate pinned source proofs and baseline audit |
| `validation/` | Reproducible receipts and logs |
| `MANIFEST.sha256` | Delivered-file hashes, excluding itself |

Copied sources retain their contents and historical pins. Bundle ledgers
separately identify the current retrieval commit and file hashes. Some
inherited relative links assume the original repository layout; use the
ledgers to resolve their pinned targets.

## Proof status and integration

For each selected tuple, the report proves existence of a zero equivalent
to existence of a finite ZFC refutation using the inherited native compiler
and literal machine calibration. Negation yields the requested
ZFC-provable equivalence, without assuming consistency.

The local reductions and compact adapter received separate AI-assisted
mathematical review and exact finite algebra checking. This is not external
peer review or a proof-assistant certificate. The syntax appendix is a
proved component, **not a completed non-K215 consistency equation**.

For integration, copy this directory as an additive proposal under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/` and
choose its number according to the repository's then-current sequence.
This archive modifies no existing repository file. Any frontier entry
should preserve the domains, exact tuple names, operation convention,
and proof-status distinctions above.

Upstream licenses and notices are included. The new contribution and
verification wrappers use the repository's MIT license; inherited
source-specific notices remain in the coefficient bundles.
