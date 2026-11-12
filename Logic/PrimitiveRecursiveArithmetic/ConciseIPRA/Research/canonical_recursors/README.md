# iPRA with one explicit computation schema

Prepared for Vladimir Reshetnikov, 12 November 2026 (UTC).

## Main result

The report gives a six-rule presentation of full first-order intuitionistic primitive recursive arithmetic. Numerical terms use variables, `0`, and a successor-seeded recursor `R(n,a;u.h)`. Successor is `R(0,a;u.0)`. The zero computation is built into a canonical term grammar; normalized substitution enforces it, including when substitution first exposes a zero counter. The only explicit computation rule is successor computation.

The written proof establishes equiconsistency and bi-interpretability with iPRA. Both numerical interpretation domains are the whole domain, equality is actual equality, and both numerical composite isomorphisms have graph `x=y`. The proof first establishes an unrestricted raw/canonical equivalence, including recursor body extensionality, and only then recovers the restricted six-rule calculus. This avoids assuming that its literal-source and witness tests are preserved by arbitrary substitution.

This is a concrete improvement, not a theorem of absolute minimality. Normalization is part of the trusted specification and is counted in the implementations.

## Start here

- `report.pdf`: the complete report, including proofs, comparison tables, inherited arithmetic appendices, and complete checker listings.
- `report.tex`: a standalone LaTeX source containing the complete report. It has no external `\input` or listing dependency.
- `strict/FORMAT.md`: every syntax form, proof instruction, freshness restriction, and public input/output convention of the new checker family.
- `strict/canonical_checker.py`: the complete standalone strict checker for the new calculus.
- `compact/ARGUMENT.txt`: the separate compact implementation refinement and its precise input contract.
- `evidence/source_provenance.json`: pinned source paths and authenticated inherited-file hashes.
- `evidence/CLAIMS.json`: machine-readable statement of claims, measurements, tests, and limits.
- `SHA256SUMS`: checksums of the delivered files, excluding the checksum file itself.

## Complete checker comparisons

All headline byte counts remove actual docstrings, run `ast.unparse`, and append one LF. Measurements were made with CPython 3.12.14. They include the entire acceptance module. Gzip level 9 uses timestamp zero and is informational.

| Matching strict implementation | Rules | Tokens | AST nodes | Normalized bytes | Gzip 9 |
|---|---:|---:|---:|---:|---:|
| Scalar initialized `I`, independent `S` | 7 | 1433 | 1595 | 4923 | 1224 |
| Raw successor-seeded `R` | 7 | 1378 | 1532 | 4753 | 1209 |
| Canonical successor-seeded `R` | 6 | 1338 | 1485 | 4611 | 1205 |

The new canonical checker is 312 bytes (6.34%) smaller than the matching strict scalar checker. All three include complete public syntax validation, capture-safe substitution, scopes, all inference rules, JSON decoding, and final conclusion checking. The scalar control uses crossed elimination and witness-directed introduction, an equivalent matching presentation rather than a literal transcription of upstream `MPrf`.

The strict checkers are deliberately transparent and do not beat the repository's compressed arity codec. The archive separately improves that existing guarded scalar codec from 522 to 516 normalized bytes. A different program improves its AST coordinate from 281 to 280 nodes. These are different programs and are not sizes of the new canonical-R calculus. The token frontier of 258 is not beaten. The compact byte profile's gzip size rises from 329 to 332 bytes. A matching pair with both strict validators is 1381 versus 1376 normalized bytes.

The compact profiles retain the guarded public Eq/D language and broader auxiliary proof syntax. The compact modules do not themselves validate the public grammar. A separately counted strict front end is supplied. The stronger compact refinements claim correspondence on the documented integer/list certificate language, not identical behavior on every malformed JSON value.

## Reproduction

Python 3.12 is the reference measurement environment; a normal TeX Live installation with pdfLaTeX builds the PDF. The checker modules require only the Python standard library.

```sh
python3 reproduce.py
python3 reproduce.py --pdf
```

The first command verifies the delivered checksum manifest when present, regenerates and tests the strict checker family, and reruns the compact measurements and certificates. The second also assembles the standalone TeX source and compiles the PDF with three pdfLaTeX passes.

To compile the delivered standalone source directly:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

To run an individual new-calculus proof:

```sh
python3 strict/canonical_checker.py < strict/certificates/canonical/used_induction_hypothesis.json
```

Acceptance is exit status zero with exactly `ACCEPT` on standard output. The strict specification describes all finite proof trees; ordinary implementation resource limits still apply. Regenerating artifacts under another Python version can change source normalization and recorded hashes, so the frozen measurements should be compared using the reference Python version. After regeneration, rerun with `--skip-manifest` if the regenerated files differ from the frozen deliverable.

## Verification performed

- 86 named strict-family certificates, replayed through both readable and normalized checkers: 172 successful expected-outcome checks.
- 480 independent numerical substitution/evaluation comparisons, plus binder capture controls.
- 311 compact-package checks, including ordinary and optimized Python execution and negative scope, context, and malformed-input controls.
- Independent written-proof review of the canonical equivalence, rule recovery, interpretation composites, and zero-induction countermodel.
- Compiled PDF with resolved cross-references, rendered-page review, and archive checksum verification.

These executable checks supplement the mathematical proofs. No new Lean or Rocq formalization is claimed. The selected upstream Lean files are reference excerpts; they require the full pinned upstream project to build. This archive does not claim that those four files are a standalone Lean project.

## Additional mathematical results

1. In the pure scalar self-seeded language `0,S,F`, every unary term `t` has a constant `C` such that `t(n) <= C` or `t(n) >= n` for every natural `n`. Consequently this term language cannot define predecessor or an unbounded contracting unary function. This is a term-definability obstruction, not by itself a theorem against every relational interpretation.
2. Restricting induction to zero equations does not recover general equation induction in the existing scalar setting, even with both iterator computations, numerical coverage, successor separation, and successor injectivity. The report constructs an extensional nonstandard two-point-fiber model. The result also holds when induction against each fixed standard numeral is allowed. This does not rule out every changed-domain interpretation of that weaker theory.
3. The two initialized-scalar computation equations are independent, even over standard natural numbers with full induction, when one is omitted from the recursor's defining axioms.

## Provenance and attribution

The comparison is pinned to ProveIt commit `8eb71c1e570e07ef45ead686628e77f18ef34798`:

https://github.com/VladimirReshetnikov/ProveIt/tree/8eb71c1e570e07ef45ead686628e77f18ef34798/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The successor-seeded bootstrap, native logical bridge, scalar predecessor construction, equality reflection, primitive-recursion compiler, crossed transport idea, and witness-directed introduction are inherited. The new main contribution is the canonical-syntax presentation and its normalization/derivation/composite proofs, together with the matching strict implementations. The boundary theorems and compact refinement have their scopes stated separately.

The inherited files in `reference/`, the two successor-seeded source appendices in `theory/`, and the frozen compact controls retain the upstream MIT No Attribution license, included as `reference/LICENSE-ProveIt.txt`. The two successor-seeded appendices are renamed exact copies: local `successor_seed_prelogic.tex` is upstream `Research/successor_seed_completion/theory/prelogic.tex`, and local `successor_seed_bootstrap.tex` is upstream `.../bootstrap.tex`.

`evidence/upstream_checker_census.json` records a scoped audit of 97 current, non-reference, checker-named Python files below the stated raw-size cutoff. It is not an exhaustive census of every historical source file or every possible presentation.
