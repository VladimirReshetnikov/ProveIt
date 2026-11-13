# Current ConciseIPRA frontier audit

Snapshot: `7a7633980dbca7f599322a5e7f1e65fb1cddb7c8`, read 2026-11-13.

## Findings

There is no proved universal complexity lower bound in the project. Its reported minima are empirical coordinatewise minima among inspected complete Python checking programs under specified input contracts. They are upper bounds on the unknown optimum. A row combining minima from different programs is not the size of a single checker.

The top-level README's package table is obsolete for the newest values. The integrated article's Chapter 11 is more current but does not yet incorporate the four ZIP archives in `docs/incoming/` at this pin. All four were inspected here.

## Integrated article contracts

| Contract | Tokens | AST nodes | Normalized bytes |
|---|---:|---:|---:|
| R/U: raw canonical guarded goal, whole JSON | 244 | 261 | 465 |
| R/U allowing JSONL prefix readers | 239 | 256 | 465 |
| R+2/U: shifted raw codec (single byte-profile program) | 267 | 298 | 461 |
| T/ed1: fully validated whole JSON and native Eq/D public grammar | 317 | 356 | 597 |
| G1/A-: goal-only native validation, includes strict contenders | 317 | 356 | 573 |

These contracts are not interchangeable. The article explicitly declares shifted R+2/U incomparable with R/U and separates JSONL readers from whole-JSON readers. Its triple 239/256/461, quoted by many packages, combines different encodings and framing contracts.

## Pending archives that change the current frontier

`ipra_validated_three_field_2026-11-13.zip` (Git blob `c2e318a7b9939b04f16676d679b8b37438e3dc8e`):

| Complete checker | Tokens | AST nodes | Normalized bytes |
|---|---:|---:|---:|
| `code/checker_tokens306.py` | 306 | 362 | 668 |
| `code/checker_joint.py` | 313 | 353 | 701 |
| `code/checker_ast348.py` | 330 | 348 | 681 |
| `code/checker_bytes595.py` | 329 | 372 | 595 |

These validate the entire input alphabet and the native Eq/D public grammar. Its stated strict coordinate envelope is 306/348/595. Three-field protocol reconstructs major formulas; AST profile is certificate-equivalent to its control; byte profile retains the public theorem set but can change accepted noncanonical certificates. No axiom deletion or new mathematical theory is claimed.

`ipra_checked_reduction_2026-11-13.zip` (Git blob `51a2ac2187ec0e9d4780d1a727bef4df8ec8d5ed`):

| Complete checker | Tokens | AST nodes | Normalized bytes |
|---|---:|---:|---:|
| `compact/checker_ast255.py` | 245 | 255 | 580 |
| `native/code/checker_tokens315.py` | 315 | 365 | 618 |
| `native/code/checker_ast353.py` | 323 | 353 | 630 |
| `native/code/checker_bytes589.py` | 324 | 367 | 589 |

Compact AST improvement is exactly replacing temporary singleton `[k]` by `{k}` before the decoder immediately returns the same list, saving one AST `Load`. Native improvements compose an eager opener, empty administrative premise, context phase selection, and delayed neutral truth. These preserve canonical public theorem sets; not all arbitrary raw certificates. Again no axiom deletion.

Thus the combined current empirical extrema are compact **239/255/461** (mixed contracts) and strict native whole-JSON **306/348/589** (different programs).

All eight measurements above were independently reproduced with CPython 3.12.14, normalization `ast.unparse(ast.parse(source)) + LF`, significant tokens excluding formatting/comment tokens, and full `ast.walk` node counts. Source hashes and measurements are in `latest_measurements.json`. This parse-only measurement does not verify program soundness.

## Other pending archives: avoid repeating these results

`ipra_frontier_church_2026-11-13.zip` explicitly fails the requested positive minimization. It proves a three-element-model obstruction for a specific pure simply typed fixed Church-number arithmetic, including coverage, separation, and full formula induction; no finite-dimensional ordinary interpretation of iPRA, even with finite parameters or quotients. It also rederives the fixed Church-type predecessor obstruction. Not a claim about polymorphism, added arithmetic constants, additional sorts, or all combinatory calculi. No checker improvement.

`ipra_induction_boundary_2026-11-13.zip` explicitly fails the requested positive minimization. It extends an automorphism obstruction to the numbering theory with all standard numbering laws and finite/nonstandard parameters, including finite-dimensional definable domains and quotients. It supports computation, injectivity, coverage, separation, identity iteration, extensionality, fixed-point laws, and constant-target induction. It gives a literal equation with derivable base/step but a nonstandard colored counterexample. No checker improvement.

## Foundation and accepted mathematical standard

The project studies full first-order iPRA, not merely its equational or quantifier-free consequences. Its standard stronger condition requires whole numerical domains, actual equality, and both numerical composite maps provably the identity graph `x=y`, along with term/formula round trips. User's current request permits other domains but still requires actual bi-interpretability, not equiconsistency alone.

The native scalar terms are `x`, `0`, `S(t)`, `I(n,a;u.h)`. Native formulas are equations, `Q_y B := B(0) -> forall y B(y)`, and `D_xy B := exists x (B(x,0) -> forall y B(x,y))`. Native rules: hypothesis, two iterator computations, equational transport, QE, DE, DI by cases, progress restricted to literal equations. These ingredients and numerous fusions are already in the corpus.

Near-miss mathematical simplifications already present include one-term crossed transport; no-literal-zero source; single witness-tested or diagonal introduction; clauses removing Q; one-body homogeneous contexts; computation normalization; evaluation fused into witness discharge; deterministic newest-parameter witnesses; inference of witnesses from matrix patterns; variable-only or backward replacement; scalar uniqueness of iteration; counter-aware/constant-free/successor-seeded recursors. The recently integrated homogeneous-discharge theory has only three rule families but a 3427-byte complete readable checker and explicitly does not beat the global frontier.

## Sources inspected

- `README.md` (local `source_snapshot/readme.md`).
- `docs/Article/chapters/ch11_cert.tex` (local `source_snapshot/ch11_cert.tex`), especially sections `cert:sec:envelope`, `cert:sec:sizes`, `cert:def:contracts` and final research questions.
- `Artifacts/validated_arity_refinement/README.txt`, `CLAIMS.json`.
- `Artifacts/prefix_conditional/README.md`, `CLAIMS.json`.
- `Artifacts/conditional_image/README.txt`.
- `Artifacts/homogeneous_discharge/README.txt`.
- All four current incoming ZIPs: README, CLAIMS/STATUS, measurement/source evidence and selected checker source.

All archives are available under `source_snapshot/incoming/`; textual members have been extracted. Public raw download and Git blob verification succeeded for every incoming archive. No upstream repository was modified.
