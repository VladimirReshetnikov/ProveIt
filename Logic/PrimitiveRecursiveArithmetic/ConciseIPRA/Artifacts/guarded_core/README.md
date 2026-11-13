# A guarded core for intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 10 November 2026.

This package gives a modest structural simplification of the current ConciseIPRA presentation: its canonical calculus no longer lets a certificate choose between case and progress introduction at an equation. The new calculus is effectively intertranslatable with the inherited calculus, with both native formula composites. Its ordinary realization is bi-interpretable and equiconsistent with full first-order iPRA, with the entire numerical domain, actual equality, and identity numerical composites.

The reference snapshot is ProveIt commit `b17dd5487f34adea473a0204c5320fb3eeb8910e`, under `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`.

## The construction

Terms remain `x`, `0`, `S(t)`, and the scalar iterator `I(n,a;u.h)`, with its two usual computation equations. Canonical formulas are equations and paired formulas `D_{x,y}B`. If the matrix `B` is an equation, it must have the form

```text
I(y,0;u.h) = I(y,0;u.k).
```

Both sides therefore reduce to zero at `y=0`. The update bodies may contain the bound state and fixed parameters. A compound matrix is unrestricted within the same canonical grammar.

There is one introduction schema. It retains `B(t,z)` when the matrix is an equation, and `B(t,0)` when the matrix is compound; its successor target is always `B(t,S z)`. The primitive choice flag is gone.

The proof is substantive: padding an equation by a guarded paired formula gives an equivalent compound formula. This reconstructs equation implication and numerical cases, then unrestricted contextual equation induction. The induction argument first proves a compound implication in a context independent of the case variable; it does not perform an invalid case split while retaining an assumption that depends on that variable. Explicit translations then recover every old rule and both formula composites.

The full axioms, schemas, inference rules, proof transformations, ordinary interpretations and both composites are in `report.pdf` and its LaTeX source. Attributed appendices reproduce the existing logical and arithmetic bridge, including predecessor, equality reflection, pairing and primitive recursion.

## Size comparison

All figures charge a whole standalone Python module under the repository's canonical-statement checking convention. Normalization removes actual docstrings, applies `ast.unparse`, and adds one final newline, using CPython 3.12.14. Gzip is level 9 with a zero timestamp and is informational.

| Program | Normalized bytes | Significant tokens | AST nodes | Gzip 9 |
|---|---:|---:|---:|---:|
| Frozen current byte profile | 529 | 266 | 310 | 333 |
| Frozen current token profile | 576 | 261 | 292 | 345 |
| Frozen current AST profile | 613 | 263 | 289 | 349 |
| `code/checker.py` | 528 | 265 | 308 | 332 |
| `code/checker_bytes.py` | **527** | 266 | 307 | 335 |
| `code/checker_tokens.py` | 575 | **260** | 290 | 345 |
| `code/checker_ast.py` | 607 | 263 | **286** | 349 |

The coordinate minima **527 bytes / 260 tokens / 286 AST nodes belong to different programs**. No single program realizes all three. The gain is small; global minimality and a literature-wide priority claim are not established.

The direct checker isolates the mathematical change. The byte and AST profiles also compose the mandatory major-premise verification into the hypothesis-supply expression, preserving all successful executions. The token and AST profiles retain the inherited broad-exception traversal and its malformed-input qualifications. `code/readable_checker.py` uses a clear explicit list test and descriptive names.

## The canonical-input contract matters

The theory for the bi-interpretation claim is the guarded **Eq/D canonical language**. `Q` closures are administrative resources, not additional canonical object formulas.

The compact checkers permit a broader administrative certificate syntax. In particular, an unguarded atomic `D E` has the sound progressive reading

```text
exists x forall y (E(x,y) -> E(x,S y)).
```

Its elimination exports the weaker conditional closure using equation induction in iPRA. On a canonical guarded matrix the progressive and ordinary conditional readings are provably equivalent, since the zero instance is a theorem. This proves conservativity of administrative proofs over canonical guarded conclusions.

**The entire unrestricted administrative syntax is not claimed to be bi-interpretable with iPRA.** The compact programs do not themselves reject every noncanonical public goal. This is the same kind of canonical-encoding contract used by the repository's compact arity checkers, but the new canonical grammar is explicitly stated here.

`code/strict_checker.py` adds an explicit canonical closed-goal validator and remains a whole standalone program. It has 1,208 normalized bytes. A supplied old-core control with the corresponding ordinary Eq/D goal parser has 1,109 bytes. Thus the compact byte advantage does not carry over to this stricter input contract. Both modules and all their costs are included; no validator is hidden outside the accounting.

## Run and reproduce

From this directory:

```bash
python3 scripts/reproduce.py
python3 tests/build_root_cases.py
python3 tests/audit_guarded_proofs.py
python3 code/checker.py < tests/root_cases/guarded_literal_equation_introduction_local_neutral.json
python3 code/strict_checker.py < tests/root_cases/guarded_induction_with_used_hypothesis_local_neutral.json
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Acceptance means exit status zero and exactly `ACCEPT` on standard output. An exception, timeout or resource limit is rejection. The byte, direct, AST, readable and strict profiles use the `local_neutral` fixtures. The token profile uses `global_plain` fixtures. The named producer emits both scope conventions; they must not be mixed.

The delivered reproduction receipt records **800 CLI checks across ten whole programs**, in ordinary Python and `python -O`, with **zero mismatches**. It includes eight canonical named examples, a 176-instruction guarded induction proof using its hypothesis, a separate administrative example, an old atomic case theorem rejected by the new calculus, scope attacks, wrong computations and malformed inputs. The guarded-proof audit finds no unguarded atomic paired occurrence in the eight canonical named derivations.

One inherited negative fixture changes only the retired introduction-mode field. The deterministic checker intentionally accepts its otherwise valid progress proof; the receipt explicitly records this changed expectation.

These are finite implementation checks. The universal mathematical results are written proofs and have not been formalized in Lean or Rocq. The existing repository's Lean files were inspected; no new Lean build is claimed.

## Contents and attribution

- `report.tex`, `report.pdf`, `sections/`: the complete report and new proof.
- `code/`: standalone checkers; none imports a producer, validator module, axiom database or theorem catalog.
- `tests/`: untrusted named proof producer, new derived-rule compiler, certificates and guard audit.
- `scripts/reproduce.py`: whole-module measurements and CLI verification.
- `evidence/`: metrics, validation receipts, source provenance, review and layout evidence.
- `reference/`: exact pinned baseline sources and attributed inherited mathematical proofs; `baseline_strict_goal.py` is a new control derivative, not a frozen upstream file.

Inherited ProveIt material is distributed under its MIT No Attribution license, included in `reference/LICENSE-ProveIt.txt`. The report distinguishes the new guarded reduction from inherited logic, arithmetic and codec results. `MANIFEST.sha256` covers the final package files other than itself.
