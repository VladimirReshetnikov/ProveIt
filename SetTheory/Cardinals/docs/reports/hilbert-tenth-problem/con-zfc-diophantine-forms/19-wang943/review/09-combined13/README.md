# Smaller Diophantine descriptions of ZFC consistency

Research contribution prepared for ProveIt, 22 October 2026.

Source snapshot: [VladimirReshetnikov/ProveIt at 3b201cdea32d2c816f5f3d20734051f25fd3ef14](https://github.com/VladimirReshetnikov/ProveIt/tree/3b201cdea32d2c816f5f3d20734051f25fd3ef14).

## Main result

This package specifies fixed integer polynomials and systems whose absence of solutions, in the stated domain, is equivalent **provably in ZFC** to Con(ZFC). The recommended compact equation has **13 positive integer unknowns, 84 arithmetic operations, and exact total degree 571**. One extra operation lowers its degree to 515.

The proof combines the existing blank-input K215 compiler, new weighted square-root elimination, an ordinary-strong Pell scaling, and a smaller local computation alphabet. The attached report gives the formulas, proofs, coefficient recipe and logical calibration. The claims are ordinary mathematical theorems with reproducible finite checks; **the changed reductions have not been formalized in Lean or Rocq**.

Start with `con_zfc_reductions.pdf` or its editable source `con_zfc_reductions.tex`.

## Results and tradeoffs

Every system degree is the maximum degree of a residual. Counts charge every binary addition, subtraction and multiplication, including multiplication by a numeral. Register reuse and final comparisons are free.

| Construction | Domain | Unknowns | Equations | Exact degree | Operations |
|---|---|---:|---:|---:|---:|
| Weighted main polynomial | positive integers | 13 | 1 | 571 | 84 |
| Alternative-weight polynomial | positive integers | 13 | 1 | 515 | 85 |
| Weighted comparison system | positive integers | 13 | 4 | 544 | 78 |
| Alternative-weight system | positive integers | 13 | 4 | 488 | 79 |
| Root-amalgamated polynomial | positive integers | 14 | 1 | 121 | 76 |
| Root-amalgamated system | positive integers | 14 | 5 | 72 | 67 |
| Ordinary-strong polynomial | positive integers | 15 | 1 | 99 | 69 |
| Ordinary-strong system | positive integers | 15 | 6 | 28 | 61 |
| Retained-auxiliary system | positive integers | 16 | 7 | 24 | 60 |
| Quadratic lift | positive integers | 32 | 23 | 2 | — |
| Sum of squared lift residuals | positive integers | 32 | 1 | 4 | — |
| Signed lift with positivity equations | all integers | 62 | 33 | 2 | — |
| Sum of squared signed residuals | all integers | 62 | 1 | 4 | — |

The report also specifies a 39-unrestricted-integer version of the main equation, degree 1142, by substituting a surjective three-integer positivity expression. SOS alternatives and two inputless specializations of package 05 are supplied as additional JSON circuits.

The existing 06/08 equation still has the cheaper 67-operation evaluator; this package does not improve every measure simultaneously. The new ordinary system improves the existing 15-variable/61-operation system's degree from 60 to 28. The positive quartic improves 34 variables to 32; the unrestricted integer quartic improves the reviewed collection's 83-variable form to 62.

No global minimum is claimed. In particular, the repository's formalized nine-unknowns existence theorem is a different benchmark from an emitted polynomial with stated degree and circuit.

## The coefficient binding is part of the equation

**Use `COEFFICIENT_BINDINGS.json`.** It selects `compiler/tshape_constants.json` as the default recipe for all new constructions. These are four specific integers, not four further unknowns:

| Circuit names | Meaning |
|---|---|
| `beta` or `Bm1` | B − 1 |
| `K0` or `Kconstant` | DC + B DR |
| `MC` | Native low mask |
| `MF` | Native high mask **plus B − 1** |

The shifted `MF` must not be confused with `MF_native`.

The four-site compiler has exactly 71,356,645 local tuples and B − 1 has exactly 5^28 binary digits, compared with 5^67 in package 06. This is a factor 5^39 reduction in that bit length. The intermediate cross compiler has 38,256,607,897 tuples and 5^36 bits.

The recipe uses the literal finite K215 transition table and a fixed lexicographic enumeration. It never searches for a ZFC refutation or asks whether K215 halts. The complete integers are finite and specified exactly, but far too large to materialize. The JSON records a symbolic recipe and scalar geometry, not the expanded integers.

The source arithmetic was first derived on package 06's original ports. The new coefficient proof establishes the same complete compiler interface, including supports, carry margins, masks, overlap semantics, canonical positivity and actual-index dummy tuning. This is why the arithmetic reductions transfer. Mask congruences alone would not justify the transfer.

The inherited `arithmetic/p67_source.json`, `p80_source.json` and `p82_source.json` are generator inputs retained for provenance; their original coefficient annotations are not instructions to mix old numerals with the new recipe.

## Proof entry points

| Issue | Main report | Supporting note |
|---|---|---|
| Exact thirteen-variable formula | Section 3 | `proofs/ROOT_AMALGAMATION_PROOF.md` |
| Nonzero reconstruction denominators | Sections 3.1–3.2 | `proofs/INDEPENDENT_ROOT13_AUDIT.md` |
| Signed reconstructed f and auxiliary root | Section 3.3 | Same independent audit and upstream signed-quotient notes |
| Ordinary strong rank and lower-degree system | Section 4 | `proofs/LOW_DEGREE_PROOF.md` |
| Explicit 23-quadratic lift | Section 6 | Same low-degree note |
| Only ten primary coordinates need positivity | Section 7.2 | `proofs/SIGNED_CORE_AND_INTEGER62.md` |
| Independent 62-integer-variable review | Section 7.2 | `proofs/INTEGER_QUARTIC62_INDEPENDENT_REVIEW.md` |
| Four-site local relation and exact coefficients | Sections 8–9 | `proofs/COEFFICIENT_REDUCTION_PROOF.md` |
| Machine/refutation equivalence and formal status | Section 10 | `proofs/AUDIT_STATUS.md`, pinned endpoint source |

The logical chain is:

    polynomial/system solvability
        iff a valid blank K215 tableau exists
        iff K215 halts on the blank tape
        iff a finite ZFC refutation exists.

Taking negations gives the requested consistency equivalence. This does not prove Con(ZFC). No accepting run of the literal machine or solution of the final equation is supplied.

## Reproduction

Python 3 with its standard library suffices for all mathematical finite checks:

```sh
python3 verify_arithmetic.py
python3 verify_compiler.py
```

The arithmetic runner uses temporary copies and verifies that 19 generated JSON files reproduce byte for byte. It checks live-gate ledgers, sparse identities, quadratic residual degrees, exact construction dimensions, independent formula evaluations and degree diagnostics. Uniform exact-degree proofs are in the report; diagnostic line restrictions are not their replacement.

The compiler runner checks the literal table and three inherited checker hashes, all 430 actions, the exhaustive 13 center categories against the predicates, 32 toy halting tableaux, 9,152 mutated periodic planes, and 26,790 sparse basis checks across the two recipes. It compares four saved receipts exactly. The toy machines are explicitly controls; they are not purported halting computations of K215.

To typeset the report:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error con_zfc_reductions.tex
```

A conventional TeX installation with the packages named in the preamble is sufficient. `make verify` and `make pdf` are equivalent convenience commands. No network access is required.

## Artifact layout

- `arithmetic/`: complete high-degree circuits, generators, generator inputs and receipts.
- `low_degree/`: the ordinary and retained systems, all expanded quadratic residuals, exact sparse-polynomial tools and receipts.
- `compiler/`: literal machine, four-site/cross predicates and fixed-coefficient recipes, finite checkers and receipts.
- `proofs/`: new derivations and independent reviews.
- `upstream/`: selected pinned mathematical dependencies and logical endpoint. This is a review bundle, not a complete Lean checkout.
- `verification/`: delivery-level check summary and PDF review record.
- `SOURCE_PINS.json`: source URLs, revision and content hashes.
- `SHA256SUMS`: hashes of all distributed files other than the manifest itself.
- `licenses/`, `LICENSE`, `NOTICE.md`: inherited license texts and provenance.

Paths are relative to this directory. The files can be incorporated as a new report package under the repository's existing `con-zfc-diophantine-forms` collection without changing the old eight packages.

## Verification scope

The new mathematical arguments were reviewed independently where the domain and denominator issues are delicate. All finite checks passed, and the 20-page PDF was rendered and inspected. The inherited K215 endpoint statement was read at the pinned snapshot; the entire Lean/Rocq project was not rebuilt. A proof-assistant certificate for the new reductions remains future work.

The compiler recipe and number-theoretic proofs are both necessary. Finite tests alone are not a proof of the final equivalence, and there is no claim of global minimality or a new universal Diophantine operation bound.

