# Comparison of eight Con(ZFC) Diophantine packages

Review snapshot: `3b201cdea32d2c816f5f3d20734051f25fd3ef14` of VladimirReshetnikov/ProveIt, directory `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`. All packages originally target upstream snapshot `cdd582bec13f908df3711fa9e05d1ddac368a5db`. The repository reconciliation says the eight were independently prepared on 22 October 2026, arrived together in `2fd49a1a9d`, and were placed in `084e120830`. Those provenance facts are repository statements, not newly reconstructed from archives here.

## What was checked

Downloaded source texts, JSON circuits, and proof notes were treated as inert data. No repository Python, shell, or build script was executed. The separate owned `independent_circuit_review.py` checks each available literal JSON gate list, free ports, witness use, arithmetic counts, and two finite-field line-specialization degree diagnostics. Its JSON receipt contains 30 circuits. The diagnostics agree with all supplied exact-degree claims but are not substitutes for uniform symbolic degree proofs or semantic proofs. In particular they cannot establish consistency or produce an accepting K215 computation.

## Metric and domain

Arithmetic operations mean binary addition, subtraction, and multiplication. Squaring and multiplication by a fixed constant each count one. Reuse and equality comparisons cost zero. Fixed coefficients and their enormous bit lengths cost zero. Thus one must distinguish shared-circuit system cost from the cost of a single polynomial obtained by a sum of squares. All primary equations below are over strictly positive integers. A formula must not be silently interpreted over all integers; the scaled factor discriminant can vanish outside its positive domain.

| Package | Important positive-domain presentations: unknowns / equations / maximum degree / arithmetic operations | Main contribution |
|---|---|---|
| 01-explicit82 | 18 / 1 / 187 / 82; 20 / 9 / 42 / 72 | Literal fixed-input specialization with minimal changes. Keeps the variable-input infrastructure. Separate tag-system route is not a newly kernel-checked endpoint. |
| 02-system63 | 16 / 7 / 28 / 63; 16 / 1 / 157 / 72; 16 / 1 / 101 / 74; SOS 16 / 1 / 56 / 83 | Fixed marker, merged gamma, raw slack absorption; ordinary strong equation lowers degree. Squared budget guard saves operations but preserves existence, not every tuple. |
| 03-system64 | 16 / 7 / 28 / 64; 15 / 6 / 244 / 71; 15 / 1 / 295 / 82 | Same ordinary-strong system as 02 up to an alpha shift, with one extra operation; algebraic elimination of strong Pell root f removes one unknown. |
| 04-poly73 | 16 / 1 / 156 / 73; 16 / 7 / 60 / 65; SOS 16 / 1 / 120 / 85 | Affine marker factor 3W+1−3W0 avoids a quadratic marker guard; two-sided rather than folded machine. |
| 05-fixed15-16 | 16 / 7 / 34 / 66; 15 / 1 / 295 / 82; 15 / 1 / 346 / 80 | Independent f-elimination and alternative outer norm; careful signed-root proof order. |
| 06-blank67 | 15 / 6 / 60 / 61; 15 / 6 / 46 / 62; 15 / 1 / 155 / 67; 15 / 1 / 123 / 68 | No input or normalized machine. Direct blank K215 windows. Same arithmetic as 08, much smaller fixed coefficient recipe. |
| 07-fixed70 | 16 / 1 / 169 / 70; 16 / 1 / 156 / 71; 17 / 8 / 28 / 61 | Delay the sign of repunit factor q−(B−1)J until after dyadic power recovery; use scale X=wq². |
| 08-start-only67 | 15 / 6 / 60 / 61; 15 / 1 / 155 / 67; SOS 15 / 1 / 120 / 78; 34 / 25 / 2, hence quartic | Independent inputless Start-only construction; best prior positive-variable quadratic lift. |

The 01–07 entries in this table are supported by reviewed source files and the independent gate audit (except SOS forms whose counts follow the displayed residual finalizer). The 08 values agree with the prior owned artifacts and the pinned repository reconciliation. 'Maximum degree' is exact for the listed reference formulas; some package summaries only write an upper bound.

## Important distinctions hidden by similar filenames

1. In 02, `fixed_input63_system.json` is the old normalized-strong system, degree 60. The recommended `fixed_input63_ordinary_system.json` has the same 63-operation cost but degree 28. They are not the same equations.
2. In 03, `fixed_marker74_system` has degree 60; `fixed_marker76_system` has degree 28. Both cost 64 operations.
3. 05's degree-34 system uses an unscaled normalized-strong factor; this differs from 02's genuinely ordinary strong equation. Simply unscaling a factor does not give 02's degree-28 system.
4. 06 and 08's 67-operation polynomial and 61-operation system are the same arithmetic skeleton up to renaming. Direct independent comparison of their literal JSON gate lists finds exactly one register rename, `C` to `marked_rhs`, and its one use; every other gate and every system comparison is identical. They have different, non-interchangeable coefficient tuples. The independently discovered degree-295 root-elimination products in 03 and 05 likewise share their algebraic construction, though this latter correspondence was checked from their displayed formulas rather than byte-identical DAGs.
5. 07's signed repunit and 02's squared-budget constructions require separate existential reconstruction arguments. An operation count by substitution without those proofs is insufficient.

## Fixed coefficients and coefficient height

Every package supplies a terminating, bounded recipe for specific integers; none expands the enormous actual coefficient tuple. No free machine index, oracle, or variable exponent is part of the final polynomial. Nevertheless these are compressed definitions, not printed numeral lists, and coefficient bit length is excluded from the operation measure.

| Package | Compiled machine / tiles | Radix exponents |
|---|---|---|
| 01 | 437 states, 8 symbols / 3510 | stated by finite formula |
| 02 | 436 states, 8 symbols / 3502 | b=5^43, d=5^87 |
| 03 | 436 states, 6 symbols / 2628 | b=5^42, d=5^85 |
| 04 | 220 states, 3 symbols, two-sided / 669 | b=5^35, d=5^71 |
| 05 | 436 states, 10 symbols / 4376 | b=5^45, d=5^90 |
| 06 | raw K215 plus padded halt, 216 states, 2 symbols / 439 | b=5^33, d=5^67 |
| 07 | 435 states, 10 symbols / 4366 | b=5^44, d=5^89 |
| 08 | 435 states, 10 symbols / 4366 | formula in its coefficient recipe |

Here B=2^d. The fixed source port MF is always the shifted mask, native MF plus B−1. Matching port names does not authorize mixing independent coefficient recipes. To transfer arithmetic onto 06's smaller tuple, prove it against 06's Start-only compiler interface, rather than merely splice a number into a 07 fixed-marker formula.

06 is the cleanest available coefficient baseline: direct raw K215 rather than an input-erasing, folded normalized machine; 439 rather than 4366 tiles; d=5^67; modulo-five arithmetic removes the correction bit. These are real improvements in coefficient description and size, not changes to the cost model. Its local tableau proof is a new proof obligation and is being reviewed independently from the arithmetic.

## Useful combinations

### Ordinary strong equation plus inputless compiler

02 proves that replacing normalized strong f²−Delta i²c⁴=1 with ordinary strong (ic²)²=Delta(f²−1), while using A0=Delta(f²−1) in the auxiliary norm A0(V²−y²)+y²=1, preserves the intended existence predicate. Its seven-equation system remains 63 operations but drops maximum degree 60 to 28. Removing the input-marker equality using the already proved 06/08 inputless interface should yield a 15-variable, six-equation, 61-operation degree-28 system. This needs the ordinary-strong rank proof transplanted, not merely the algebra. The crucial bootstrap is c>A Delta², f>2c, c² dividing f²−1 obtained from the rank theorem, and restoration of positive auxiliary coordinates before decoding.

### Signed repunit plus Start-only

07 allows q−(B−1)J to be an initially signed unit and recovers its positive sign only after proving q is a power of two. This might eliminate a coordinate or budget guard when paired with an inputless compiler. Its pre-decoding estimates differ, so its larger X=wq² scale must be retained or replaced with a new proof. The original scale X=wq is not justified by mere textual substitution.

### Strong-root elimination plus Start-only

03/05 eliminate f by a quadratic norm with an even, nonzero cross coefficient, giving a rational root whose integral square forces it integral. This should reduce the 15-variable inputless interface to 14 variables, at substantially greater degree and arithmetic cost. The sign is not automatic: one must first recover the pre-input Pell kernel, then use a signed-quotient theorem on the correctly restored compiler interface. A root-eliminated formula is a variable-count tradeoff, not necessarily a shorter formula.

### Better unrestricted-integer conversion

06 uses Pos(u,v,r)=1+u²+v²+r(r+1), surjective onto positive integers by Legendre's three-square theorem, while leaving tau and y signed because they occur only squared and are nonzero on solutions. This gives 41 integer variables and degree 310 from the 15-positive-variable degree-155 polynomial, rather than 60 variables under one-plus-four-squares. Its cost is 158 operations. The cost reduction is meaningful but does not improve the positive-variable frontier. Further signed-coordinate reductions require separate proofs.

### Low degree

08's 25 quadratics in 34 positive variables remain the best prior low-degree construction here. Other packages' larger lifts are often over different domains: 02 has 79 nonnegative variables, 04 has 83 unrestricted integers, and 03 has 128 unrestricted integers. Those numbers cannot be compared directly without charging domain conversion. The natural target is to exploit existing squares, positivity, and multiplication dependencies in the retained-index core, rather than naively give every gate a new variable.

## Proof assumptions and formal status

All eight compose the exact K215 blank-halting calibration with a native-window/Pell compiler and a new fixed-input or inputless reduction. The K215 endpoint has existing Lean/Rocq support upstream. None of these Diophantine bridges is a newly checked end-to-end Lean/Rocq theorem, nor a derivation encoded in ZFC syntax. The assertion 'ZFC proves the equivalence' rests on formalizability of the ordinary mathematical construction and calibration in ZFC, not on importing proof-assistant soundness as an axiom. A correct report should state that distinction plainly.

No consistency assumption is needed to prove the equivalence itself. It neither proves Con(ZFC) nor decides whether the fixed equation has a standard solution. Under consistency, unsolvability cannot be proved in ZFC; claiming both directions of independence from consistency alone would require extra care or a stronger soundness hypothesis.

No global optimum is established. Number of variables, degree, arithmetic operations, coefficient height, domain, and proof complexity produce a Pareto comparison. Classical nine-variable existence results already prevent treating 14 or 15 variables as a global record; those do not provide the same short, explicit coefficient-and-circuit artifact.

## Sources

Primary immutable directory: https://github.com/VladimirReshetnikov/ProveIt/tree/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms

Key proofs inspected: 02 `FIXED_INPUT75_ORDINARY_PROOF.md`; 03 `proofs/FIXED_MARKER.md` and `proofs/DEGREE_295.md`; 04 `zfc_diophantine.tex`; 05 `proofs/fixed_input_proof_notes.md`; 06 `report.tex`, `proofs/blank_helical_proof.md`, `proofs/fixed_blank_67_proof.md`, and `proofs/pell_lemma_audit.md`; 07 `artifacts/fixed_input_notes.md`. The top-level upstream README reconciliation is saved inert as `README.upstream.md`.
