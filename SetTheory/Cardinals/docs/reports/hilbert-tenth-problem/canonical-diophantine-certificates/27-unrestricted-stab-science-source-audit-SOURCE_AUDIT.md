# Independent source audit: unrestricted finite stabilization

Audit date: 4 October 2026. Result: **PASS for source-to-equation correspondence, the fixed arithmetic ledger, exact degree, and deterministic replay**, subject to the explicitly identified mathematical dependencies below.

## Scope and provenance

The audited fresh source is `../build_stabilization.py`; the authoritative emitted object is `../evidence/polynomial-dag.json`. The exact SHA256 values are:

- Builder: `47c2e5c63ea6eceef26c4bd117ca8a195eb5180e00482f9d9384a7705788fb2c`
- DAG: `8622585bcafaf9b3aee84e12f229beb17a33d27d6f1bf0b6cb6bc956ee4ac759`

I read the entire fresh builder before execution. I read the preceding fixed-arity packet's `PROOF.md` only as inert text to establish the input convention and explicit POWER dependency. No earlier builder, checker, simulator, arithmetic schedule, or theorem prover was imported or executed.

`audit_source.py` is a newly authored independent checker. It does not import or execute the builder. It parses the DAG as data, gives every input/witness a distinct formal indeterminate, and normalizes every pre-SOS gate as a sparse integer polynomial. It independently reconstructs the mathematical system, with deliberately rearranged residuals, then compares canonical polynomial coefficient dictionaries. This is exact all-assignment algebraic comparison, not a finite sample of modular evaluations.

The checker verifies every one of the 1,897 equality residuals, every argument and output of all 164 macro records, all 33 advertised ports, and all 3,263 formal variable names including the ordinary input. It checks that none of the expected or emitted equations, macros, ports, or witnesses is unaccounted for. It also validates references, acyclicity, literal syntax, the operation whitelist, the exact final sum-of-squares shape, and output liveness.

`run_replay_checks.py` runs only this fresh builder and this fresh checker. Normal Python and Python `-O`, both with working directory `/tmp`, produce byte-identical DAGs and builder receipts. The independent checker produces identical normal/optimized receipts. Eleven deliberately damaged DAGs are rejected in both modes, for 22 expected rejections; no failed check writes a PASS receipt. These mutation checks are useful implementation regressions, not a completeness theorem about every possible mutation.

## What was matched

The independent symbolic reconstruction checks the following full chain rather than trusting macro metadata as a specification:

1. The seven nested Cantor equations for `(p−1,q−1,r−1,T,d−1,e−1,f−1,D)`, with raw code `InputPlus−1`
2. The external base-32 geometric masks, tile bitplanes and exclusion of digits 6/7, and the finite patch's 0–15 mask
3. The unknown precision, its explicit POWER call `b=32^L`, the equation `16s=b`, and both explicit base-32-to-base-b SPREAD conversions
4. Centered dimensions, padded tile and patch row/plane SPREAD calls, tile repetitions, the patch translation, and all associated POWER and geometric equations
5. The three box powers, whole-prism and interior masks, `Sub((s−1)I,U)`, all three negative shift quotients, stable endpoint bitplanes, and the single balance equation
6. All 117 fifteen-equation POWER expansions and every Sub, AND, SPREAD, geometric and stable macro expansion nested in the above

In particular, the generalized capacity mask really is `(b/16−1)I`, via a separately paid exact quotient witness. It has not been replaced with the binary mask `I`. Both conversion outputs are genuinely connected to the spatial embedding. The final balance uses coefficient 6 and all six neighbor streams, with no missing conservation equation hidden in prose.

## Positive-domain dependency order

The following is the required order for applying the mathematical macro lemmas. It prevents a theorem on natural exponents or positive bases from being applied before its hypotheses have been established.

- The six dimensions are positive witnesses. Tile, patch and intermediate Cantor codes use positive-minus-one adapters and are natural. The single input does too. Positive `box.tx`, `box.ty`, `box.tz` witnesses are increased by one before geometric use, so the actual padding parameters are at least two
- The first external masks use base 32 and positive volume exponents. Their geometric-value witnesses are natural. Every initial Sub mask and value is consequently natural. In a Sub call, the first base is 2 and exponent is `M+1≥1`; it produces a radix at least 2, after which the two remaining POWER bases and all exponents meet the POWER domain. All extraction quotients, half-digits and remainders are natural adapters, and the two strict slacks are positive
- Precision `L` is positive. The POWER call has base 32 and natural exponent; therefore `b=32^L≥32`. The exact equation `16s=b` gives `s=b/16≥2`, so `K=s−1` is natural. No floor division is being silently used
- Each SPREAD has its own natural stride gap and equation `stride=length+1+gap`, and a positive range slack imposing `value<base^length`. All six lengths are positive. Thus `stride−1≥length≥1`, the copy base is at least 2, and both geometric denominators are nonzero. The two first conversions establish `L≥pqr+1` and `L≥def+1`. Their base-32 digit supports already imply the requested input range
- After conversion, tile and patch streams are genuinely base-b streams with the original coefficients. All spatial bases are positive powers of the power-of-two radix b. Tile row, tile plane, patch row and patch plane lengths are positive. Their strides have their own paid bounds. The row and plane input bounds follow from their established embeddings and are also expressly asserted by the SPREAD range constraints
- All repetition lengths are positive polynomial expressions. The half-lengths are positive, and each full side length is at least four. The three trimmed-mask equations consequently identify the natural sums of lengths `A−2`, `B−2`, `C−2`; no negative geometric length is used
- The interior mask and capacity are natural. The support Sub call's value U is a natural adapter. The three negative-shift quotients and all endpoint bitplanes are separately natural adapters

Within POWER, `a` and `beta` are positive-plus-one, hence at least two; all zero-capable auxiliary differences are positive-minus-one. The previously specified fifteen-equation number-theoretic theorem is the only source of the claim that these equations represent exponentiation. The sparse audit proves the equations were emitted exactly, not that theorem itself. In using its natural-subtraction statement, its thirteenth equation supplies `a>w≥base`, so the displayed integer `a−base` agrees with natural subtraction.

## Domain-specific semantic cross-check

The generalized support mask is valid because b is a power of two and `K=b/16−1=2^(5L−4)−1` consists of contiguous low one-bits in a base-b block. Multiplication by the interior indicator I gives that bit pattern at exactly the strict-interior slots, with no overlap. Therefore `Sub(KI,U)` means precisely that U is a finite interior-supported stream with each odometer coefficient in `[0,K]`; it permits arbitrary natural values up to K, not merely 0 and 1.

The interior shell ensures all six shifts stay inside the prism and have no row or plane wrap. The natural quotients asserted by the three division equations are the exact negative shifts. Outside the prism, only stable periodic background remains and all odometer neighbors crossing its boundary are zero.

Every coefficient on the left of the balance is at most `5+15+6K=3b/8+14`; every coefficient on the right is at most `6K+5=3b/8−1`. For `b≥32`, both are strictly below b. All coefficients are nonnegative. Thus base-b uniqueness makes the single integer balance equivalent to all sitewise equations. For the smallest possible b=32 the upper bounds are 26 and 11; in the actual source the conversion length inequalities may force an even larger b, which only improves the bounds.

A supplied finite natural supersolution with stable endpoint bounds every legal prefix by the usual first-excess-toppling argument. A legal process can make at most the finite sum of its coefficients; it therefore reaches a global stable configuration. No claim that the supplied supersolution equals the true odometer is needed.

Conversely, any finite legal global stabilization has a finite natural odometer. Choose a sufficiently large centered padded prism containing its support and the patch strictly in the interior and meeting the four spatial stride inequalities. Independently choose precision L large enough for both conversion inequalities and `max(u)≤32^L/16−1`. Since changing L only changes the encoding radix, it does not obstruct the prism choice. The actual endpoint and odometer then supply the stream data. Completeness of the explicit macros provides their witnesses. This confirms that the binary-only restriction has actually been removed without changing the raw input language.

## No hidden unpaid arithmetic or dimension-dependent syntax

The DAG alphabet is exactly positive input/witness leaves, fixed integer constants and binary `+`, `−`, `*`. Every adapter, shift, mask product, spatial offset, Cantor operation, residual, square and sum appears as a counted gate. No exponentiation, division, remainder, AND, digit operator or comparison appears as a primitive DAG operation.

The builder imports only argparse, collections, hashlib, json and pathlib. Its construction classes and construction function have no Python power, division, floor-division, remainder, bitshift, or bitwise arithmetic operator. Three `/` operators elsewhere are only pathlib output-path construction. The named macro methods do not evaluate unbounded powers; they emit fixed polynomial constraints. All loops are over fixed source lists, fixed seven-coordinate decoding, fixed macro equation lists, or the finite already-constructed graph. The program never accepts a mathematical input value from which to choose an equation count. File output selection and JSON/hash traversal are outside the arithmetic straight-line program and are not claimed as arithmetic gates.

## Exact ledger

- Strictly positive existential witnesses: **3,262**, plus the single positive input
- Polynomial equalities: **1,897**
- Body: **8,881** gates, comprising **3,837 multiplications, 3,101 additions, 1,943 subtractions**
- Final sum of squares: **5,690** gates, comprising **1,897 residual subtractions, 1,897 squarings, 1,896 additions**
- Full polynomial: **14,571** gates, comprising **5,734 multiplications, 4,997 additions, 3,840 subtractions**
- Macro calls: **117 POWER, 28 Sub, 6 AND, 6 SPREAD, 5 geometric, 2 stable**
- Dead gates: **0**; dead witnesses: **0**; the input is live

An independent witness subtotal is `117×26 + 28×5 + 6×3 + 6×4 + 5 + 2×3 + 27 = 3262`. The last 27 account for descriptor/Cantor witnesses, precision and its quotient, padding parameters, prism masks, the supersolution and three shift quotients. The equality subtotal is `117×15 + 28×3 + 6×2 + 6×4 + 5 + 1 + 16 = 1897`; the last sixteen are seven Cantor equations, the quotient equation, four prism-mask equations, three shift equations and the final balance.

## Exact degree eighteen, without a merely syntactic claim

Gatewise propagation bounds the final polynomial's total degree by 18. Exact sparse normalization finds that the only degree-nine residuals are `patch.shift.eq8`, `patch.shift.eq9` and `patch.shift.eq11`; every other residual has degree at most eight.

Write `tx0,ty0,tz0` for the actual positive witness variables named `box.tx`, `box.ty`, `box.tz` (the geometric padding values are each one larger). Each of these three residuals has exactly the same highest homogeneous term:

`−4 p q r d e f tx0 ty0 tz0`.

Consequently the highest homogeneous part of the sum-of-squares polynomial is exactly

`48 (p q r d e f tx0 ty0 tz0)^2`.

This is nonzero and has degree 18, proving exact degree. The checker records each degree-nine homogeneous part explicitly. As a second algebraic certificate, substituting one formal variable t for those nine witnesses and zero for all other witnesses and the input produces a univariate polynomial with leading coefficient 48 at degree 18. A specialization used to test polynomial degree need not lie in the positive solution domain.

## Reproduction and limitations

Run `python source-audit/run_replay_checks.py` from any working directory. Its absolute paths select this packet only; it performs replay from `/tmp` and writes `source-audit/replay-and-mutation-receipt.json`. The primary exact audit receipt is `source-audit/audit-receipt.json`.

This audit establishes the exact emitted constraints and finite symbolic checks. It does not instantiate an enormous complete Pell/sandpile witness, enumerate all mathematical inputs, execute a universal-machine loading schedule, compile Lean, or turn the external POWER theorem into a new independent number-theoretic proof. The mathematical semantics continue to rely on that stated theorem and the explicit bit-mask, spreading, geometry and least-action arguments. There was no detected source mismatch or failed final replay.
