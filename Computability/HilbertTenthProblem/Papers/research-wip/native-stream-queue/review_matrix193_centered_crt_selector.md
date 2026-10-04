# Independent review of the centered circle CRT selector

**PASS; no author correction requested.** The complete frozen helper and proof were read, their declared dependencies authenticated, and the actual receipt independently reconstructed as described below. The result is an integer-exact local/fixed-duration improvement, with the real and unbounded-duration limitations stated correctly.

| Author artifact | SHA256 |
| --- | --- |
| [matrix193_centered_crt_selector.py](matrix193_centered_crt_selector.py) | 091ea1a9fae724f7dd9cab551e6938b0524677766b39f0311d9e324f8837cd28 |
| [matrix193_centered_crt_selector.json](matrix193_centered_crt_selector.json) | 51e304b13fbeea6d1b69a35ee8fbd3f359dfe050e2ceee177890b8b3d07d1d78 |
| [matrix193_centered_crt_selector.md](matrix193_centered_crt_selector.md) | 5360a8ecd24ab88eb0e7867ca98179eebfcded3a11fd427fb3923ba535106046 |

## 1. Integer selection and unrestricted proof

The circle equation is z^2+b^2=5,928,325. An independent exhaustive scan of all 4,869 possible integers z from -2434 through2434 reproduces exactly the saved96 labels and their square witnesses. Every integer solution lies in this interval. The sorted labels are bijective with the unchanged96 paired actions, including the unchanged tile order; no extra transition is introduced.

An independent smallest-prime-factor sieve finds the same1,721 distinct positive label differences and their148 prime divisors. Thus L0 has precisely the required prime support. The argument proving pairwise coprimality of m_z=1+(z+2435)L is valid: a common prime would be coprime to L, divide the label difference and therefore divide L. A multiple L of L0 strictly greater than2T preserves this argument for every fixed-context table. Prime powers in the differences need not divide L.

The centered lookup is sound on arbitrary integer zeros. First the circle forces an admitted label and hence a positive modulus greater than2T. Each coefficient sphere gives |A_c|<=T. The computed equality A_c+T=C_c-m_z*q_c, with integer quotient, then identifies A_c+T with the unique residue in [0,2T], yielding exactly twice the intended entry. No parity condition is assumed for an arbitrary candidate zero; evenness follows from this recovery.

For every intended coefficient, T is odd, A_c is even and |A_c|<T. Therefore T^2-A_c^2 is positive and1 or5 modulo8. Legendre's three-square theorem supplies the three integer roots. The theorem is correctly identified as an external existence dependency; neither the author packet nor this review claims to re-prove its general formalization. The twelve saved concrete decompositions are additionally checked by exact integer squaring.

With recovered entries A=2a,B=2b,C=2c and ad-bc=1, the row residuals are2e0 and2(ae1-be0), where e0,e1 are the ordinary row-action errors. Since a is nonzero, both residuals vanish exactly on the row action. The source pays all four row-coordinate doublings. This inference is made only after coefficient recovery; no off-node determinant identity is used.

The supplied-coefficient alternative adds the six defining residuals. Substitution of the computed coefficient expressions makes these residuals identically zero and gives the complete computed polynomial, including its countdown wrapper. This all-value relation is separate from the merely integer-zero relation equivalence to the older154-operation selector; no bijection of their auxiliary witnesses is asserted.

## 2. Independent saved-source reconstruction

The fresh independent checker imports neither author nor predecessor code. It reads their pinned JSON as inert data. It compares the entire transition table, initializer and endpoint to the immediate parent, authenticates all six direct dependency pins, and checks all192 determinants and nonzero pivots. It recomputes the six full CRT integers by successive two-modulus CRT, independently of the author's idempotent-sum formula. All576 residue matches and4,560 pairwise gcds agree.

Each actual local source is independently interpreted in a sparse polynomial ring. Separate formulas describe every circle, coefficient-sphere and row residual, the full sum of squares and the full LOAD factor. All residuals and complete output coefficients agree, with fixed-numeral bindings treated as independent formal ports. The resulting ledger is:

| Complete source | M | A | Total | Exact degree | Full output terms |
| --- | ---: | ---: | ---: | ---: | ---: |
| Computed synchronized | 52 | 55 | 107 | 8 | 403 |
| Computed countdown | 64 | 69 | 133 | 10 | 8466 |
| Supplied synchronized | 58 | 67 | 125 | 4 | 175 |
| Supplied countdown | 70 | 81 | 151 | 6 | 3684 |

All516 local gates and12,728 complete output coefficient entries are covered. The audit checks producer freshness, topological closure, the final output binding and liveness of every row, supplied port and named numeral. This is a complete literal-source audit, not a residual-count estimate.

The four actual fixed-numeral specialization lines independently attain the advertised degrees. The computed modes have leaders L^4*t^8 and L^4*t^10; the supplied modes have monic degree4 and6 leaders. These do not use equations that hold only at zeros. Uniformity follows because the recipe has L>0. The degree claim after arbitrary initial-state substitutions remains only an upper bound, as stated.

The independent checker reconstructs all rows of both positive-duration arrays through its own coordinate-copy/rename schedule. They match literally:172 gates and32 positive witnesses at h=1, and337 gates and63 witnesses at h=2. The509 rows are fully live. It also independently verifies eight complete integer tile zeros, rejects their eight perturbed successors, and evaluates the four complete rational false-transition examples.

The rational examples are genuine domain diagnostics: z=-2434,b=63 is on the circle, the coefficient spheres use A_c=0 and one root T, and rational quotients restore these values. Both nonzero current rows then map to zero. This is impossible for the actual invertible matrices. Real nonnegativity of the polynomial remains true but does not imply real transition exactness.

## 3. Countdown, positive coordinates and uniform context scope

The inherited26-row wrapper is retained as E_load*(U+n^2+next_n^2). Both factors are nonnegative over the reals. Over integers a zero therefore means LOAD with unrestricted selector auxiliaries, or one matched TILE at zero counters. From natural input x and the fixed initializer, the endpoint forces exactly x LOAD steps before any TILE. A LOAD after a TILE makes the counter negative, and no allowed step can raise it. Signed counters create no extra accepting trajectories.

At fixed duration h, five next-state coordinates and26 local auxiliaries give31h signed witnesses. Summing the h nonnegative local predicates with the seven-gate endpoint pays h joins, giving134h+7 operations. A single positive offset represents the entire finite signed list; paying one subtraction for each of its31h coordinates gives165h+7 operations and31h+1 positive witnesses. The external input is unchanged. The note correctly reuses adjacent state coordinates and keeps the degree claim at most10.

The uniform fixed-context extension is justified by the pinned group theorems: all relevant matrices remain in H' inside Gamma_1(5), so their first entries are1 modulo5 and never zero. Recompiling odd T, the multiple L and the CRT constants retains the exact local schedule. This does not assert that one unchanged numerical semigroup accepts every program, nor does it execute a new arbitrary-program compiler.

The source counts fixed numeral uses in the same declared arithmetic model as the parent. The larger constants are not hidden: L has1,221 bits, the CRT product118,159 bits, and the largest bound numeral118,158 bits. No bit-complexity or coefficient-height improvement follows. Unbounded duration still requires fixed-arity packing; the present packet supplies no new universal-operation bound or real-exact improvement over the earlier real-safe interface.

## 4. Authentication and replay

The authenticated direct dependencies are the matrix193_crt_selector trio, matrix193_gamma1_recode.md, matrix193_context_absorption.md and matrix193_synchronized_rows.md, at exactly the six hashes recorded in the frozen author receipt. Their relevant group/context and countdown contracts were cross-read in this review and the immediately preceding [CRT review](review_matrix193_crt_selector.md). The faithful encoding and machine simulation remain inherited theorems; this review does not claim a new proof of them.

Fresh normal and -O executions of only the new frozen helper from / both passed exact receipt comparison against the pinned WIP data root. Its checks use explicit exceptions and recursive type-exact equality, with duplicate-key, noninteger-number and nonfinite-number rejection. The independent arithmetic/source reconstruction also passed against the final96-label receipt hash above. No predecessor, archived program or historical suite was executed, and no repository file or Git state was modified.
