# Independent complete Grill arithmetic-stream audit

Date: 2026-10-03. Decision: **PASS for this frozen full arithmetic composition**, conditional on the pinned full positive native/recoder/U15 theorems and the separately reviewed literal source simulation. No source discrepancy or missing interface was found. This is a whole-stream audit, not a count inferred from a small fixture or truncated prototype.

The source reviewed is `universal.dag`, SHA-256 `a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`, with exactly 61,209,290 bytes. `review_complete_manifest.json` freezes the full manifest, producer modules, fixed data, composition/component proofs, and this review's independent scripts and receipts. The newly completed `FULL_COMPOSITION_PROOF.md` was read in full and agrees with the interface and domain reviewed here.

## 1. Independently recomputed full ledger

- 3,600,546 binary arithmetic gates
- 803,517 multiplications
- 2,792,839 additions and 4,190 subtractions, hence 2,797,029 additions/subtractions
- 797,141 supplied positive coordinates: six external and 797,135 existential witnesses
- Formal total-degree **upper bound 71,731,007**, treating all six external coordinates and every witness as degree one
- 8,160 fixed-integer recipe rows
- All 3,600,546 runtime gates and all 797,141 coordinates are reachable backwards from the actual terminal output

The stream has an eight-byte header and exactly 17 bytes per row. Every opcode and signed numeric operand was inspected. Every gate operand is a declared input, an existing constant, or an earlier numeric gate ID. There are no forward references or dangling nodes. Input declarations partition the input namespace without gaps or overlaps and their names are unique.

The actual named signature was checked against the complete expected family list, including both separate 49-auxiliary recoder namespaces, the loader witnesses, the native seven scalar witnesses, 794,976 selector hats, 2,030 selected-history hats, and 16 native-kernel witnesses. No extra program selector or exponent input exists.

The first 310 gates are the complete loader; the native prefinalizer has 3,599,976 gates; the finalizer has 260. The stream's manifest totals agree with all independently recomputed totals.

## 2. Fixed integer coefficients and literal queue interface

Every constant is an exact decimal integer, a power of two at a fixed nonnegative source exponent, a finite geometric sum at a fixed nonnegative source length, or an addition/subtraction/multiplication of earlier constants. Every recipe operand is checked to be a prior negative constant handle. No recipe can read an input or gate. Thus the recipes denote ordinary fixed integer coefficients, with no runtime exponentiation or division. The cost model reads such fixed numerals freely; it is an arithmetic operation count, not a bound on bit complexity.

The modular evaluator deliberately evaluates `geom4` by binary concatenation of finite geometric sums, rather than copying the producer's division-after-modulus formula. One test modulus is divisible by three, so that invalid modular inversion of three could not masquerade as a correct geometric sum.

The reviewer reconstructed the complete 397,488-bit string `E(300)E(539)` directly from the corrected literal words and compared its exact integer value to the actual constant used by the queue multiplication. They are equal; the value has 319,867 bits. The actual constants `K=2^397488` and `K-1` were also compared by exact integer equality. This is stronger than a modular check of the E-pair numerator.

The actual queue-value gate topology is exactly `(K-1)X=(K-1)C_e+L_e*V*(T-1)`, and its scale gate is `K*T=Q1`. Independently inspected width gates are `P0=X+Z0` and `target_width=L_e*T`; the last residual is exactly their difference. No existential padding ambiguity remains on the valid input slice.

There are 75 unused *constant recipe* rows. They are inert numeral data, not runtime gates, inputs, or hidden operations; no runtime gate or quantified coordinate is dead. No optimization claim is made for constant storage.

The fixed recoder's SHA-256 and Git blob ID, the native kernel SHA-256, complete run-table SHA-256, and literal Genera table SHA-256 were checked. Producer module hashes were rechecked against the full manifest.

## 3. Exact finalizer structure

All of the last 260 actual rows were checked against the claimed source construction, without merely evaluating a stored finalizer label. Each of the 86 listed nonunit comparison pairs is subtracted and that exact difference is squared. The 86 squares are summed, one is added, the result is multiplied by the one native unit, and one is subtracted:

`F=U*(1+sum(R_j^2))-1`.

The four-factor native unit product was also traced through the actual multiplication rows. There is no additional checksum family, no external sum of squares added to a possibly negative native polynomial, and no residual lying outside the product.

Over the integers, `1+sum(R_j^2)` is positive. Therefore a zero forces every residual to be zero and `U=1`; the converse is immediate. The 86 comparisons split as 10 native, 34 first recoder, one canonical-length guard, one right-tape frame, 34 second recoder, three exponent extraction/binding, one unary scale, one queue value, and one exact width.

## 4. Independent whole-size formula evaluation

`review_complete_dag.py` imports only Python standard-library modules. It does not import or execute the producer or upstream Python. It evaluates every actual binary row, while a separate implementation computes the specification from the supplied coordinates and inert pinned JSON data.

The independent specification uses:

- The two entire pinned 130-row recoder sources, with only their documented fixed-width power prefixes replaced; all 34 comparisons in each are preserved
- Physical U15 blocks constructed as literal strings, reproducing both 32-bit block numerals and the negative difference coefficient
- The exact E-pair string, independently of the producer's factored constant formula
- The original, uncompressed chronological phase sums `Q=sum((i+1)S_i)` and `Next=sum((((i-1) mod m)+1)S_i)`, rather than copying the emitted prefix-sum compression
- Forward power-weighted packing, rather than the producer's reverse Horner loop
- Division-free independent geometric-sum recurrences
- The native H/M/Z/scale formulas from the pinned word-closure contract and all 67 fixed native kernel rows as JSON data

Seven whole-size assignments passed: four deterministic random modular assignments, all ones, signed small coordinates reduced modulo a prime, and all zeros. Each case matches all 86 residual values, all four native factors, the native unit, both actual queue-width ports, and the final output. In total this is 25,203,822 evaluated gates, 602 residual comparisons, 28 native-factor comparisons, and seven complete output comparisons.

The moduli are 2^61-1, 2^31-1, 1,000,000,007, and 3,000,000,021. The last is intentionally composite and divisible by three. The zero/all-one cases also exercise degenerate off-zero algebra such as J=0 and P=1.

An exact coefficient argument was separately checked at all 397,488 phase indices. The coefficients of each phase pair in the original phase residual and emitted compression agree both in the B-dependent part and constant part; the triangular unhat correction agrees too. This is an exact algebraic identity, not an inference from the sampled assignments.

These finite evaluations are implementation evidence, not a proof that arbitrarily large positive Pell witnesses exist. The parametric transfer proof supplies algebraic identities; the pinned positive converses supply existence.

## 5. Degree boundary

Independent structural propagation gives degree upper 71,731,007. The native unit's propagated degree is 52,602,723; the maximal nonunit residual bound is 9,564,142, so the final multiplication gives `52,602,723+2*9,564,142=71,731,007`.

The optional `review_complete_leading.py` evaluated the corresponding top-degree homogeneous forms at deterministic nonzero input weights modulo two primes. Both final values were zero, already because the first native norm factor's propagated top form evaluated to zero. These probes are **inconclusive**. They do not certify exact degree, do not justify lowering the bound, and are not presented as proof that a lower bound has been established. This review retains **upper bound only**.

## 6. Positive semantic composition and theorem boundary

The semantic contract, independent input-contract audit, corrected bridge and complete run-table review were read, as were the generic-width recoder theorem and its complete positive converse, the 130/132 recoder transfer, geometry47's domain/converse, the native word-closure/weak-cone/composed proof contracts, `native_history_proof.md`, and `FULL_COMPOSITION_PROOF.md`.

The canonical recoder has the single extra guard `input_slack+beta=u+1`, with `u=x+1>=2`, giving `u<q0<=2u`; the upper endpoint is correctly non-strict. The second full recoder is specialized to input/output one and has neither that guard nor the dyadic-duration predicate. Its full theorem allows every h>=2. The three positive extraction constraints have a unique representative in `[1,B-2]`, forcing h=N+1. They impose no unintended power-of-two restriction on h.

The tape value N and queue value X are supplied positive witnesses, not signed off-zero expressions being declared positive by fiat. Their valid-slice values are forced by the equations. The native positive width slack is retained, and the exact-width comparison closes the ordinary-input interface. The literal E word lies in the strong cone; its strong-to-weak witness transfer preserves the exact chosen width. No padding-language shortcut is used.

Only x varies as the represented set's ordinary argument. The five coordinates a_e,p_e,s_e,C_e,L_e are external positive program parameters, fixed together for that represented set. The explicit valid slice in `FULL_COMPOSITION_PROOF.md` supplies their finite definitions. Arbitrary positive parameter tuples are not asserted to be valid U15 programs, and these five coordinates are never existentially chosen anew with x.

The positive-zero interpretation remains conditional on the precisely pinned full native/recoder/U15 theorems and the source-simulation proofs. **Signed and zero-coordinate test assignments only check off-zero polynomial algebra; they do not extend the halting theorem beyond its positive domain.** This audit does not formalize the theorem in a proof assistant, reconstruct the entire historical Pell dependency chain, materialize astronomical Pell tuples, prove universality on malformed program slices, or prove an optimal gate/witness/degree bound.

A complementary root reviewer independently reports exact replay of every runtime gate and exact constant value, reconstruction of the whole Grill run table, and matching of the fixed 67-row native kernel to four freshly fetched authenticated upstream receipt forms. That work is preserved separately; the current audit's numerical and structural evidence does not depend on its checker.

## 7. Reproduction and resources

Run only the independent local checkers:

- `python review_complete_dag.py`
- `python -O review_complete_dag.py`
- `python review_complete_dag.py --structural-only`
- `python review_complete_leading.py`

The whole-stream checker uses explicit exceptions rather than removable assertions. Normal and optimized substantive results agree. The final normal full run took about 18.2 seconds with 154,796,032-byte peak RSS; leading-form probes took about 7.8 seconds with 189,579,264-byte peak RSS. Every pass had a 1 GiB address-space cap and 300-second CPU cap. No full integer Pell tuple was constructed.

The primary receipts are `review_complete_dag.json`, `review_complete_dag.normal.json`, `review_complete_structure.json`, and `review_complete_leading.json`; logs preserve normal/optimized progress. The file pins are in `review_complete_manifest.json`.
