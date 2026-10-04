# Independent review of packed atomic selected outputs

**PASS; no requested source or proof change.** I read the entire final helper and companion, authenticated their three declared dependencies, and independently checked both complete emitted arrays. The actual fixed-table source has **3,162 = 1,467M + 1,695A**, **152 positive witnesses**, and exact degree **34,817**. The complete diagnostic has **330 = 132M + 198A**, **57 positive witnesses**, and exact degree **1,361**.

| Reviewed file | SHA-256 |
|---|---|
| `matrix193_packed_output_scout.py` | `80959b87138eea4148b5fc6aafb78fc73a5a8283d3b676c142f57b8a8190fba9` |
| `matrix193_packed_output_scout.json` | `74f119d979d92851e571967de7baf046e85d523ba9ca03acf21fa92bafa1c244` |
| `matrix193_packed_output_scout.md` | `036d93d564baf6b018f6541a4662ffcf9de102456aef80405d3586a0933b3518` |

## Complete source checks

A fresh checker reads saved JSON and independently interprets the rows in a sparse polynomial ring. It does not import or execute author or predecessor Python. Both arrays have unique outputs, topological closure, and complete row/input liveness: **3,492 binary rows** in total. Direct recounting agrees with the two ledgers above. The witness conversion is the parent's count minus ell plus32, giving exactly the advertised 308-witness reduction on the actual table.

The checker compares every retained group and fixed context binding with the atomic parent. From those matrices it independently recomputes the two maximum coefficient magnitudes, block lengths and least dyadic padding constant. It checks every coefficient of the four reversed positive coefficient words, with actual lengths **144,144,194,194**. Each coefficient lies in `[1,2M_block-1]`; the exact constants and 2^93 padding agree. I also recounted the 1,022 distinct actual integer literals and their maximum 94-bit magnitude.

The independent polynomial comparisons cover the complete H, M, Z, q and joint-bound expressions, every selector sum, both computed time/spatial bases, all six native cut bindings, and all four reconstructed matrix increments. The actual H, M, Z expansions contain respectively 444,14,241,111 terms at the explicitly declared cut variables. The four complete increment expressions contain 195,195,205,205 terms. These counts describe exact sparse cut expansions, not an expansion of the final degree34,817 polynomial.

All **24** full comparison residuals are checked coefficientwise against separately constructed formulas: two block bounds, six comparisons for each pair of middle-digit extractions, two word-sum comparisons per block, and the retained six history/controller/population comparisons. This includes every positive-hat decrement, signed correction, low/high decomposition and offset subtraction. The complete native63 block matches the pinned contract literally after substituting its six verified cut expressions. The full74-row finalizer is checked row by row, including every square, all23 joins, addition of one, multiplication by the native product and final subtraction of one. These cut identities and literal downstream checks certify the entire intended new polynomial; finite modular samples are not being used as proofs of those identities.

For degree, a fresh leading-component interpretation follows every actual row, replacing only the known cancelling main norm by its exact expanded identity. At a new deterministic linear specialization of the ordinary input and all witness coordinates, with the saved valid fixed coefficients held constant, it obtains:

| Array | Exact degree | Nonzero leading coefficient modulo1,000,000,007 |
|---|---:|---:|
| Diagnostic | 1,361 | 462,720,187 |
| Actual fixed table | 34,817 | 448,782,300 |

This assignment differs from the author's dense diagnostic line. I also checked the uniform upper/leading-form argument in the companion: the native product retains degree34,039; the independent high-hat term in a length194 extraction residual has degree389; its square gives SOS degree778 without cancellation. The result is uniform over the stated valid program-coefficient recipe, not just the saved coefficient assignment.

## Bounds, extraction and ordinary input

The order of the proof is sound. At a positive zero the integer native product times `1+SOS` equals one, so all24 comparisons vanish before native decoding is invoked. The two positive block slacks therefore bound the large block integers within their allotted Q-powers. The smaller joint sum bounds the four H fields and two SWITCH selections by P. Its unconditional minimum is seven, giving P at least six; this excludes J=0, and then P is at least B. On the diagnostic parent recipe B is already at least320. No use of the old340 individual-hat bound is made.

Those preliminary bounds prevent overlap in every Q-block before the AND is decoded. The native truth fields are positive and have the required total and residues. Once the inherited native theorem gives dyadic q, `q=32*B*Q^(ell+m+4)` makes B and Q dyadic. Since the padding C is fixed dyadic and `Q=C*P`, P is dyadic too. This preserves the time repunit `P=B^t`; Q is only the wider spatial radix. The controller, time scale and marked population have not been silently moved to Q.

After the joined AND is separated, every selected block digit is below P. This is the necessary stronger bound for extraction. For each positive coefficient word, every convolution coefficient is nonnegative and below `2*M_block*l_block*P < Q`, so the full integer multiplication is carry-free. The low and dot slacks select the unique base-Q middle digit; the nonnegative high quotient needs no extra bound. The word-sum remainder is also unique because the true sum is below `l_block*P < Q-1`. The strict last inequality follows from the chosen dyadic padding and integer bounds, rather than being assumed from modular equality alone.

Subtracting `M_block*sum` removes the common positive coefficient offset. Subtracting the separately paid `c0*sum_g(a_(2g)+a_(2g+1))*S_g` restores the exact signed row increment. The right-action SWITCH is retained directly. Thus the unchanged history equations recover precisely the old atomic trajectory, and its typed SWITCH pre-state still gives `k<D`. The retained population congruence and `x<D` force `k=x`, including zero input and an empty TILE word.

Conversely, an accepting atomic trajectory supplies the two concatenated blocks and unique nonnegative quotient/remainder values, with strictly positive hats/slacks. The new joint slack is positive by the displayed `(12D-6)J` bound. A fresh native extension is supplied for the new packed fields. This proves the same ordinary-input projection; it is not a polynomial identity with the parent, nor a claim to preserve its native Pell witness tuple.

## Evidence and scope

I read the full diagnostic and actual-fixture code. The actual saved83-TILE example is correctly identified as an x=0 illustrative context: it materializes the packed blocks, four products and mathematical extraction relations, but does not re-evaluate the entire large outer DAG or materialize native Pell coordinates. My exact source interpretation covers the complete emitted DAG independently of those finite fixtures. I did not repeat the large-integer fixture computation.

The author reports fresh normal and optimized exact replays from `/` on the pins above; I did not duplicate those executions. I read the strict duplicate-key parser and recursive type-exact comparison. The source/degree checks described here are separate fresh computations, not runs of predecessor builders.

The eight program parameters are still fixed coefficients prepared by the valid inherited recipe. Arbitrary assignments to them are not asserted to encode a program, and the diagnostic is not universal. The underlying directed193/unary initialization and native Pell/AND converse remain explicit inherited dependencies. Within that scope this is a complete fixed-arity ordinary-input construction, saving993 operations and308 witnesses from the atomic parent. It does not improve the universal84-operation frontier.
