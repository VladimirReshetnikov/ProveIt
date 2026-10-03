# Independent full Grill circuit audit

Date: 2026-10-03. Decision: **PASS, conditional on the explicitly imported complete native/recoder theorems and finite-input U15 universality theorem.** No source, coefficient, domain, comparison, finalizer, or semantic-composition defect was found.

This is an independent exact source and mathematical-interface audit of the fixed universal-input proposal. It is not proof-assistant certification, a new proof of all historical Pell-kernel lemmas, a construction of numerical giant Pell witnesses, or a minimality/record claim.

## 1. Audited object and decisive results

The binary source is `source://arithmetic/universal.dag`, SHA-256 `a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`. It has 61,209,290 bytes: an eight-byte header followed by 3,600,546 seventeen-byte rows.

Independent exact reconstruction consumes **every source row**, not just sampled evaluations or the author's ledger:

| Quantity | Independently established |
|---|---:|
| Binary operations | 3,600,546 |
| Multiplications | 803,517 |
| Additions | 2,792,839 |
| Subtractions | 4,190 |
| Additions plus subtractions | 2,797,029 |
| Positive existential coordinates | 797,135 |
| External positive coordinates | 6 |
| Nonunit comparisons included in the output | 86 |
| Comparisons including the unit condition | 87 |
| Exact constant-only recipes | 8,160 |
| Largest actual fixed coefficient bit length | 551,891 |
| Formal total-degree upper bound | 71,731,007 |

Every gate is topologically closed, every supplied coordinate is declared exactly once in a disjoint input partition, and every gate and supplied coordinate is live from the final output. The six externals are exactly `x,a_e,p_e,s_e,C_e,L_e`; the last five are fixed for a represented set and are not existential choices depending on x.

The degree entry is **only an upper bound**. The literal source contains norm leading-term cancellation, so a syntactic max/sum propagation must not be presented as an exact-degree certificate. No exact-degree claim is made here.

## 2. Independence, pins, and actual replay method

No producer module, producer checker, upstream Python module, cached producer bytecode, or dynamically compiled upstream code was executed. The two checkers in this directory were written specifically for this audit and import only Python standard-library modules. Producer source was read for format/schedule review; correctness comes from the independent mathematical motifs, directly fetched source data, and exact comparisons below, not from calling the emitter.

`check_exact_source.py` parses the raw binary stream itself. It evaluates all coefficient recipes to exact integers, then consumes the stream sequentially against independently reconstructed operations. A runtime constant operand must equal its expected integer exactly; modular fingerprints are not the equality oracle. Free simplifications are restricted to literal constants, zero/one identities and identical subtraction. Expected live operations must match the actual opcode and both operands at the next row.

The checks cover:

- The paid `x+1` shift and both complete generic recoder sources, their fresh 49-coordinate auxiliary sets, and every retained comparison
- The first recoder's canonical guard, signed finite tape formula, unrestricted second exponent, all three extraction equations, unary scale/value and exact width
- Every chronological selector pair, running phase-prefix accumulation, slope-group membership and multiplicity
- All grouped affine transports, exact compressed phase residual, Horner packs, binary powers, doubled repunits, joined native lanes and their precise exponent offsets
- All 67 native unit-kernel rows, all six of its retained residuals, its four unit factors and sixteen positive auxiliary names
- All 86 differences/squares, their complete sum, and the one safe integer-unit finalizer

The independent checker also reconstructs **all 397,488 run exponents** from the literal 1,013-symbol Genera table by decoding phase membership in the three arithmetic-progression rule families. Every emitted run-table entry agrees. This duplicates the numerical table check as a fresh check; accepting-head and normalization semantics remain imported from the separately audited semantic packet.

The 67-row native kernel is authenticated beyond the producer's extracted file: four unit-mode forms in a freshly fetched upstream `grill_tag_native_composed205.json` have exactly the same named kernel definitions after replacing only the four actual H/M/Z/scale interface names. All four six-residual lists, factor lists, and sixteen-coordinate lists match. Topological order differences in the upstream forms are harmless; the full target stream's actual topological order is separately checked exactly.

The recoder receipt was also freshly fetched and authenticated to its exact Git blob, and its bytes match the producer's frozen data byte for byte. Twelve directly fetched sources are authenticated in `source_connector_pins.json` by recomputing Git's `SHA1("blob "+length+NUL+bytes)`. Their repository commit is `2d887f0fa768fd67f3e545d83f8998b5780e530d`. `pins.json` records all reviewed binary, JSON, theorem and semantic sources by SHA-256 and byte count. Existing theorem files from the prior independent semantic audit are additionally frozen there.

## 3. Exact numerals and paid arithmetic

The coefficient language consists solely of decimal integers; fixed `2^t`; fixed `1+4+...+4^(t-1)`; and constant-only additions, subtractions and multiplications. Each exponent is a source integer, every recipe reference points to an earlier constant, and no recipe references an input or runtime gate. Exact division by three in the geometric identity is checked to have zero remainder.

All 8,160 recipes are evaluated exactly, including unused interned intermediates. Every runtime occurrence of a coefficient is checked against the actual intended integer, including the negative frame coefficient, all 2,030 slope-class numerals, the native radix multiplier and the huge E-pair numeral. This proves coefficient exactness independently of recipe-expression formatting.

For exponent n, the two affine maps are `(2,0,1,0)` and `(2,1,2^(2n+1),2(4^n-1)/3)`. Their multiplier is exactly the least dyadic integer at least `max(8,s+4,1+max(a+c,b+d))`, namely `2^551890` here. The exponent-zero class is retained: its one-head V slope is 2, distinct from the zero-head baseline 1.

Runtime powers of recoder q or history P are actual multiplication gates, not coefficient recipes. Fixed exponentiation only describes ordinary literal coefficients. This is a scalar arithmetic-circuit count, not bit complexity or a bound on expanded coefficient storage.

The independently built literal E-pair has width 397,488 and value bit length 319,867. Its exact value equals the source coefficient. In particular all terminal zeros are part of the width and are not discarded by the shorter binary numeral.

## 4. Positive coordinate and parameter domains

All 797,135 existential coordinates have domain strictly positive integers. The census is:

- 98 auxiliaries in two disjoint complete recoder namespaces
- Eight additional supplied positive loader coordinates: spread, canonical beta, N, ell, v, g, T, X
- 794,976 native selector hats and 2,030 native selected-history hats
- Seven native outer coordinates: width slack Z0, final sentinel Vfinal, initial phase code, height slack, two histories and global slack
- Sixteen retained native kernel coordinates

These sum to 106 loader plus 797,029 native coordinates. No unhat selector or unhat class product is itself asserted positive: it is a nonnegative difference of a positive hat and one, or a sum of such differences. Unused classes and unused chronological choices use hat one and are therefore allowed.

On every supplied positive tuple, before native classification, X>0, P0=X+Z0>=2, Vfinal>=1, Uf=P0*Vfinal+X>P0,Vfinal,1, and D=Uf+phase_initial+height_slack>=5 exceeds the needed endpoint and phase code. With positive fixed K, B=KD is positive. Selector hats give J>=0 and P=(B-1)J+1>=1. Every unhat pack is nonnegative by its exact polynomial identity, so the joined Z is nonnegative, F3=16Z+8>=8, and q_native=16P^797011>=16. The native projected positive definitions are therefore valid before the desired AND/history interpretation.

The first native global comparison, at a zero, forces P>1 and J>0, then B<=P and the required no-carry bounds. This is not assumed for free on arbitrary tuples. The retained exact-width lane contains P0 and P0-1; it has not been deleted when adding the external width equality.

The recoders receive positive ports: first input x+1 and supplied positive spread; second input and output both the constant one. Their internal conceptual ports input*J+1, Kmask+1, Ahat and qP are positive before their theorems are applied. For either fixed width k>=4, B=2^(k-1)q^k>=8q^2 on every positive q, so no circular native-geometry typing is used.

For a selected c.e. set, the valid finite U15 initialization has q_B>=2 and fixes P_e=(01)^(8q_B), a nonempty suffix S_e ending in 11, and a finite left-tape integer M_e. Then a_e=val(P_e)>0, p_e=2^|P_e|>0, s_e=val(S_e)>0. The last two coordinates are the exact value/width of `E(A_0 xi_0 (a_0 xi_0)^M_e B_0 xi_0)`. Their displayed fixed finite geometric recipes give C_e>0 and L_e=K^(M_e+2)>0, including M_e=0. They are coefficients after selecting the language, but degree propagation for the single unspecialized polynomial treats all six externals as degree one.

No arbitrary positive five-tuple is claimed to describe a valid program. Nor may the five parameters be existentially reselected for every x; that would describe a different language relation.

## 5. Both recoders, exact exponent, and exact native history boundary

The complete generic recoder theorem is imported at its full positive converse: every positive input u<2^h and every h>=2 has a full positive extension. It is not merely an existence assertion for some larger exponent. All 34 comparisons and 49 auxiliaries remain in each instance. The source replaces only the private q-power prefix and scale constant of the pinned complete width-four source.

For the first recoder, u=x+1>=2 and the retained positive input slack s satisfies u+s=q0. The sole extra canonical guard s+beta=u+1 yields u<q0<=2u. Since q0 is dyadic, q0=2^bit_length(u), including the equality endpoint q0=2u. Conversely s=q0-u>0 and beta=2u+1-q0>0. The denominator-cleared signed frame expression then uniquely fixes N to the full finite LSB tape value; its suffix makes N>0. The computed signed expression is never used as an unconditionally positive native argument.

Only the first recoder receives this guard. The second instance has positive input/output one, width 397,488, and no canonical or dyadic-duration predicate. The complete converse permits every h>=2; the shifted quotient is one here, so no zero-coordinate defect arises when the unshifted quotient vanishes.

For this second recoder, J is congruent to h modulo B-1 and B=2^(kh+k-1)>h+1. The two equations `(B-1)v+ell=J` and `ell+g=B-1`, with positive v,ell,g, place both ell and h in `[1,B-2]`; thus ell=h exactly. The third equation ell=N+1 fixes h=N+1, without modular aliases or a power-of-two restriction on h. Conversely v=(J-h)/(B-1)=sum_(1<=j<h)sum_(0<=i<j)B^i>0 and g=B-1-h>0, including the N=1 boundary. N=0/h=1 are neither needed nor silently admitted.

The exact fixed K=2^397488 and paid equation K*T=Q1 now force T=K^N. The unary value comparison uniquely forces the complete initial E numeral X, since K-1 is nonzero. The independent additional comparison P0=L_e*T binds its **exact** width. The native positive supplied slack Z0 and its computed definition P0=X+Z0 are retained. This closes the earlier existential padding problem at the same width.

For completeness, each original E block is nonzero and has at least two terminal zeros, so the exact concatenated E word has 0<3X<P0. Choose Zstrong=P0-3X>0, apply the full strong native converse at that very dyadic width, and map to Zweak=Zstrong+2X=P0-X>0. Alternatively the pinned complete weak-cone converse directly applies at the same width. Neither argument changes the word, appends padding, or substitutes an arbitrary computed difference for a positive supplied coordinate.

The exponent in the native scale is the fixed lane count **797,011**, unrelated to the first canonical bit length n, the extracted exponent h=N+1, or the existential history duration. Native history duration remains arbitrary and nonempty; there is no external runtime cutoff.

## 6. Native source transfer and finalizer completeness

The audited raw upstream slope-class template has the same maps, selectors, class order, baselines, transports, controller/range/radix lanes and precise input-width lane as the reconstructed source. The source's grouped V terms distribute to every actual one-head selector. Equal numeric appendants retain distinct chronological selectors.

The phase source evaluates the polynomial identity

    B*Next+phase_initial-Q-mP
      =m*(Shat0+Shat1)-(B-1)*Tphase+phase_initial-(J+3m)

with J and P expanded from their actual definitions. The prefix-sum motif gives coefficient m-i on pair i and subtracts m(m-1), exactly yielding Tphase. This identity holds over arbitrary integer tuples, not only on typed histories or at zeros. Horner packing, binary powers and repunit doubling are likewise polynomial identities without divisions. Hence the entire native component is the imported complete polynomial after explicit coordinate renaming and scheduling identities.

The native unit product has precisely three sign-safe norm factors and one checksum. The first norm is a square modulo four; the main norm is never 3 modulo four; the auxiliary factor is congruent to one of two squares. If their integer product is one, every factor is ±1, and these exclusions force all three norms and the checksum to be +1. The retained strong auxiliary comparison is essential and is present. Six positive native definitions and the odd positive root-gap map restore the parent coordinates exactly under the hypotheses reviewed above. No unrestricted checksum from either recoder has been multiplied into this product.

The independently generated list has 10 native residuals, 34+34 complete recoder residuals, one canonical guard, one frame equation, three extraction equations, one unary-scale equation, one unary-value equation, and one exact-width equation: 86 in all. Every one is squared and included once in the actual source finalizer

    U*(1+sum R_j^2)-1.

Over integers, the second factor is a positive integer. A zero forces it and U to equal one, hence every residual is zero; the converse is immediate. U need not be positive away from solutions. This avoids the unsound alternative of adding a free-standing sum of squares to an arbitrary signed native polynomial.

The finalizer is exactly 260 paid operations: 86 differences, 86 squares, 85 sum additions, one addition of one, one multiplication by U and one final subtraction. There is no hidden separately finalized loader polynomial.

## 7. Soundness, completeness, and remaining theorem boundary

Fix a valid program tuple representing a c.e. set S. A positive zero first yields all comparisons by the integer-unit argument. The two recoders identify the canonical LSB input x+1, exact finite tape integer N, and exact unary scale K^N. The value/width equations identify one literal E word. Native soundness yields actual finite emptying from that word. The previously audited corrected tag/Genera/Grill simulation then yields the designated U15 accepting head. The represented fixed semidecider decodes x+1, subtracts one and recognizes S, so x belongs to S.

Conversely, an accepting U15 computation has the reviewed no-short-queue and unique accepting-head properties; normalization produces a permitted unique H; the corrected Grill bridge empties from the exact E word. At canonical n and at h=N+1, both imported complete recoder converses supply all positive auxiliary coordinates. The explicit positive loader coordinates above and the exact-width native converse supply the remaining witnesses. Namespaces are disjoint except their intended positive ports. Every residual vanishes and U=1, hence the complete polynomial vanishes.

The native word-closure soundness permits a certificate containing a post-halt suffix: it concludes actual emptying at or before closure length, never physical execution after emptying. The source bridge separately gives its genuine first-empty cleanup time. This distinction is retained.

The accepted result is therefore a conditional, explicitly sourced **universal positive-program-slice construction** with a measured full source ledger. The historical complete native/Pell and finite-U15 universality theorems, and the earlier semantic source audit, remain genuine imports. This pass did not independently rebuild every historical kernel proof, execute upstream code, materialize an actual enormous unary U15 input, or exhibit an enormous complete Pell witness.

## 8. Reproduction and bounded supplementary evidence

Run in this audit directory:

    python check_exact_source.py > fresh-exact.json
    python -O check_exact_source.py > fresh-exact-optimized.json
    python check_interfaces.py > fresh-interfaces.json
    python -O check_interfaces.py > fresh-interfaces-optimized.json

Both checkers use explicit checks, never removable Python assertions. Normal and optimized receipts agree byte for byte in each pair. The exact checker authenticates dependencies before consuming the raw source. Its runtime is about ten seconds in the observed environment, without requiring materialized runtime values of the full source.

`check_interfaces.py` independently checks 4,095 canonical inputs; 585 literal finite U15 frames; 128 unrestricted-exponent and positive extraction cases, including nondyadic exponents; 16 literal actual-alphabet E-prefix/unary-queue cases including M_e=0; 4,096 exhaustive norm residue cases; and 6,929 signed unit-finalizer cases. The E cases verify exact program C_e/L_e formulas, strong/weak same-width slack transport and rejection of extra padding. These checks supplement the parametric proofs and are not finite substitutes for the complete converses.

The separate producer-side independent full-size modular reviewer reports seven whole-source differential assignments and the same structural ledger. That review is useful corroboration, but this audit's exact row and coefficient result does not depend on its outputs.
