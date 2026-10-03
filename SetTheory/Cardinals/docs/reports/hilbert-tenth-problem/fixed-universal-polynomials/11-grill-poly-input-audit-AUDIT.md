# Independent audit of the Grill universal-input semantic contract

Date: 2026-10-03. Status: **PASS at the semantic gate, conditional on the explicitly imported complete native kernel and finite-U15 universality theorems.** No correction to the reviewed semantic formulas is required. This is not approval of an as-yet-unemitted large arithmetic/history circuit, an actual operation ledger for that circuit, or a new fully instantiated universal polynomial.

Reviewed subject: `reviewed_semantic_contract.md`, copied unchanged from the requested packet. SHA-256: `7aed950759736e6b6a30f36ef7515dabb4d87ca0ed02240638d121f7a8b06d5c`.

No repository was edited, no upstream Python was executed, and no repository was cloned. All executed tests were independently written for this audit. Seventeen relevant repository sources were fetched at commit `2d887f0fa768fd67f3e545d83f8998b5780e530d`; their saved bytes were checked against the connector's exact Git blob SHA-1. URLs, Git blob IDs, and SHA-256 values are in `source_pins.json`.

## 1. Decision and precise remaining gate

The mathematical composition is consistent:

1. A complete, canonically bounded width-32 recoder determines the least-significant-first input blocks of `x+1`.
2. The finite U15 frame formula determines a strictly positive right tape integer `N`.
3. A second complete recoder on input and output both equal to 1 supports every exponent `h>=2`. Its repunit residue, with two positive bounds, forces `h=N+1` without modular aliases.
4. Its certified power supplies the exact unary scale of the tag input. The second denominator-cleared equation determines both the literal E numeral and its exact width.
5. The corrected tag macros and accepting-head invariant, followed by the two-generation normalization, meet the corrected Grill bridge's persistent-phase and unique-H halt interface.
6. Retaining the native positive width slack and adding the width equality closes the earlier existential-padding problem at the same width.

The next justified step is to finish and independently inspect the literal fixed alphabet/table, then emit the actual two-recoder-plus-loader-plus-history source with all comparisons in its finalizer. Passing the current gate is not a substitute for that source audit.

The two most important implementation traps are:

- The **first** recoder gets the canonical bit-length guard. The **second does not**: applying a canonical guard to its input 1 conflicts with its required `h>=2` and would kill the intended exponent graph.
- The second recoder must not include the dyadic-duration variant's extra low-block AND predicate. Here `N+1` may be any integer at least 2, not just a power of two.

## 2. Complete recoder imports were checked at their actual domains

The direct generic-width theorem is [gpcp_fixed_program_input_bridge.md, Section 1](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/gpcp_fixed_program_input_bridge.md). I also read its literal source recipe, the complete 132 parent, the 130 same-polynomial rewrite, the 129 raw-geometry theorem, the shared-B geometry47 proof, and prescribed-scale AND64's contract. The generic source changes only the paid fixed power chain and scale coefficient. For fixed `k>=4`, it retains all 34 comparisons and 49 positive auxiliaries.

On a complete positive zero, the theorem supplies

    h>=2, q=2^h, Q=q^k, B=2^(k-1)Q,
    P=B^h, J=sum_(j<h) B^j,
    Kmask=sum_(j<h)(2B)^j,
    0<input<q, output=spread_k(input).

Conversely it supplies every positive native auxiliary for every such input and exponent, not just for some sufficiently large exponent. This universal-in-the-exponent converse is essential for binding the second exponent to `N+1`.

The premise `B>=8q^2` holds on every positive supplied tuple when `k>=4`, before any recoder conclusion. The conceptual AND ports `input*J+1`, `Kmask+1`, `Ahat`, and `qP` are also positive before typing. Thus the positive-domain imports are not circular. The geometry and prescribed-scale AND together synchronize the repunit exponent with the binary exponent of q; neither an uncharged logarithm nor an independently chosen history duration is being used.

For input=output=1 the exact outer values are especially transparent:

    A=(J AND Kmask)=1,
    Ahat=2, quotient_hat=1,
    input_slack=q-1>0, output_slack=Q-1>0.

The shifted quotient is indispensable here: its unshifted value is zero. The complete positive native converse still applies, including padding for absent Boolean classes. The audit's small tests check these outer values and premises, not astronomical complete Pell solutions. Their existence remains the imported parametric theorem.

## 3. Exact canonical binary(x+1), separately from duration extraction

Set `u=x+1` with `x>0`, so `u>=2`. The first complete recoder has input u, width 32, spread output R0, and existing positive slack `s0` satisfying `u+s0=q0`. Add positive `beta` and the equation

    s0+beta=u+1.

Together these give `u<q0<=2u`. Since q0 is dyadic, it is exactly `2^bit_length(u)`. For a power-of-two u the upper endpoint is allowed and `beta=1`; changing the upper bound to a strict one would be wrong. For `u=1`, no allowed exponent exists, but the external shift deliberately excludes this case.

The complete converse can therefore be applied at this particular canonical n. It gives `Q0=2^(32n)` and `R0=sum bit_i(u)*2^(32i)` with the required positive witnesses. This n is unrelated to the second recoder's exponent h or to a packed Grill history duration.

Independent census: 4,096 small u values and 36 larger boundary cases, through 512 bits. Each allowed u has precisely its canonical exponent; u=1 has none. An extra high input bit makes the canonical beta nonpositive; deleting the top bit makes the existing input slack nonpositive.

## 4. Primary U15 convention and the finite-frame arithmetic

I checked the primary [Neary–Woods 2009 paper](https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf), especially Definition 3.1, Table 1, Table 16, the finite clockwise-TM boundary-marker construction, and the U15 discussion. The saved primary page images were inspected visually. The head is on the final c of `G=bc`; the blank is c; Table 16 has its sole missing entry at `(u10,b)`. The paragraph naming `(u10,c)` is inconsistent with its own table, and the reviewed contract correctly uses the table. No infinite periodic background is imported.

With c=0 and b=1, ordinary blocks are `A_i=(01)^(8i-5)11`, so `B0=A2 A1` and `B1=A1 A2` each have 32 bits. Literal little-endian evaluation gives

    c0=3941247658, c1=3937053418,
    c1-c0=-4194240.

The negative difference is correct. It differs in sign from a most-significant-first framing argument; it must not be replaced by a presumed positive difference. The output N is a supplied positive coordinate, so this signed fixed coefficient does not violate a native positive-input premise.

Writing `p=2^|P_e|`, `a=val_LSB(P_e)`, `s=val_LSB(S_e)`, `K0=2^32`, `m0=K0-1`, literal concatenation gives

    N = a + p*[c0*(Q0-1)/m0 + (c1-c0)R0 + s*Q0].

Clearing the nonzero fixed denominator is exactly the contract's displayed equation. The suffix `S_e=A_right A_left` is retained and ends in 11, so N is positive and its finite support is exact. Zero source bits produce whole B0 blocks; they are not omitted. The left integer M is constant for the fixed represented program, with the bit nearest the head at position zero.

The fixed program can decode the physical sequence of LSB-first pairs, subtract one, and recognize the selected c.e. set. This changes the represented finite program, not a varying external arithmetic computation. The imported U15 initialization theorem permits that ordinary input convention. The proof need not claim correctness on malformed U15 encodings.

Independent checks compare all 29 actual primary-table instructions with a sparse two-sided tape implementation in 29,696 contexts. Both move directions, both scanned bits, and zero tape integers are covered. Another 1,056 literal frame cases check the signed formula and full suffix/prefix widths.

## 5. Exponent extraction: positive and alias-free

Use a fresh second complete generic-width recoder with input and output 1. Its theorem already gives `h>=2`, `q1=2^h`, `B=2^(kh+k-1)`, and `J=sum_(j<h)B^j`. Introduce positive ell, v, g and impose

    (B-1)v+ell=J,
    ell+g=B-1,
    ell=N+1.

The first equation gives `ell=h mod(B-1)` because every power of B has residue 1. The second places ell in `[1,B-2]`. For `k>=4` and `h>=2`, `B>=2^(4h+3)>h+1`, so h is in the same interval. Two integers in this interval cannot differ by a nonzero multiple of B-1. Hence ell=h exactly and h=N+1.

Conversely, for N>=1 set h=N+1 and use the complete recoder converse at that exponent. Then

    v=(J-h)/(B-1)
      =sum_(j=1)^(h-1) sum_(i=0)^(j-1) B^i >0,
    g=B-1-h>0.

At the smallest abstract boundary `k=4,N=1,h=2`, the values are `B=2048,J=2049,ell=2,v=1,g=2045`. There is no zero-quotient defect. N=0 would require excluded h=1 and is not admitted by this interface; the physical suffix proves that no valid input needs it.

The extraction is the pre-dyadic portion of [native_binary_dyadic_duration_recoder.md, Section 3](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_dyadic_duration_recoder.md), applied to the old unrestricted recoder. It does not import that variant's later predicate `ell AND (ell-1)=0`.

Independent tests cover 192 exponent cases including nondyadic h, check the explicit positive quotient formula, and reject nearby modular aliases. They also verify the input=1 shifted quotient and output=1 in each case.

## 6. Exact unary E loader and the native width interface

Let N_G be the eventual fixed normalized alphabet size, distinct from the tape integer N. All symbols in the initial source word are original symbols of width one. Their E blocks have exact length `b=196(N_G+1)`, so the repeated pair has length `k=2b`. Put `K=2^k`. The second complete recoder's certified port is

    Q1=q1^k=K^(N+1).

The positive supplied T with `K*T=Q1` is uniquely `K^N`. For the fixed program prefix F_e and repeated source pair U,

    C_e=val_LSB(E(F_e)), L_e=2^|E(F_e)|,
    V=val_LSB(E(U)),
    (K-1)X=(K-1)C_e+L_e V(T-1),
    P0=L_e T.

These are exactly the geometric-series value and width of `E(F_e U^N)`. Since K-1 is positive, the value equation determines X uniquely. Width-zero pair/dummy symbols that arise later in the normalization do not occur in this initial word, so they do not alter k or L_e here.

The bridge's literal corrected E blocks have positive values and many terminal zero bits. Their exact concatenation has `0<3X<P0`. Retain the weak native positive slack Z0 and its existing definition `P0=X+Z0`; bind that computed width to `L_e T`. Do not delete Z0 and merely presume the positivity of an arbitrary computed difference before applying a native theorem.

On a complete zero, this equality forces the precise initial bit width. On a genuine halt, choose `Zstrong=P0-3X>0`, use the full strong native converse at this exact width, and map to `Zweak=Zstrong+2X=P0-X`. No padding argument is needed or permitted. The native word-closure theorem and its weak-cone successor were read at their full soundness/converse interfaces.

The program-dependent frame coordinates are valid constants for each represented set, or free program parameters specialized to valid slices of one polynomial. They must not silently become arbitrary existential choices when stating recognition of a selected set. The contract already keeps this distinction.

Independent literal E tests cover 192 prefix/repetition cases, three alphabet sizes, M=0..3, N=1..16, exact value and width, strict strong cone, same-width positive slack transport, and 192 rejected six-zero extensions. Actual U15 N is already enormous even for tiny x, so these tests intentionally do not materialize the actual unary word or its full Pell certificate. The symbolic formulas, not finite materialization, establish that case.

## 7. Tag and Genera halt boundary

The [Cocke–Minsky primary paper](https://cs.famaf.unc.edu.ar/~hoffmann/cc18/p15-cocke.pdf), pp.16–19, uses already-read finite control and finite binary tape integers, which match the refinement and tape arithmetic above. The printed p.19 image really does show `t0 -> beta0` without its filler, while the next claimed configuration has paired repeats. The reviewed construction explicitly changes that rule and proves its own local macro; it correctly avoids presenting a silently corrected transcription as the paper's exact table. The new explicit left rotation is a separate finite schema, not an appeal to an unspecified symmetry.

The normalization was additionally assigned an independent direct audit against the pinned [corrected halt bridge](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/grill_tag_halt_bridge.md) and the creator's Genera semantics. Its result is PASS, conditional on the accepting-head invariant. See `normalization/AUDIT.md` and its independently written checker/receipt.

The key invariant is a two-layer one. At an original-symbol layer, erasing d leaves the unnormalized generation. Original symbols alone contribute to phase. Processing them gives only pair symbols plus width-zero d; processing that layer expands the pairs and gives the next original-symbol layer. Its phase is exactly the phase after the first pass, including when the erased original word has odd length. Dummy expansion changes neither erased output nor phase.

A first H is emitted only on the expansion pass. Every symbol before it in that output is original or d, whose hypothetical next productions contain pairs/dummies and no literal H. The published hypothetical-prefix condition therefore holds. Pair symbols containing H are distinct nonhalt symbols and cannot trigger H early. The unique-head proof excludes multiple H emissions in the preceding original generation.

The normalization checker reports 819,907 two-generation identities, including 585,642 odd erased inputs, and 237,750 unique-H prefix tests. These validate the implementation of the invariant, not a finite substitute for its proof.

## 8. Mandatory source-level obligations before a large emission can pass

- Give the complete numeric alphabet, disjoint original/internal/pair/dummy/H symbols, widths, and every phase production literally. Check each H-bearing pair and ensure no other output emits H.
- Keep the two recoders' 49-coordinate native auxiliary sets and register namespaces disjoint, except for the explicitly intended ports. Distinguish canonical n, extracted h, tape N, alphabet N_G, and arbitrary history duration.
- Emit the paid shift, canonical guard, both complete recoders, extraction constraints, signed frame equation, exact unary value/width equations, and the actual complete fixed Grill history.
- Retain all supplied positive ports and slacks. Review computed native input positivity before typing; in particular do not use the sign of the frame expression away from a zero.
- Place every added residual inside the native integer-unit finalizer `U*(1+sum r_i^2)-1`. Do not add an external sum of squares to an arbitrary possibly negative native polynomial. Over integer tuples the displayed product forces U=1 and every residual zero.
- Count the actual new fixed table, binary power chains, scalar products, comparisons, finalizer, witness set, and degree. Neither the three-phase 205 example nor the reject-all example supplies this ledger.

## 9. Resolved count provenance, not a semantic defect

The original exact-width loader and its independent review at the pinned commit give 16,291 operations. The distinct [factored128 packet](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_recoder_factored128.md) and its review give 16,289 for `exact_width_grill`, by two same-polynomial coefficient factorizations. I checked both notes. Thus 16,289 is legitimate when labeled as the factored successor; it is not the old exact-width file's own ledger. Neither count applies to the new universal-input schema.

## 10. Reproduction and limits

Run only the independent audit script:

    python independent_outer_checks.py
    python -O independent_outer_checks.py

Both runs passed and matched the complete receipt byte-for-byte in content. The script uses explicit checks, not removable assertions, and imports no producer module. Its main counts are stored in `independent_outer_checks.json`; normal and optimized logs are retained. The separate normalization directory contains its own proof and replay instructions.

This audit reviewed the complete pinned theorem contracts and their compatibility, including the stated positive converses. It did not independently rebuild all historical Pell-kernel source dependencies, construct their giant witnesses, execute upstream author code, or certify the new literal source/history before it exists. Subject to that explicit theorem-import boundary, no narrower mathematical gap was found in the two-recoder input composition or the normalization.
