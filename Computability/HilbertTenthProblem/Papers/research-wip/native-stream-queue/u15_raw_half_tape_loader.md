# A paid ordinary-input loader for U15 raw half tapes

The literal generic-width recoder can initialize the Neary–Woods U15 machine's raw binary half tapes with **five additional arithmetic operations**. The complete supplied-output relation costs **138=73M+65A**, has36 comparisons and50 positive existential coordinates, and a conservative sum-of-squares finalizer costs245=109M+136A, degree66. These are loader-only counts. The recoder's full positive extension is inherited from its existing proof; the finite checks do not materialize the enormous Pell witnesses.

The main algebraic improvement is to clear the fixed denominator of the 32-cell block repunit and absorb the fixed program frame into three positive numerical coefficients. No input block repunit is supplied. A uniformly scaled-tape variant costs one less multiplication in the loader, but pays additional scaled-bit products in the subsequent recurrence, so the raw form is the recommended composition interface.

## Computational and bit conventions

The underlying universal machine is the same fixed29-instruction binary U15 table already retained in `neary_woods_explicit_universal_tm.py`. Its published source is [Neary and Woods, Four Small Universal Turing Machines](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf), especially the effective Turing-machine/clockwise-machine/bi-tag constructions, Tables1–3, and Table16 on PDF page17. The repository note `neary_woods_explicit_universal_tm.md` gives the existing paid ordinary-input proof and explains the source's halting-symbol typo. This loader changes the represented recognizer's input convention explicitly; it does not identify the two numeric word orientations.

For a word in the physical tape symbols c=0,b=1, define

    low(w0...w_(r−1)) = Σ_(j<r) [w_j=b]·2^j.

The character nearest the head is the least significant bit of either half. Let `qB` be the number of ordinary bi-tag letters. The physical word for ordinary symbol a_i followed by its separator is

    A_i = (cb)^(8i−5) bb.

In particular `|A_1|=8`, `|A_2|=24`. Choose the represented Turing recognizer's input convention to be:

    bit0 → (a1,a2),       bit1 → (a2,a1),
    bits listed least significant first, with any trailing zero padding.

For any c.e. set S of positive integers, a deterministic recognizer for this convention exists effectively: decode the pair sequence, interpret its bits in little-endian order, discard zero padding beyond the last1, and simulate a recognizer of S. The clockwise/bi-tag simulation carries that convention through its fixed program. The end markers still delimit the finite input; zero padding does not mean deleting physical cells. With n≥2, the initial dataword contains at least six ordinary letters, as in the existing repository universality proof. Leading-zero padding in the old most-significant-first convention becomes trailing-zero padding here.

This is why no bit-reversal function has been smuggled into the arithmetic loader. The finite recognizer is changed before producing its fixed bi-tag program. At each ordinary input x, the paid recoder supplies x's ordinary least-significant-first bits directly.

The two physical32-cell blocks are

    B0=A1A2,     B1=A2A1,
    c0=low(B0)=3937053418 = 0xeaaaaaea,
    c1=low(B1)=3941247658 = 0xeaeaaaaa,
    δ=c1−c0=4194240 > 0.

The old big-endian GPCP encoding uses the opposite pair assignment to keep its own coefficient difference positive. Reusing those names without accounting for orientation would be wrong.

## Exact program parameters and half tapes

Let the valid bi-tag program have qB≥2 ordinary symbols, h≥2 markers, and active production dictionary as in the source's `bts_program`. Let a_right,a_left be its ordinary boundary symbols. The retained source's `encoded_configuration` writes

    PROGRAM · b · [head c] · (cb)^(8qB) · B_(x0)...B_(x_(n−1)) · A_right A_left,

with infinitely many c blanks outside the finite word. The current state is u1=A and the current head bit is0.

Define fixed positive program quantities

    L_S = low(reverse(PROGRAM·b)),
    κ = 2^(16qB),
    ρ = low((cb)^(8qB)) = 2(κ−1)/3,
    σ = low(A_right A_left),
    M = 2^32−1 = 4294967295.

L_S is positive because the adjacent left cell is b; σ is positive because each symbol block contains b. These integers depend only on the represented program, not on x or its padding length.

The existing paid recoder at width32 proves, for some n≥2,

    q=2^n,   0<x<q,   Q=q^32=2^(32n),
    z=spread32(x)=Σ_(j<n) bit_j(x)·2^(32j).

The mathematical block repunit `T=(Q−1)/M` need not be a witness. Reading the right tape away from the head gives exactly

    R_S(x,n) = ρ+κ(c0 T+δz+σQ).                    (1)

This explicitly places the initial e1 word at the low end and the two blank-boundary markers at the high end. It includes every padding B0 block.

Multiplying (1) by M and collecting terms gives

    M R_S + Dfull = Afull Q+Bfull z,
    Afull=κ(σM+c0), Bfull=Mκδ, Dfull=κc0−Mρ.

All three coefficients are positive. In particular

    Dfull = 1073741888·κ+2863311530 > 0.

The constants M and c0 have common divisor257, so every full coefficient is divisible by257. Use the smaller fixed odd denominator and positive program parameters

    m=M/257=16711935,
    A=Afull/257, B=Bfull/257, D=Dfull/257.

The supplied raw output R0 is constrained by

    m R0+D=A Q+B z,        L0=L_S.                  (2)

For valid fixed program parameters, the paid recoder theorem and (2) force exactly the intended tapes for some allowed padding n. Conversely every x>0 has arbitrarily large allowed n, the full recoder positive extension exists, and the literal positive tapes satisfy (2). Globally the relation may have multiple tape outputs for different padding lengths; it is not claimed to be one padding-independent numeric function. Every such padded physical input accepts exactly the same x in S.

For arbitrary positive parameter quadruples `(L_S,A,B,D)`, the source still defines an integer polynomial relation, but no valid program interpretation is asserted. Universality needs one effective valid fixed slice per language, exactly as with the older three-parameter GPCP frame. This loader alone supplies no halting predicate.

## Literal operation source and composition

The complete source is emitted by `build(scaled=False)` and saved in the JSON receipt. Its first133 rows are the existing actual `gpcp_fixed_program_input_bridge.recoder(32)`: the radix16 parent's two q-power multiplications become five squarings, and all34 comparisons remain. The five appended rows are

    raw_Q_term = A*Q
    raw_z_term = B*z
    raw_sum = raw_Q_term+raw_z_term
    raw_scaled_R = 16711935*R0
    raw_shifted_R = raw_scaled_R+D

with comparisons `raw_shifted_R=raw_sum` and `L0=L_S`. Thus the append costs3M+2A, not free multiplication by a large fixed numeral. Parameters are x, four positive program numbers, and two positive supplied tape outputs. The50 witnesses are z plus the49 positive recoder coordinates; the tape outputs become witnesses only when the caller existentially quantifies them.

| Form | Certificate | Comparisons | Positive internal witnesses | SOS polynomial |
|---|---:|---:|---:|---:|
| Width32 recoder with supplied x,z |133=70M+63A|34|49|234=104M+130A|
| Raw two-output loader |138=73M+65A|36|50|245=109M+136A|
| Scaled two-output loader |137=72M+65A|36|50|244=108M+136A|

The generic-width recoder's residual-degree bound is33 at width32. The new loader residuals have degree at most33 before projection, and its new parameters do not increase that bound. Exact univariate source evaluation attains degree33 in a recoder residual, so both displayed SOS polynomials have degree66. The stronger unit-product recoder finalizers can be composed separately; the table deliberately gives a simple SOS baseline, not the best standalone recoder polynomial.

For root's complete history composition:

- Use only `source`, `comparisons`, `parameters`, `auxiliaries`; do not append this packet's standalone SOS finalizer.
- Alias the initial left tape directly to the positive program parameter `program_L`, then omit `L0=program_L` and the redundant supplied L0. This leaves35 loader comparisons at the same138 source rows.
- Treat R0 as the shared positive initial-right witness, counted once. Keep its five-row equation; it is not a free decoded input.
- Share or rename the recoder's Q and all native auxiliaries explicitly before assembling the history source. Do not assume the input duration n is the computation duration k.

## Optional scaled tape form

For scaled outputs use `L0=mL_S`, `R0=mR_S`. Keep A,B,D unchanged and compute

    raw_output=A Q+B z−D

in2M+2A, comparing it with R0. There is no division operation. All intended outputs are positive.

For a history representation storing m times both raw tapes, multiplication/push preserves that scale. A pop equation is `2T'=T−m r`. If T=mU, then because m is odd and T' is an integer, U−r is even; hence T'=m(U−r)/2 is again a scaled natural tape. This proves exact integer recovery inductively from the valid initial scale. No free divisibility predicate is introduced.

However root's current packed recurrence would then need `mW`, `mU`, and `m(2ZW+ZU)`, costing three shared constant multiplications. Saving one loader multiplication need not improve the composed source; under that schedule it adds two operations overall. The raw form is therefore primary.

## Evidence, API and limits

Public `build(scaled=False)` rejects non-Boolean mode values. `parameters(q,h,productions,right,left,scaled=False)` checks exact integer types, complete active keys, exact tuple output shapes, marker/alphabet ranges and mode. It returns `program_L/A/B/D`. All20 explicit repository dependencies are byte-pinned before their ordinary sibling imports; the receipt records their hashes. Parent files and receipts are unchanged.

The source checker has passed:

- 192 arbitrary full source/residual/SOS evaluations, including96 signed assignments;
- 2,286 literal `encoded_configuration` comparisons covering six fixed program fixtures, x=1,...,127, and three padding choices;
- 4,572 substitutions through the actual two loader DAGs, checking all five outer recoder equations and both tape comparisons;
- exact univariate degree certificates and both complete operation ledgers.

The remaining Pell coordinates in those outer fixtures are placeholders. These fixtures are not reported as complete positive zeros. The full positive extension is the existing recoder theorem, whose literal source is retained. Tests of synthetic bi-tag program encodings verify orientation and coefficient recipes, not that every such synthetic program is a universal recognizer.

Run `python u15_raw_half_tape_loader.py --write-receipt` to regenerate or run without flags to compare the adjacent deterministic receipt. Its proof/construction uses the repository's primary-source input theorem plus the explicit new orientation and coefficient identities above. It does not strengthen the87-operation global universal theorem.

## Separate possible transfer to the completed GPCP source

The same coefficient precomputation suggests an actual smaller existing U15 compiler, separately from the new history route. Its current paid GPCP frame is

    V=a(pQ+c0J+δz)+b,       Q=MJ+1.

On the retained repunit comparison it equals

    V=Anew·J+Bnew·z+Cnew,
    Anew=a(pM+c0), Bnew=aδ, Cnew=ap+b.

All three new program numerals are positive on each valid old program slice, and the new expression is positive on arbitrary supplied positive tuples. The seven old body/frame gates become four, saving2M+1A. The same three program-parameter slots can carry the new coefficients. This is a valid-slice parameter transformation, not a bijection between arbitrary old/new parameter tuples. Before the repunit equation, the exact difference is

    Vold−Vnew=ap·(Q−MJ−1).

The current744 history compiler still has that input-body/frame layout on inspection, making a741 candidate plausible. This scout has not implemented or reviewed that production rewrite, its consumer/privacy conditions, complete off-zero source correction or new formal degree. It is a concrete next step, not a certified741 result, and would leave87 unchanged.
