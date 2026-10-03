# Paid two-recoder ordinary-input loader

Status: emitted and checked. This file proves the input-composition interface; it does not claim that the separate native history has been emitted, validated, or counted here. The imported complete recoder and native-history theorems remain explicit proof dependencies.

## Literal source and trust boundary

`input_loaders.py` executes only newly written orchestration over the compact DAG API. Its only upstream executable-looking content is the inert JSON `input_recoder130_receipt.json`, fetched with the GitHub connector at commit `2d887f0fa768fd67f3e545d83f8998b5780e530d`. Its Git blob is `c52224469f5644d99214f13559fb54d7c414aea6`; SHA-256 is `175c498990a8e63de7a91d1e3d321ef90a19f129f305074f0c6de10967d0a182`. The blob hash was recomputed over the actual saved bytes. The emitter checks the SHA-256 on every receipt load.

The complete 130 source has 49 positive auxiliaries and 34 comparisons. For a fixed k>=4, replace only its first three gates `q2=q*q; Q=q2*q2; B=8*Q` by the ordinary left-to-right binary multiplication chain for `Q=q^k` and `B=2^(k-1)*Q`. The remaining 127 gates and all 34 comparisons are retained. The old private `q2` has no other consumer. The chain uses `bit_length(k)+popcount(k)-2` multiplications. Fixed integer numeral recipes have no variable operand and do not assert any variable power relation for free.

The mathematical import is the complete generic-width theorem in [gpcp_fixed_program_input_bridge.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/gpcp_fixed_program_input_bridge.md), based on [recoder130](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_input_dilation130.md). For every positive input z_in<2^h with h>=2, the full positive converse supplies all 49 auxiliaries, and the 34 comparisons force exactly

    q=2^h, Q=q^k, B=2^(k-1)Q,
    P=B^h, J=sum_{j<h} B^j,
    Kmask=sum_{j<h}(2B)^j,
    z_out=sum_j bit_j(z_in)2^(kj).

This is the full raw positive extension, including geometry and prescribed-scale AND, not a replacement by selected outer equations. The recoder's conceptual AND ports `z_in*J+1`, `Kmask+1`, `Ahat`, and `qP` are positive before its equalities are used. For arbitrary positive q and k>=4, `B=2^(k-1)q^k >= 8q^2`; thus the geometric bootstrap is available before recoder conclusions. The existing independent semantic audit reviewed these imports and their converses. This packet checks transcription and composition, not a new proof of the underlying Pell rank theorem.

## Disjoint positive coordinates and program parameters

The six external positive coordinates are

    x, a_e, p_e, s_e, C_e, L_e.

For each represented c.e. set, the five e-coordinates are fixed to that program's valid finite-frame values. They are not existential choices that may select a different program for each x. `build(..., external=None)` creates them with backend role `external`; a caller may instead supply those six previously declared external handles.

`canonical_input_bits__*` and `unrestricted_tape_exponent__*` each allocate their own 49 native recoder auxiliaries. Their coordinate sets are disjoint. There is one further positive first-recorder spread output and seven positive loader witnesses: `canonical_beta,N,ell,v,g,T,X`. Thus there are 106 positive existential coordinates in this module. The native history must reuse X as its queue port rather than silently identifying unrelated coordinates. All computed intermediates are ordinary integer arithmetic; signed frame expressions are never declared positive native inputs.

## First recoder: canonical ordinary input

Pay one addition `u=x+1`. Since x>0, u>=2. Supply positive R and call the full generic recoder with `(input,output,k)=(u,R,32)`. Its input slack s satisfies `u+s=q0` at a zero. Add a positive beta and the paid equation

    s+beta=u+1.

Hence `u<q0<=2u`. The recoder gives q0 a power of two, and the unique such power is `2^bit_length(u)`. The upper endpoint is included; at a power-of-two u the genuine beta is 1. Conversely, at n=bit_length(u), s=2^n-u and beta=2u+1-2^n are positive. The complete generic converse applies at that particular n, yielding positive auxiliaries, `Q0=2^(32n)` and `R=sum_j bit_j(u)2^(32j)`.

## Literal right tape value

The physical U15 input blocks have the exact little-endian values

    c0=3941247658, c1=3937053418, c1-c0=-4194240,
    K0=2^32, m0=K0-1.

With positive supplied N, pay

    m0*N = m0*a_e + p_e*c0*(Q0-1)
                    + p_e*m0*(-4194240)*R + p_e*m0*s_e*Q0.

The first recoder's existing `modulus=Q0-1` register is shared; it is not recomputed for free. On a valid program slice, the right side is exactly the denominator-cleared little-endian value of `P_e B_w0 ... B_w(n-1) S_e`. Because m0 is nonzero, the equation uniquely forces N=N_e(x). The literal nonzero suffix ends in 11, so this genuine N is positive. Off the zero set the expression may have either sign, which causes no typing problem because N is itself a positive supplied coordinate.

## Second recoder: unrestricted exponent

The literal normalized alphabet has 1013 symbols, so

    a=28(1013+1)=28392,
    b=7a=198744,
    k=2b=397488.

Call a fresh complete generic recoder with input=1, output=1, and this k. Retain all 34 comparisons and all 49 positive auxiliaries. The single gate `copies=1*J` becomes an alias under the backend's ordinary multiplication-by-one simplification; its value and every consumer are unchanged. No native comparison or auxiliary is dropped.

This recoder has **no canonical-length guard** and **no dyadic-duration predicate**. Its full theorem permits every h>=2, with `q1=2^h`, `Q1=q1^k`, `B=2^(kh+k-1)` and `J=sum_{j<h}B^j`. The shifted quotient is important: for input=output=1 its genuine value is 1, even though the unshifted quotient would be zero.

Pay three equations with positive ell,v,g:

    (B-1)*v+ell=J,
    ell+g=B-1,
    ell=N+1.

Reducing the first modulo B-1 gives ell congruent to h. The second gives `1<=ell<=B-2`. Since k>=4 and h>=2,

    B>=2^(4h+3)>h+1,

so `2<=h<=B-2`. Both representatives lie strictly within one modulus interval, and therefore ell=h=N+1 without a modular alias. This allows nondyadic h without restriction.

Conversely, for any positive N, choose h=N+1, use the full recoder converse at that exact exponent, and set

    v=(J-h)/(B-1)=sum_{j=1}^{h-1}sum_{i=0}^{j-1}B^i>0,
    g=B-1-h>0, ell=h>0.

This supplies the added coordinates positively. The excluded h=1/N=0 case is unnecessary because the valid frame has N>0.

## Exact literal E pair and unary loading

The literal source IDs used by the repeated initial pair are `b:00=300` and `x:00=539`, each an original width-one symbol. The emitter verifies their names, IDs, widths, and the 1013-symbol alphabet. It uses the corrected E formula from [the halt bridge](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/grill_tag_halt_bridge.md):

    gval(r)=2*(4^r-1)/3,
    A=2^7*(gval(a-3)+2^(2a-5)*gval(7)+2^(2a+10)*gval(a-4)),
    val_LSB(E_y)=A*2^(14y), |E_y|=b for width-one y.

Consequently the exact fixed pair value is

    V=A*2^(14*300)+A*2^(b+14*539), K=2^k.

Its constant-only recipe uses `pow2`, `geom4`, and fixed addition/multiplication; no enormous decimal constant is expanded in the emission. An independent literal-bit implementation checks the actual pair against the backend's exact recipe value. The value's bit length is 319867 while the pair's exact width is 397488. In particular `0<3V<K`; terminal zeros remain part of its width.

Supply positive T and pay `K*T=Q1`. Since h=N+1, this uniquely forces `T=K^N`. Supply positive X and pay

    (K-1)*X=(K-1)*C_e+L_e*V*(T-1).

On the fixed program slice, C_e is the exact value of the source prefix E(F_e), and L_e is `2^|E(F_e)|`. As K-1 is nonzero, the displayed equation uniquely gives

    X=C_e+L_e*V*(1+K+...+K^(N-1)),
    target_width=L_e*T.

This is precisely the value and exact binary width scale of E(F_e(b:00 x:00)^N). It does not discard zero source bits or permit queue padding. The compiled E word gives `0<3X<target_width`, so the native strong-cone converse can be applied at this very width.

The caller must retain the native positive width slack Zweak and its paid definition `native_width=X+Zweak`, and append the comparison

    native_width=target_width.

At a genuine halt choose `Zstrong=target_width-3X>0`; transporting to `Zweak=Zstrong+2X` is positive and gives exactly the same width. Replacing the positive supplied native slack by an arbitrary computed difference is not allowed.

## Required finalizer interface

The returned 75 pairs are equations, not an already finalized polynomial. Add the native-width equality once, and put every one of these residuals into the same integer-unit finalizer as the full native history:

    U*(1+sum_i r_i^2)-1.

Over integers, a zero forces the integer factors to multiply to 1. Since `1+sum_i r_i^2` is a positive integer, it is 1, U=1, and every r_i is zero. This is the composition that permits importing the native relation's integer-unit interface. An external sum of squares added to an arbitrary signed native polynomial would not suffice.

## Exact local ledger

All counts below are measured from the new emission, not copied from the reject-all example or any old loader.

| Part | Multiplications | Additions/subtractions | Operations |
|---|---:|---:|---:|
| Complete width-32 recoder | 70 | 63 | 133 |
| Complete width-397488 recoder, input/output 1 | 87 | 63 | 150 |
| Paid shift, guard, frame, extraction, queue, target width | 16 | 11 | 27 |
| Total loader before finalizer | 173 | 137 | 310 |

The second recoder's unsimplified source has 151 gates; `1*J` removes exactly one multiplication. The raw two-loader source would therefore have 311 gates. The measured 137 additive gates are 108 additions and 29 subtractions. All 310 gates are reachable from the returned comparison ports and exact width port. The backend independently confirms all 112 inputs (106 witnesses plus six external ports) are used.

There are 34+34+1 canonical+1 frame+3 extraction+1 scale+1 queue = 75 comparisons. The native-width binding adds one more outside this module. If appending to an existing nonempty residual-square accumulator, each new comparison costs one subtraction, one square, and one accumulator addition: the 75 module comparisons cost 225 additional finalizer gates, and the width comparison costs another 3. These are conditional incremental counts only; the actual complete ledger must be read from the full composed DAG, including any sharing or additional native ports.

The largest loader comparison degree is exactly k+1=397489: the second recoder's first repunit comparison has the nonzero monomial `2^(k-1)q1^k J`. Every other term there has lower degree, so this degree is attained. The raw kernel comparison degrees are at most 20; extraction and the second mask also have degree at most k+1. Thus the standalone sum of these 75 squares has exact degree 794978. This is not a degree claim for the uninspected complete native polynomial.

## Verification and its limits

Run `python input_verify.py` and `python -O input_verify.py`. Both compare against the same frozen validation receipt. Explicit checks are used rather than removable assertions. The independently assembled raw-kernel formulas cover every native comparison, including norm, shifted-index, parity, bounds, Boolean fields, and the input/output bounds.

The deterministic checks cover:

- 768 complete generic recoder residual identities, at six widths, half positive and half signed arbitrary assignments
- 192 complete two-loader modular residual identities at three primes, including all 75 pairs and the target-width port
- 1023 canonical-bitlength cases, including dyadic endpoints and adjacent forbidden lengths
- 128 positive exponent-extraction cases including nondyadic h
- 24 literal unary queue value/width/strong-cone cases
- The actual 1013-symbol alphabet's fixed E pair value, checked exactly against the corrected literal bit strings
- Actual compact-backend operation counts, roles, formal comparison degree, gate/input reachability, and a reproducible diagnostic DAG hash

`input_backend_probe.cdag` and its JSON are reachability diagnostics only: their root is the sum of all residual squares plus the exact-width square. They are deliberately not a proposed zero polynomial or the full native finalizer. The tests do not materialize full giant Pell witnesses, an actual unary U15 input, a complete halting history, or a fixed-program universality witness. The symbolic full converses above, together with the imported theorems and valid program slices, establish those existential interfaces.
