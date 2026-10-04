# Independent review of the complete padded binary reversal source

Status: PASS on the frozen author trio below. The complete source, mathematical interface, and exact degree pass. One wording correction in the optional Hadamard paragraph was made before this freeze: the off-diagonal contribution lies outside the band when `i!=j`. There is no remaining requested correction.

The reviewed relation has strictly positive external parameters `x,q,z` and 48 strictly positive existential coordinates. Its claimed projection is precisely `q=2^n`, `n>=2`, `0<x<q`, and `z=reverse_n(x)`, including leading zero positions in the specified width. It is a local fixed-arity reversal relation. It does not normalize the length of `x`, include the zero word, or improve a universal Diophantine operation bound.

## Exact source and polynomial audit

The fresh independent checker reads the frozen dilation129 JSON as inert data and reconstructs the successor from an explicit 19-row outer schedule, the 47 literal geometry rows, and the 64 AND rows with exactly the two declared input rebindings. It reconstructs all 34 comparisons and the entire ordinary sum-of-squares finalizer. Every register and every supplied parameter/witness is live; the predecessor object remains unchanged.

The independently derived ledgers are:

| Object | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Producers and 34 retained comparisons |66|64|130|
| Complete single-polynomial source |100|131|231|

The finalizer pays 34 residual subtractions, 34 squares, and 33 additions. Fixed-numeral multiplications are included. The graph has no supplied logarithm, exponentiation primitive, bitwise operator, or uncharged equality test in its polynomial evaluation.

The reviewer separately specifies all 34 residuals in the actual supplied variables. In particular, both native norm systems use the actual computed scales, `q` and `16qP`, and the actual main indices, `J` and `and__r`. Exact sparse integer-polynomial expansion agrees with every emitted residual and the whole final output. The latter has 362 nonzero monomials. Its only degree-40 monomial is

`2^48 * and__w^4 * and__s^8 * and__k^4 * q^12 * P^12`.

The unique degree-20 residual is `and__L9-and__R9`; every other residual has smaller degree. Thus degree 40 is attained on the declared ordinary polynomial variables, without a genericity assumption or an off-zero semantic identification.

## The smaller geometry bootstrap

The original geometry47 theorem states the containing identity `B=8q^2`; its source cannot simply be assigned a new `B` while quoting that statement. The new proof supplies the necessary extension. Positivity of `x+input_slack=q` gives `q>=2`. The paid `B=q+q` and `J=B+index_beta` then give `r=J>=5` and `r>q`. The other paid bounds give `X>r`, `Y>=3`, `E=XY>r+1`, and `a=Y(X+1)>2r+1` before any dyadic or population conclusion.

I traced the rank, signed-index, and parity arguments at this smaller threshold. With `P0=2XY^2+1` and `A=a+2`, one has `P0>A>1`. The first Pell index `v` satisfies `v>=r+1>=6`; the ratio comparison and monotonicity give main index `p>=v+1>=7`. Consequently

`c>(2A-1)^(p-1)>A^6>A*(A^2-1)^2`,

as well as `c>2p` and `c>Yk>6v>2(2r+1)`. These are sufficient for the relaxed auxiliary rank theorem, which yields `f=chi_A(m)`, `c|m`, and `m>=c>2p`. It also gives `f>2c` and makes the computed normalized root `U=jc-(2r+1)` positive. The two fixed-minus congruences recover `p=2r+1`; the generic parity theorem then gives `r` odd. That theorem needs the displayed bounds, not the older numerical threshold `p>=513`. The first index becomes exactly `v=r+1` by its residue and the upper bound `k<c`.

The ratio proof remains valid at every integer `r>=5`. Its lower estimate uses `6XY^2>a`, valid already at `X>=6,Y>=3`. It yields `Y>=X^r` and `a>X^(r+1)` before any small-error estimate. Each of the needed elementary inequalities holds at five and improves thereafter:

- `4r/(r+1)^(r+1)<1/2`;
- `2*4^r<(r+1)^(r+1)`;
- `16r/(2^(2r+1)+1)<1/2`.

The exponent congruence therefore gives `X=2^(2r+1)`. The strict fractional tail below one quarter and ratio error below one half give the same central-binomial floor formula for `Y`. Finally, `r>q` permits reduction modulo `2q`; odd `Y/q` gives `q=2^popcount(r)`. No bit field or selector typing was assumed during this argument.

The original positive converse construction also extends to odd `r>=5`: the ratio estimates give positive `eta,zeta`; recurrence congruences and growth give positive integral `h,ga,tau`; and the auxiliary construction with `m=2c(2r+1)` gives positive integral `i,j,o,y_aux`. Its two minus congruences use the already specified oddness of `r`. These are parametric Pell arguments, not finite witness tests. For the smallest admitted synchronized width, `n=2` gives `q=4,B=8,J=9`; the weaker threshold is needed only before synchronization.

## Typing, synchronization, and reversal

The AND source is exactly the prescribed-scale64 interface with

`scale=qP`, `Hhat=2xK+1`, `Mhat=qJ+1`, `Zhat=Ahat`.

The actual paid padding is `32xK+12` and `16qJ+10`, with native scale `16qP`. All restored relation ports are positive before any equations. Therefore the complete native projection applies without circularly assuming its digit bounds: it gives dyadic `qP`, the strict input ranges, and the selected output. The geometry proof separately supplies dyadic `q`; hence `P` is dyadic. The two paid repunit equations then force

`q=2^n`, `B=2^(n+1)`, `P=B^n`, `J=sum_(i<n)B^i`, `K=sum_(i<n)(2B)^i`, `n>=2`.

Here the population of `J` synchronizes the exponent with the external width. This is not an equality of uncharged logarithms. The converse input ranges follow directly from `2xK<qP` and `qJ<qP`.

Set `V=n+1`, `W=n+2`. A bit of `2xK` has position `Wi+j+1`; a mask bit of `qJ` has position `Vt+n`. Equality implies

`V(t-i)=i+j+1-n`.

The right side lies between `1-n` and `n-1`, strictly inside one multiple of `V`. Thus `t=i` and `j=n-1-i`. The blocks are disjoint, so this reasoning has no binary carry ambiguity. The AND output is exactly `qR`, where `R=sum_(i<n)bit_(n-1-i)(x) B^i`.

Since `B=2^(n+1)=2 (mod q-1)`, `R` is congruent to the intended reversal `z0`, with `1<=z0<=q-1` and `R>=z0`. The emitted quotient comparison is exactly

`Ahat-1=q*((q-1)*(quotient_hat-1)+z)`.

Together with `z+output_slack=q`, it gives the unique representative `1<=z<=q-1`. In particular the all-ones result is `z=q-1`, the positive representative of residue zero. The quotient hat is positive because its decoded quotient may be zero. This avoids excluding short-support cases or the all-ones word.

For every intended word, the canonical outer values and both positive native extension theorems provide a full witness tuple. Conversely every positive zero has the stated geometry, selected word, and output. None of this invokes a bounded sample as the unbounded soundness or completeness argument.

## Evidence and limitations

The reviewer fully read the author helper/proof and the following inert mathematical dependencies: dilation129, geometry47, prescribed AND63/64, the relaxed auxiliary rank proof, the half-parameter main-index proof, and the generic fixed-minus parity proof. Their exact bytes are pinned in the companion receipt. The wider archived source ancestry and all earlier executable evidence were not replayed.

Fresh independent finite checks cover all 2,035 nonzero words of widths two through ten, including nine all-ones cases, all five outer comparisons, input ranges, and positive outer witnesses. Separate quadratic-ring calculations at odd indices `r=5,7,9,11,13` verify the two initial Pell norms, strict ratio slacks, odd scale, and positive integral `h,ga`. These partial tuples need not satisfy the new repunit bound and are not full geometry or native Pell zero witnesses. No enormous full auxiliary Pell extension was materialized. The independent exact symbolic checks, rather than these finite cases, establish the recorded source identities and degree.

Frozen author pins:

- Python: `ed6e355f365f78015e5326d087047923b47967936a95712e1c8372b0481ef0ca`.
- JSON: `1ef05ab68b9de6030d71abcdb2a3caeb2932d53b531192d99937b018d7c17197`.
- Markdown: `d5af03d5d30cb3e0a851d2c2a29bf17beb6a3373657a6ca295d2a9a1804a8c73`.

Fresh independent reviewer normal and `-O` exact-receipt replays both passed from `/`. The checker authenticates all three author files, the actual predecessor JSON binding, and the author's recorded dependency bytes; its receipt equality is type-exact and rejects duplicate JSON keys. No author or predecessor helper was executed by this reviewer.

Independent reviewer PY SHA-256: `51165a75a54560368dedf6d2034fd2dec2571cfec8ee46b27dea44ab3da29874`.

Independent reviewer JSON SHA-256: `89a9aa81c6e1ff3452ca628fe59b1263f53d0f3a148562d9e580afd90a85fec0`.
