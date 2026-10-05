# Independent review of the complete84 cross-block stopping point

**PASS in the stated restricted scope; no correction requested.** I read the full frozen author note `complete84_cross_block_next.md`, SHA256 `f528326b033473e288c20da5ceb72bfd4cd94198ecfea11bf54f758a0ab3d5d5`. Its companion checker and receipt were authenticated as inert bytes at SHA256 `5197d2da12b8d2e8b17d0fc5953898d242f769a5417797deac192f01708f4b64` and `d9794f7ebb9678635846bf0444edd7635857ce15f7275bbb5dbc672aea697616`, respectively. The checker was not executed or imported; its implementation is not separately certified by this proof review.

## Read scope and source binding

I read the entire84-row `packet.source` array and its supplied-port lists in `complete84_scaled_strong_output.json` as inert JSON, and the complete associated mathematical note. I also read `complete75_half_binomial_compiler.md` Sections1–4, including the actual shifted fixed-mask recipe. No source, supplied, predecessor or frozen helper was executed or imported, and no repository file was changed. The mathematical argument is proof-only; it needs no finite experimental inference. Fresh standard-library data inspection additionally compared the entire saved tied array with the parent, checked its topological order and liveness, and counted its operations; it did not execute either arithmetic circuit or any author checker. The earlier bounded-scout novelty summaries are not independently re-audited here.

Authenticated source files in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue`:

- `complete84_scaled_strong_output.json`: SHA256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`.
- `complete84_scaled_strong_output.md`: SHA256 `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`.
- `complete75_half_binomial_compiler.md`: SHA256 `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117`.

## Eight multiplications for the specified monomial cut

The actual register map is `q=q`, `k=R10b`, `X=wn2`, `Y=sn2`, `E=UM`, `Z=kY=ksn2`, `U=EZ=first_root_base`; here the proof's `Z` is not the supplied source witness named `Z`. The eight charged source multiplications are source rows4–8,10–11 and50:

```
Lbig = q*q
n2 = Lbig*q
wn2 = w*q
sn2 = s*n2
UM = wn2*sn2
ksn2 = R10b*sn2
first_root_base = UM*ksn2
hpm1 = h*UM.
```

The seven required boundary values are therefore the distinct monomials

`q^2, wq, sq^3, wsq^4, ksq^3, kws^2q^7, hwsq^4`

in independent paid leaves `q,k,w,s,h`. Each is a nonleaf, so any multiplication-only monomial DAG producing all seven uses at least seven multiplication gates. If exactly seven sufficed, every produced register would be one of these seven targets: there would be no non-target intermediate.

Consider the gate that first produces `Y=sq^3`. Multiplication adds nonnegative exponent vectors. Each operand must divide `Y`, so it cannot contain `k,w` or `h`. Among the other six targets, only `q^2` divides `Y`. The available nonscalar operands could thus only be `q,s,q^2`; no product of two of them is `sq^3`. A scalar factor cannot supply missing variable exponents. This contradiction proves the eighth multiplication is necessary. The displayed actual source attains eight using `q^3` as the extra intermediate.

The bound also survives removal of `q^2` from the required boundary, which matters when combining cuts. Producing `Y=sq^3` alone needs at least three multiplication gates from degree-one leaves `q,s`: with at most two gates, reaching total degree4 forces the second gate to square the first degree2 monomial, producing only even exponents, unlike `(3,1)`. Every ancestor of `Y` is free of `w,k,h`, since nonnegative exponent vectors cannot cancel. Each of the other five required targets contains at least one of these variables, so it requires its own distinct gate outside that ancestor cone. Thus the six-target version still costs at least `3+5=8M`. This strengthening closes the potential interaction in which the tied index rewrite stops requiring `q^2` as an external output.

The lower bound is sharp for this cut, not for the complete polynomial. In particular it assumes the stated six or seven boundary outputs and no additional paid product donors. It permits sharing among the targets but excludes additions/subtractions, cancellation, division, zero-set replacements, changed coordinates and alternative boundary charts. The paid addition `R10b=eta+zeta`, the construction of `q`, and every other complete-source gate remain outside the count. No global84-operation optimality or complete-source obstruction follows.

## A six-operation index rewrite ties the actual source

Let `g=gap`, `J=Jrep`, and `b=Bm1`, with the literal source relation `q=bJ+1`. The old tail, using already paid `q^2`, has six operations:

```
Lm1 = q^2-1
rproduct = g*Lm1
qMF = q*MF
mask_factor = MC+qMF
mask = mask_factor*J
R = rproduct+mask.
```

It costs3M+3A and gives `R=g(q^2-1)+(MC+q MF)J`. The alternative same-interface schedule

```
t = b*g
u = t+MF
v = q*u
v2 = t+MC
s = v+v2
R = J*s
```

also costs3M+3A, with every intermediate consumed. Its expansion is

`J[(q+1)b g+q MF+MC] = g(q^2-1)+(MC+q MF)J`.

This is an exact commutative-ring identity after substituting the actual source relation; there is no division, norm equation or positivity premise. Independent receipt inspection found exactly84 rows,79 common names,78 literally unchanged definitions, and precisely the six displayed replacement rows. The free/witness arrays are unchanged. The new source is topological, has47 multiplications and37 additions/subtractions, and all84 rows and25 free ports are live. Induction through the unchanged remaining definitions transfers the local identity to all79 common computed values and the complete output; exact degree187 and positive-zero equivalence are inherited from that full polynomial identity. The schedule does not require an extra supplied numeral. It is a tie, not a reduction. Because `q^2` is already a required monomial-cut output, this count does not hide its production cost.

For the alternative factorization `J[(b g+MF)(q+1)+MC-MF]`, the fixed difference may be precomputed on a fixed compiler slice, again giving six operations; if it must instead be formed from symbolic numeral ports, that variant incurs another addition. Actual `MC-MF` cannot vanish: the compiler's native `MC` is even, native field mask is divisible by4, and the source port is `MF=native_MF+B-1`, which is odd since `B=2^d`. This source-port distinction matters; the source `MF` is not the unshifted one-cell mask. The same-interface schedule above avoids any precomputation convention.

## Outcome

The proposed monomial cut is already sharp at eight multiplications; the displayed index refactor is an exact six-operation tie. These bounded results do not rule out a cheaper complete construction using additive identities, donors outside the cut, a different chart or another circuit. They make no new universality, witness-count or degree claim.
