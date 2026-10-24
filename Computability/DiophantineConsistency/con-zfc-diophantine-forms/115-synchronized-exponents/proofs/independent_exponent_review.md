# Independent ordinary review: replacing fixed squaring chains by a shared exponent

## Scope and disposition

The proposed changes are mathematically valid, provided the proof of power
correctness is staged as described below. In particular, positivity of the new
coordinate `H` must not be assumed from its syntax: it is first recovered from
the new power call with a known positive exponent.

This note reviews the unbounded ordinary argument. It is not a Lean theorem,
an internal object-language ZFC derivation, or an independent check of every
expanded coefficient in a later generated polynomial.

Inspected sources:

* `analysis-root/experiment_powers.py` and its `both/raw_builder.json` output;
* the authenticated 407 source's `code/build_projected.py`,
  `code/additive_index.py`, and `upstream/code/shared_power.py`;
* the same source's `upstream/code/shared_product_power.py`;
* `candidates/projected-factorial-radius/radius_builder.py` and `PROOF.md`;
* `PROPOSAL_REVIEW_QUARTICS407888.md` in the pinned repository.

The literal certificates give label exponent `3,445,908`, rounded carrier
exponent `L = 4,194,304 = 2^22`, local exponent `6,893,253`, and rounded local
exponent `K = 8,388,608 = 2^23`. Thus `K = 2L`.

## 1. The first, separate-exponent rewrite

The original construction uses

    M = ((t+1)^t)^L,       R = 2+t+x+y+M0,       H = R^K,
    M = M0+1.

It computes the outer fixed exponents by repeated polynomial squaring. The
first proposal instead requests the already available existential power
interface at

    (base, exponent, output) = (t+1, Lt, M), (R, K, H).

The elementary identity `((t+1)^t)^L = (t+1)^(Lt)` proves equality of the
intended values. The fixed-power bound `R^K` is also unchanged. The replacement
does not assert that `x^k` is itself a polynomial in variable `k`: it invokes
the explicit quadratic Pell certificate whose existential projection is
exactly that function.

The original script contains precisely these two replacements. Its raw output
starts with the requested exponent atom `L*t`, then the literal exponent `K`.
All semantic power arguments and proposed outputs are allocated before the
private shared-Pell coordinates. The global frame includes all their atoms.

## 2. A strictly more economical shared-exponent variant

Pad the proof horizon to satisfy `t >= 2`, implemented by `t = t0+2` with
`t0` natural. Put

    e = L*t,       M = (t+1)^e,       H = R^e.

Both calls now use exactly the same exponent atom. They therefore share one
indexed-Pell pair and its auxiliary index test in the existing compiler.
There is no change to the intended carrier `M` for a given horizon `t`.
Although the intended `H` is generally larger than its former value, we have

    e >= 2L = K,       H = R^e >= R^K,

because `R >= 4`. Consequently all old local-majorant conclusions remain
valid. This avoids paying for a second independent index solely to encode the
fixed exponent `K`.

More generally, any positive integers `L,K,q` with the label exponent at most
`L` and `qL >= K` support this change when `t >= q`. The exact majorant
exponents can guide a smaller common coefficient. At the delivered horizon
offset q=2, it must be at least
max(3,445,908,ceil(6,893,253/2))=3,446,627; simply taking the label bound
3,445,908 would fail. This separate coefficient-size choice is not used in
the delivered equation.

## 3. Why no circularity is introduced in soundness

At an arbitrary natural solution, all arithmetic input coordinates, all
proposed power outputs, and all literal gate values are nonnegative. The
frame equation is

    W = 2 + sum(distinct bases, exponents, and proposed outputs),
    A^2 - W^3(W+2) Z^2 = 1,       Z >= 1.

This equation is interpreted before the factorial, binomial, CRT, carrier, or
majorant meanings. It gives `W >= 2` and makes `W` strictly larger than every
atom in the finite power inventory, even if a proposed output is initially
incorrect.

For clarity, set `b = W+1` and `Y = WZ`. The frame is

    A^2 - (b^2-1)Y^2 = 1.

The positive Pell classification yields `A=X_n(b)`, `Y=Y_n(b)` for `n>0`.
The elementary congruence `Y_n(W+1) = n mod W` implies `W | n`, hence
`n >= W`. The addition formula or recurrence gives

    A > (W+1)^W > W^W.

No equality involving `H`, `M`, or a factorial was used.

For any individual request whose present base `a` and exponent `k` are known
positive, the indexed-Pell certificate gives `X=X_k(A), Y=Y_k(A)`. Its
modulus row defines

    T_a = 2Aa-a^2-1.

Since `a,k,m < W`, the frame gives `A > a^k,m` and
`T_a >= 2A-2 > a^k,m`. The power-congruence row says

    X_k(A)+(a-A)Y_k(A) = m+T_a q.

The left side is congruent to `a^k` modulo `T_a`; therefore the strict bounds
force `m=a^k`. This proof is pointwise in a request. It does not require the
other requests to have been interpreted already.

Apply it first to the two new requests. Their bases satisfy `t+1>=3` and
`R>=4`, and their common exponent `e=L*t` is positive by literal natural
arithmetic. Therefore they give

    M=(t+1)^e,       H=R^e>0.

Only after this step should the old argument invoke positivity of later
exponents involving `H` and interpret the rest of the power inventory.
All those positivity arguments are now the original ones. For the earlier
separate-exponent experiment the same order works with positive exponents
`L*t` and literal `K`.

The common auxiliary Pell witnesses are simultaneous constraints, but their
soundness lemma can be applied to any selected known-positive exponent.
They are not defined by a recursive attempt to compute `H`. Sharing the pair
for the two equal exponents strengthens neither relation beyond the true
Pell pair, because that pair is uniquely determined by `A` and the exponent.

## 4. Every old use of H survives the larger value

I checked the ordinary projected-radius proof and the direct 407 review for
the potentially dangerous use of exact equality `H=R^K`. Their downstream
estimates use the following consequences:

1. `H` dominates the local source polynomial on the declared finite boxes.
   The literal majorant certificate gives this from `H>=R^K`.
2. `H>=R^4`, and hence `H>=t+2`, `H>=8`,
   `R(R+2)<=H`, and `4R(R+2)<=H` where used.
3. Once the factorial graphs have been interpreted, `T=H!` and `J=t!`.
   Their exact identities concern the present value of `H`; they do not
   require `H` to have been a particular fixed power of `R`.
4. Before validating the product binomial, the actual remainder rows imply
   `B<TQ`, with `Q=(1+(t+1)T)^t+2`. This uses the present `T` and `t`.
5. `T<=H^H`, the aggregate eight-column bound, and `t+2<=H` give the stated
   bounds on all lower binomial coefficients. Larger `H` satisfies the same
   displayed inequalities; no upper bound on `H` in terms of `R` is used.
6. For the candidate-output radius `rho_H=T H^2`, the lower bound
   `(H!)^2>=H^H` and `H>=R^4` supply the strict radix estimate. These are
   pointwise assertions for the present natural `H`.
7. The CRT range theorem uses `H!` to control the small primes and to bound
   source residues. Again, its hypothesis is a lower majorant, not an exact
   power formula for `H`.

Thus replacing `R^K` by `R^(Lt)` with `t>=2` is permitted at every use. The
argument must explicitly state this inequality-based reuse rather than call
the replacement an identity of the old full polynomial.

## 5. Completeness and the order of witness choice

Start with an actual finite C222 refutation. Expand it to the finite proof
tree used by the accepted Horn-flow argument. Select a horizon `t` at least
two, its length, and all four local schema parameters. Increasing this horizon
is allowed because truth steps have zero flow balance and leave the
accumulator unchanged. Padding with these steps preserves the target
derivation and the initial/final accumulator values.

Now choose the witnesses in this order:

1. Choose that `t`, put `e=L*t`, and set `M=(t+1)^e`, `M0=M-1`.
   The unchanged label bound licenses the same flow argument.
2. Build the actual accumulator trace at this carrier. Choose `y`, then a
   suitable beta code `x` and its quotients as in the accepted source proof.
3. Define `R=2+t+x+y+M0` and then `H=R^e`. Its required majorant is now
   automatic. Choose `T=H!`, `J=t!`, the true modulus product, positive CRT
   representatives, and the canonical index.
4. Choose the factorial radii, binomial values, shared radix, all true
   requested powers, and their Euclidean witnesses. Every semantic input
   and output in the finite power inventory is now fixed.
5. Define `W` from those fixed atoms. Choose a frame Pell solution with
   ordinate divisible by `W`; the canonical index `W` already supplies one.
   It gives a sufficiently large `A`.
6. Choose the exact indexed-Pell pairs, the common finite-unit period and
   compatible common auxiliary base, and the remaining quotient witnesses.

The last stage does not change any earlier arithmetic argument. This gives
an acyclic construction of a full natural solution and rules out a hidden
global fixed-point requirement.

The oriented power quotient is also nonnegative: if
`s_k=X_k(A)+(a-A)Y_k(A)`, then

    s_0=1, s_1=a, s_(k+1)=a*s_k+T_a*Y_k(A).

Consequently `s_k>=a^k` and `T_a | s_k-a^k`, so the required quotient is a
natural number for every positive base and exponent.

## 6. Logical strength and packaging requirements

The proof uses finite induction, integer arithmetic, Pell classification,
finite-unit periods, factorial/binomial identities, and the already supplied
C222-to-ZFC refutation calibration. These are ordinary arguments formalizable
in ZFC and remain uniform over the theory's internally represented naturals.
They neither assume `Con(ZFC)` nor assert that the equation has no solutions.

The resulting equation is a new existential presentation of the same
refutability statement. It is not the same polynomial as the old 399-variable
one. The root must still bind the delivered literal residual list to the new
generator, replay every natural restoration, expand the sum of squares, and
report actual variable/degree/coefficient measures and their tradeoffs.

In particular, the initial `both` experiment reduces variables at a sizable
coefficient-height cost. No statement that it dominates all old equations,
or that it is globally simplest, follows from this review.

## 7. Additional review: a latent seed at the common square radius

The later selected architecture uses one shared factorial radius
`rho=T^2`. Its separate factorial lemma and radix estimates require their
own review; this section checks the additional **index compiler** change.
I inspected `analysis-incoming/experiments/shared_square_builder.py`,
`latent_square_builder.py`, and the complete raw ledger at
`common_exponent_latent_square/both/raw_complete.json`.

The semantic power inventory contains exponents `H+rho` and `t+rho`. The
old indexed-Pell compiler would certify them independently. The new version
certifies one extra pair at exponent `rho`, although no arithmetic power
request has exponent `rho` alone, and derives both requested pairs by the
addition law. This is legitimate: the indexed-Pell theorem is a theorem
about a positive integer index, not about membership in a particular list
of requested powers.

### Positivity before interpreting factorials

The literal definition is `rho=T^2`. The variable `T` is a base in the
request `T^t`, whose exponent satisfies `t>=2`. Independently of that
power request's intended meaning, its natural modulus row is

    2AT = T_T + T^2 + 1.

At `T=0` this would read `0=T_T+1`, impossible over the naturals. Therefore
`T>=1` and `rho>=1` before either factorial is interpreted. Furthermore,
`rho+1` is a base in the power inventory. The exact frame sum therefore
gives `W>rho+1>rho`. In particular the new latent index does not evade the
available global numerical bound merely because it is not itself a power
exponent atom.

One can now use the following soundness order:

1. Interpret the known-positive common exponent `e=2^22*t` and recover `H`.
2. Use the literal base modulus row to prove `T>=1`, hence `rho>=1`.
3. Interpret the seed pairs at `H`, `t`, and `rho` by their own indexed-Pell
   certificates, using the same already-present common auxiliary witnesses.
4. Apply the addition identities to get the pairs at `H+rho` and `t+rho`.
5. Interpret the rest of the positive power calls, then the separately
   established factorial/radix/CRT semantics.

This does not infer `T=H!` in order to prove the positivity needed to
infer `T=H!`.

### Exact addition law and the actual dependency graph

For `D=A^2-1`, define `(X_n,Y_n)` by
`(A+sqrt(D))^n=X_n+Y_n sqrt(D)`. Then

    X_(a+b) = X_a X_b + D Y_a Y_b,
    Y_(a+b) = X_a Y_b + Y_a X_b.

These are polynomial identities. They construct natural coordinates from
natural earlier pairs. The inspected raw ledger has exactly these three
derived indices:

* `H+rho` from the independent pairs at `H` and `rho`;
* `t+rho` from the independent pairs at `t` and `rho`;
* `t+1` from the pair at `t` and the literal pair `(A,1)` at index one.

The graph is acyclic. No derived pair is used to justify its own seed
certificate. The raw discriminant row is exactly `A^2=D+1`.

### Common auxiliary completeness with the extra seed

Let `I` be the finite collection of independent indices, now including
`rho`. In the existing common-auxiliary construction, choose a Pell-unit
period modulo `4 product_(i in I) Y_i^2`. This ensures a common positive
auxiliary ordinate `V` divisible by every `Y_i^2`. Its norm ensures
`gcd(U,4V)=1`, so the two congruences defining the common auxiliary base
remain compatible. The original finite-unit argument works for any finite
collection of positive indices. Adding `rho` may make witnesses much
larger, but does not obstruct existence.

It is essential that the finalizer's product run over **all independent
seed pairs**, including the latent one. The actual code does so. The
derived pairs do not require separate factors because their values are
already fixed by exact additions from the certified seeds.

For completeness, choose all true semantic arithmetic values first. This
fixes `T`, `rho=T^2`, and all indices before choosing `W`, `A`, the indexed
pairs, and the common finite-unit period. Thus the extra seed preserves
the acyclic witness order from Section 5.

### Finite no-import audit

`analysis-alternative/check_latent_index.py` imports no producer module.
It reads only the raw JSON, independently expands the literal triangular
rows, and checks:

* `t=t0+2`, `e=2^22*t`, the common exponent binding and the exact `R`;
* `rho=T^2`, the `T^t` request, and the `rho+1` base;
* the global frame equals two plus exactly the distinct power atoms;
* `rho` is a genuine seed although absent as a lone power exponent;
* the global auxiliary product is exactly the product of the squares of
  all fifteen independent seed ordinates, including `Y_rho`;
* the discriminant row and each of the three actual Pell additions;
* the complete index graph is accounted for by those seeds and acyclic
  additions.

It passed on raw JSON SHA256
`338ec15ab7f4782e6c58e21a49f3ea0bddb3d5cf68c9b7554fc211d7e6e3d364`.
The census is 22 arithmetic power calls, 15 independent seeds, and
18 total indexed pairs. The receipt is `latent-index-check.json`.
These exact finite identities complement the preceding unbounded proof;
they do not replace the separate full coefficient and contraction checks.

**Disposition:** the latent-radius index construction is accepted at the
ordinary mathematical level, conditional only on the separately reviewed
shared-square factorial/radix changes and the already accepted source and
arithmetic interfaces. No new premise concerning ZFC consistency is added.

## 8. Supplementary independent proofs for the shared square radius

These arguments independently support the shared-square factorial/radix
change. They are given here because they make the potentially delicate
initial small-value and zero-value cases explicit.

### 8.1 A uniform lower-digit envelope

For all integers `n,rho>=1` and `0<=j<=n`,

    binomial(n+rho,j) <= (rho+1)^n.

If `rho>=n`, the binomial coefficients are increasing up to index `n`, and

    binomial(n+rho,n) = product_(i=1)^n (rho+i)/i <= (rho+1)^n.

If `rho<=n`, every coefficient in the binomial row of order `n+rho` is at
most `2^(n+rho-1)`. This follows by Pascal induction from the row of order
one. The desired comparison is equivalent to

    2^(rho-1) <= ((rho+1)/2)^n.

For `rho=1` it is equality; for `rho=2` it follows from `n>=2` and
`(3/2)^2>2`; for `rho>=3` it follows from `(rho+1)/2>=2` and `n>=rho`.

This bound applies before the factorial output is known. The modulus row
already implies `T>=1`, hence `rho=T^2>=1`. With `H>=t`, the common base
gives `(rho+1)^t <= (rho+1)^H`. Thus the radix

    q = B*((rho+1)^H+1)

bounds all lower digits of both factorial binomials whenever `B>=1`.
The latter follows, as before, from the power-base modulus for `q`.
There is no circular assumption `T=H!` or `rho>=H` in this step.

### 8.2 The first factorial, with candidate-output radius T squared

For `n>=5` write `F=n!`, `S=n(n-1)/2`, and for an integer `T>=1` define

    G_n(T) = (T^2+1)^n / binomial(T^2+n,n)
           = F product_(i=1)^n (T^2+1)/(T^2+i).

The exact ceiling rows say `T=ceil(G_n(T))`. Every product factor is at
most one, hence a solution has `T<=F`. We prove `G_n(T)>T` for every
`1<=T<F`, ruling out all smaller candidates.

* If `T<=n` and `T<=4`, monotonicity in `n` gives `G_n(T)>=G_4(T)>T`.
  The four elementary values are `16/5`, `125/14`, `2000/143`, and
  `9826/570`, respectively. (Only the strict comparisons are used.)
* If `5<=T<=n`, retain just the first `T` product factors. The remaining
  factors are at least one. Each retained factor after the first is
  strictly greater than `i/2`, so
  `G_n(T)>T!/2^(T-1)>T`. The last inequality follows from
  `4!>2^4` and induction.
* If `n<T<=F/2`, the finite product inequality gives
  `G_n(T)>F(1-S/T^2)>F/2>=T`.
* If `F/2<T<F`, the same bound gives
  `G_n(T)>F-4S/F>=F-1>=T` because `n!>=4S` for all `n>=5`.

For the stated four values, direct evaluation of
`G_4(T)=24(T^2+1)^3/((T^2+2)(T^2+3)(T^2+4))` is sufficient; reductions
of the fractions are optional. At `T=F`, the product inequality gives
`G_n(F)>F-S/F>F-1`, while `G_n(F)<=F`. Hence the ceiling is exactly `F`.
We have proved

    T = ceil(G_n(T))  iff  T = n!       (n>=5, T>=1).

The new `H=R^(2^22*t)` is far larger than five, so this theorem applies
directly to the first factorial. The initial zero candidate was excluded
by the actual natural modulus row, not by an assumption of the answer.

### 8.3 The second factorial at the same radius

After the first factorial is interpreted, `T=H!` and `H>=t>=2`. Therefore
`T>=t!`. At the fixed shared radius `rho=T^2`, the second factorial ratio is

    t! product_(i=1)^t (rho+1)/(rho+i).

Its deficiency below `t!` is strictly smaller than

    t! * t(t-1)/(2T^2) <= t(t-1)/(2t!) <= 1/2.

It consequently lies in `(t!-1,t!]`, so its ceiling equals `t!`. This
identifies the proposed second output even if it was initially zero.

### 8.4 The remaining radix estimates

For the true `T=H!`, the paired-factor inequality gives

    (H!)^2 = product_(i=1)^H i(H+1-i) >= H^H.

Consequently the common numerator satisfies

    V_H = ((H!)^2+1)^H > H^(H^2).

The unchanged remainder and aggregate rows give the same upper bounds
on `Q+t` and each encoded column as in the accepted parent. Every remaining
lower binomial index is at most `R`, so its lower digits are at most

    H^[R(R+2)(H+1)].

From `R>=4` and `H>=R^4` we have `4R(R+2)<=H`; thus this exponent is
strictly less than `H^2`. Therefore every remaining lower digit is smaller
than `V_H`, proving the required radix bounds before invoking the
modulus-product identity. This preserves the noncircular parent order.
