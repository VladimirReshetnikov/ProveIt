# Independent review: infinitely many negative-index common-kernel solutions

## Verdict and scope

**PASS for the proposed ten-equation subsystem theorem.** There are infinitely many assignments with fixed `q=16`, `X=32768`, `Y=4096`, all supplied kernel witnesses other than the index positive, and `R=-p<0`, satisfying all ten equations displayed in `pell_kernel_half_binomial42.md` §1. The source's *positive-index external hypothesis* is deliberately not imposed. The claim is that the equations plus common scales do not recover that hypothesis.

This is a genuine obstruction to proving index positivity from this kernel alone. It is **not** a full positive child zero, a false acceptance, or a counterexample to the complete74 universal theorem. No assignment to the outer packing, transport, compiler, or input system is supplied. In particular, irrational-rotation density for the freely chosen progression in `p` does not imply density on any further subsequence imposed by those omitted equations.

Reviewed proposal: `provisional_negative_kernel.snapshot.md`, SHA256
`0efa25dacf9afeb24f71f1c65ebb312952e067d21a81783963d1f1187399981d`.

The exact upstream text is pinned to `VladimirReshetnikov/ProveIt` commit `2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff`. `source_manifest.json` records URLs and both SHA256 and verified Git blob hashes for the kernel, fixed-minus sign proof, and odd-quotient identities. No upstream code was run, no upstream source changed, and nothing was published. The existence proof does not require materializing its enormous witnesses.

## 1. Exact constants and independent quadratic fields

The proposed constants are exact:

`E=134217728=2^27`, `a=134221824`, `A=134221826`, `H=536887299`, `P=1099511627777=2^40+1`.

They give `X=8q^3`, `Y=q^3`, `X<H`, and `A<P<2A^2-1`. Since `A` is even, `Delta=A^2-1` is odd, so its squarefree part is odd. On the other hand,

`P^2-1=4XY^2(XY^2+1)=2^41(2^39+1)`.

Its 2-adic valuation is exactly 41, so its squarefree part is even. Both discriminants are positive nonsquares; their real quadratic fields are distinct.

Let `epsilon=A+sqrt(Delta)` and `lambda=P+sqrt(P^2-1)`, with logs `alpha,beta>0`. If `alpha/beta` were rational, some positive powers `epsilon^r=lambda^s>1` would agree. The shared value belongs to the intersection of the two distinct quadratic fields, which is `Q`. Its norm in the first field is one, whereas the norm of a rational value `z` in a quadratic field is `z^2`; positivity would force `z=1`. This is a contradiction. Thus `alpha/beta` is irrational. No unproved multiplicative-independence assumption remains.

For an optional concrete pin, independent integer factorization gives

`H=3*13*13766341`, `ord_H(2)=2753268`,
`T=lcm(4,2E,ord_H(2))=184768687767552`,
`L=E/2=67108864`, `n0=L-7=67108857`.

The order was verified by modular exponentiation and exclusion of every prime divisor of the proposed order. An explicit order is not required by the proof; finiteness already follows from odd `H`.

## 2. Arithmetic progressions and the density argument

For positive integers `u,v`, define `p=15+Tu`, `n=n0+Lv`. These satisfy all required congruences without a compatibility gap:

- `p=3 (mod 4)` because `4|T`
- `2^p=2^15=X (mod H)` because `ord_H(2)|T`
- `2n=1-p (mod E)` because `2n0=E-14=1-15 (mod E)`, `2L=E`, and `E|T`

This uses explicit compatible arithmetic progressions rather than an unstated CRT solvability assertion.

Put `K=L*beta>0` and

`C=log(sqrt(P^2-1)/(2sqrt(Delta)))`,
`theta_u=(15+Tu)*alpha-n0*beta+C`.

The affine quantity in the proposal is `theta_u-Kv`. Since `T*alpha/K` is irrational, the residues of `theta_u` modulo `K` are dense, and every nonempty open interval is visited by arbitrarily large positive `u`. This is the standard elementary irrational-rotation density fact: the pigeonhole principle produces arbitrarily small nonzero rotation steps, whose finite positive multiples meet every interval; applying the same statement after any starting iterate makes every tail dense.

Choose a nonempty open interval `I` whose closure lies strictly inside `(log Y,log(Y+1))`. Its length is smaller than `K` (here the upper endpoint itself is already smaller than `K`). Infinitely many positive `u` admit an integer `v` with `theta_u-Kv in I`. For these hits,

`v=(T*alpha/K)u+O(1)`,

so `v` is positive and tends to infinity. Consequently both `p,n` tend to infinity. This is an actual two-index existence argument; it does not require the two integer indices to be chosen independently after imposing the interval.

The exact Binet formula gives

`log(psi_A(p)/(2psi_P(n)))`
`=p*alpha-n*beta+C+log(1-exp(-2p*alpha))-log(1-exp(-2n*beta))`.

The final two terms tend to zero along those hits. Taking a smaller `I` with a fixed positive margin to the target endpoints therefore proves, for infinitely many sufficiently large hits,

`Y<psi_A(p)/(2psi_P(n))<Y+1`.

There is no rounding assumption, numerical-log argument, or finite-search inference here. The narrow interval only makes numerical construction difficult; it does not obstruct density.

## 3. Every first/main equation and positive slack

Define `c=psi_A(p)`, `D=chi_A(p)`, `k=2psi_P(n)`, `tau=chi_P(n)`. These are positive integers. The exact norm identities give the first and main equations:

`tau^2-XY^2(XY^2+1)k^2=1`,
`D^2-(A^2-1)c^2=1`.

The first is exactly the displayed kernel equation `(E^2+X)(kY)^2=tau^2-1`, since `E=XY`. The definitions also give `a=Y(X+1)`.

Set `eta=c-kY` and `zeta=k-eta`. The strict quotient interval proves `eta>0`, `zeta>0`, hence both ratio equations `c=kY+eta`, `k=eta+zeta`. No floor or parity assumption on these slacks is used.

For the projection, the recurrence for `chi_A(p)-a*psi_A(p)` gives residue `2^p=X (mod H)`. Thus `gamma=(D-ac-X)/H` is integral. Moreover

`D-ac=2c-psi_A(p-1)>c>X`

for all sufficiently large `p`, so `gamma>0`. This establishes `D=X+ac+gamma*H` with a genuinely positive supplied projection witness.

Because `P=1 (mod E)`, the psi recurrence gives `psi_P(n)=n (mod E)`. Hence `k=2n=1-p (mod E)`. Set `R=-p` and `h=(k+p-1)/E`; the numerator is positive and divisible by `E`, so `h` is a positive integer. The exact first-index equation is then `k=R+1+hE`, with `R<0` as claimed.

All seven first/main equations in the ten-equation kernel are now verified. The exponent congruence is not replaced by equality; indeed fixed `X` with unbounded `p` is the deliberate wrapped setting.

## 4. Strong auxiliary divisibility, sign selection, and positivity

For every integer `A`, the recurrence modulo two gives `psi_A(p)=p (mod 2)`. Thus odd `p` makes `c` odd, and `m=cp` is odd. Let `f=chi_A(m)`, `Q=Delta*psi_A(m)`.

The expansion of `(D+c*sqrt(Delta))^c` gives the exact divisibility `c^2|psi_A(pc)`: the square-root coefficient's first term is `c*c*D^(c-1)=c^2D^(c-1)`; every later odd term contains at least `c^3`. Therefore `i=Q/c^2` is a positive integer, `Q=ic^2>1`, and

`Q^2=Delta^2*psi_A(m)^2=Delta*(f^2-1)`.

Now take `saux=p+2m`. Since `p=3 (mod 4)` and `m` is odd, `saux=1 (mod 4)` and `baux=(saux-1)/2` is even. The odd-quotient polynomial gives the exact positive integer

`U=chi_Q(saux)/Q=Q_baux(Q^2)`.

Its constant-term identity gives, modulo `c`,

`U=(-1)^baux*saux=saux=p`.

Modulo `f`, use `Q^2=1-A^2` and the second polynomial identity:

`U=(-1)^baux*psi_A(saux)=psi_A(p+2m)=-psi_A(p)=-c`.

The last equality follows directly from `chi_A(2m)=-1 (mod f)` and `psi_A(2m)=0 (mod f)`. This is the required sign flip. Choosing even `m` here would not provide it with the same `p+2m` construction.

Thus `j=(U-p)/c` and `o=(U+c)/f` are integers. Their positivity can be made particularly explicit: `c>p`, `Q>=c^2`, and `saux>=3` imply

`U>=chi_Q(3)/Q=4Q^2-3>c>p`.

Consequently `j,o>0`. For `R=-p`, their equalities are exactly `U=jc-R=of-c`. Finally `y=psi_Q(saux)>0` and the ordinary Pell identity give

`Q^2(U^2-y^2)=1-y^2`.

This verifies all three remaining strong auxiliary equations. The sign proof uses only explicit identities and congruences, not a previous exact-index theorem or a hidden `R>0` assumption.

## 5. Infinite family and evidence boundary

The density argument supplies infinitely many distinct unbounded `p`; the constructed solutions are distinct already in `R=-p`. All definitions preserve fixed `X,Y` and strictly positive kernel coordinates apart from `R`. Accordingly the proposition is stronger than a single isolated auxiliary example: it covers the entire ten-equation common kernel with the actual `q^3` scales.

It does not enforce the complete source's mask packing, transport, positive word/gap variables, fixed compiler compatibility, or input norm. Adding those equations changes the admissible index set, so this free-progression density argument cannot be carried over without a new proof. The full restoration question remains open.

`audit_checks.py` is a new independent supplementary checker. It verifies the pinned source bytes, exact constants, multiplicative order, 1,024 progression pairs, 105 square-divisibility cases, five modular auxiliary sign cases, and one small exact auxiliary block (`A=2,p=3,c=15,R=-3,m=45,saux=93`, largest coordinate 7,939 bits). That last block is explicitly neither a full common-scale kernel assignment nor a full child zero. The full family is established by the unbounded mathematical argument, not by the finite tests; no full common-scale witness is materialized.

The independent check passed. No correction to the proposed theorem is required, provided its subsystem-only limitation remains explicit.
