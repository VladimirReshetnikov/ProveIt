# Independent audit of the full signed-child negative-index construction

Reviewed mathematical text: `../FULL-SIGNED-COUNTEREXAMPLE.md`, SHA256
`b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd`.
The final text includes the arbitrary-positive-input repunit generalization
and the two editorial clarifications requested during review. The audit
below applies to that exact version.

## Verdict and scope

**PASS.** For every actual fixed compiler export covered by the pinned source,
and every strictly positive ordinary input `x`, the construction below gives
infinitely many strictly positive supplied-coordinate zeros of the
`signed20` parent's **19-coordinate nonlinear-index child**, with

`restored_R = k - hXY - 1 = -p < 0`.

This is a full child-zero construction, including transport, literal shifted
packing, both first/main Pell equations, all strong auxiliary equations, and
the signed input equation. It is not merely a zero of the isolated kernel.
Consequently the proposed positive-coordinate graph inverse does not extend
to every positive zero of this signed child. The result does not construct a
positive parent zero, does not settle the two other children, does not claim
an improved universal bound, and does not identify a particular falsely
accepted input relative to a chosen machine.

The proof uses Dirichlet's theorem on primes in a reduced arithmetic
progression, density of an irrational rotation, and the elementary Pell
identities specified below. It is an existence proof; no giant full witness
tuple or accepting compiler computation was materialized.

## 1. Source and fixed-parameter audit

The equation interface was checked against the cached, pinned files
`complete75_signed_projection_elimination101.md`,
`complete74_nonlinear_index_projection_scout.md`, and the independent
literal-schedule review in `positive-index-bootstrap-independent`.
The scout removes the supplied index and only its first-index comparison,
substituting `R=k-hE-1` in **both** packing and `U=jc-R`.
The complete74 factored first norm is exactly the same Pell equation used
below. The actual paid mask coefficient is `MF_native+B-1`.

The `signed20` packet in the pinned scout JSON was also read directly as
data, without evaluating its schedule. Its eight comparison pairs are
exactly:

1. `innerC=local_rhs_sum`: transport
2. `restored_r=r_lhs`: shifted packing with the restored index
3. `L9=R9`: `(EkY)(EkY+k)=tau^2-1`
4. `L15=R15`: `D^2=1+Delta c^2`
5. `ic22=R16`: `(ic^2)^2=Delta(f^2-1)`
6. `L17=P17`: `(ic^2)^2((jc-R)^2-y^2)=1-y^2`
7. `H17=aux_u_rhs`: `jc-R=of-c`
8. `mu2=norm_rhs`: `mu^2=1+Delta kappa^2`

The source names `Jrep,zquot,y_aux` denote the mathematical coordinates
`J,z,y`. Source register `A` is mathematical `Delta`, not mathematical
`a+2`; `R10b,R10a,R12,R14` are respectively `k,c,a,D`.
The literal paid `MF` port is the shifted compiler numeral. Every source
comparison is therefore covered by the construction below.

The additional compiler source
`complete75_half_binomial_compiler.md`, pinned to commit
`2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff`, explicitly keeps `b,L,d` powers
of five and `B=2^d`. Its cached SHA256 is
`68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117`.
The ordinary source contract supplies `B>=16`, positive odd `b`, and
nonnegative `K0=DC+B DR`. The actual masks may be arbitrarily large within
their fixed valid ranges; no small-mask special case is needed.
The retained original source definitions were additionally read as text:
`explore_fixed_raw_universal_78.py` materializes `DC` from nonnegative
coefficient shifts and defines `DR=1<<(radix_bits*H)`;
`explore_fixed_raw_universal_76.py` retains this construction and adds only
a nonnegative optional monomial. This supports `K0>=0` directly.

Write the Pell sequences as

`chi_A(r)+psi_A(r)*sqrt(A^2-1)=(A+sqrt(A^2-1))^r`.

To avoid confusing the input witness with the auxiliary square, write
`Qaux=i c^2`, while `rho` always denotes the input projection witness.
For `a=Y(X+1)`, put `A=a+2`, `Delta=A^2-1`, `H=4a+3`, and
`E_A(r)=chi_A(r)-a psi_A(r)`.
The main projection identity is `E_A(p)=X+gamma H`.

## 2. Fixed context for an arbitrary positive input

Fix the actual compiler and any integer `x>0`. Choose `N` a power of five
large enough that `q=B^N>2d x+1`, and set

`t=dN`, `J=(q-1)/(B-1)`, `Q=q^2-1`, `p0=12t+7`, `X=2^p0`.

Then `t` is an odd power of five, `q=2^t`, `p0=3 mod 4`, and
`gcd(p0,2t)=1`. Also `X/q^3=2^(p0-3t)` is a positive integer.
The repunit `J` is a positive integer and gives the literal definition
`q=(B-1)J+1`.

Define

`D0 = 4q^3(X+1)/3`.

This is an integer. In fact

`gcd(X+1,Q)=3`, `v_3(X+1)=1`, `gcd(D0,Q)=1`, `D0=2 mod 3`.

For the first equality, any common divisor `g` of `2^p0+1` and
`2^(2t)-1` is odd. Choose integers `r,s` with `rp0+2st=1`; `r` is odd.
Reducing powers modulo `g` gives `2=(-1)^r=-1`, so `g` divides three;
both numbers are divisible by three. Next `p0=1 mod 6`, so
`2^p0=2 mod 9`, which proves the stated valuation. Removing this sole
factor of three from `X+1` proves `gcd(D0,Q)=1`.
Finally `q^3=-1 mod 3` and `(X+1)/3=1 mod 3`, giving `D0=2 mod 3`.

Choose `s0` modulo `Q` such that both `s0` and `1+D0 s0` are units
modulo `Q`. At every odd prime divisor of `Q`, exactly the two distinct
residues `0` and `-D0^{-1}` are forbidden, so CRT supplies such an `s0`.
At the prime three the sole allowed residue is `s0=2 mod 3`.

The residue `1+D0 s0` is a unit modulo `D0 Q`: it is one modulo `D0`
and is a unit modulo `Q`. Dirichlet's theorem therefore supplies
arbitrarily large primes

`ell = 1+D0 s0 mod D0 Q`.

Choose one large enough and set

`s=(ell-1)/D0`, `Y=s q^3`, `E=XY`.

Then `s` is positive, `s=s0 mod Q`, and `s=2 mod 3`.
The fixed Pell parameters now obey

`H=4Y(X+1)+3=3ell`, `ell=2 mod 3`.

In particular,

`gcd(QH,2E)=1`, `gcd(QH,ord_H(2))=1`.

For the first statement, `Q` is coprime to powers of two and to `s`;
three does not divide `s`; and `ell` cannot divide `s=(ell-1)/D0` or a
power of two. For the second, `ord_(3ell)(2)` divides `ell-1` because
the order modulo three is two and `ell-1` is even. But
`ell-1=D0 s` is coprime to `Q`, is not divisible by three, and is coprime
to `ell`.

Thus, for

`T=lcm(4,2E,ord_H(2))`,

one has the exact coprimality `gcd(QH,T)=1`.

## 3. Outer and input equations become a compatible progression

The following quantities are fixed before selecting the large main index:

`u=2d x+b`, `C=1`, `alpha=q-1-2d x`, `z=1`,
`F=K0+X-q+1`,
`M=(MC+q(MF_native+B-1))J`.

They have the required signs: `u` is odd and at least three; `alpha>0`;
and `F>0` since `X>=q^3>q` and `K0>=0`.
There is no need for `u<q` in this construction.

Set the fixed input Pell coefficient and its discriminant slack to

`kappa=psi_A(u)`, `delta=(kappa-u)/Delta`.

Reduction of the Pell recurrence modulo `Delta` gives
`psi_A(u)=u mod Delta` for odd `u`. Also `psi_A(u)>u` for `A>=2` and
`u>=3`, so `delta` is a strictly positive integer.

Impose the two progressions

`p=p0 mod T`,
`p=-M-Q(q^2-qF+E_A(u)-C) mod QH`.

They are compatible by `gcd(QH,T)=1`; they form one infinite arithmetic
progression of modulus `TQH`. Along it define

`Z=q^2-qF+(p+M)/Q`,
`rho=(Z+E_A(u)-C)/H`.

The second progression proves **both** integrality statements, first
modulo `Q`, then after dividing by `Q`. Both `Z` and `rho` grow affinely
with positive slopes as `p` grows, so both are eventually strictly positive.

These choices make the transport equation exact:

`(K0+X)C=F+z(q-1)`.

They also make the literal shifted packing expression equal to `-p`:

`(q^2-Z-qF)(q^2-1)+M=-p`.

Finally `W=C-Z=E_A(u)-rho H`, so the input root computed by the source is

`mu=W+a kappa+rho H=chi_A(u)>0`.

Consequently its complete input norm is exact. The construction actually
uses the **positive** input-root branch. The formerly omitted positive
`W` is not a supplied child coordinate and is eventually negative.

## 4. The main and first Pell indices remain genuinely free

Put `P=2XY^2+1`,
`lambda=A+sqrt(A^2-1)`, and `nu=P+sqrt(P^2-1)`.
The squarefree part of `Delta=A^2-1` is odd, since `A` is even. In contrast,

`v_2(P^2-1)=2+p0+2v_2(Y)`

is odd: `XY^2+1` is odd and `p0` is odd. The two real quadratic fields
are therefore distinct. If `log(lambda)/log(nu)` were rational, positive
powers of the two units would agree and lie in their intersection `Q`.
Their norm-one property would make that positive rational number one,
contradicting strict growth. Hence the logarithm ratio is irrational.

Let `L=E/2` and fix any representative

`n0=(1-p0)/2 mod L`.

Along the progression for `p` from Section 3 and the independent progression
`n=n0 mod L`, irrational rotation density yields infinitely many pairs
`p,n` tending to infinity for which

`Y < psi_A(p)/(2psi_P(n)) < Y+1`.

To be explicit, the logarithm of this ratio is

`p log(lambda)-n log(nu)+log(sqrt(P^2-1)/(2sqrt(Delta)))+o(1)`.

Choose an open interval strictly inside `(log Y,log(Y+1))`. The rotation
step is `(TQH)log(lambda)/(L log(nu))`, still irrational. Infinitely many
large positive progression indices enter that interval modulo
`L log(nu)`; choosing the corresponding integer translate determines `n`.
Both indices grow, and the vanishing error can be absorbed inside the
strict interval. Thus the extra outer/input conditions have not produced
a sparse or nonlinear restriction to which density was inapplicable.

## 5. All main/first witnesses and the restored index

For each sufficiently large pair from Section 4, define

`c=psi_A(p)`, `D=chi_A(p)`,
`k=2psi_P(n)`, `tau=chi_P(n)`,
`eta=c-kY`, `zeta=k-eta`,
`gamma=(D-ac-X)/H`, `h=(k+p-1)/E`.

The strict ratio interval gives positive integers `eta,zeta` and exactly
`k=eta+zeta`, `c=kY+eta`. The first norm is

`tau^2-1=XY^2(XY^2+1)k^2`.

The complete74 paid factored expression equals its right-hand side:
`(EkY)(EkY+k)=k^2(XY^2)(XY^2+1)`.
The main norm is `D^2-Delta c^2=1`.

Modulo `E`, one has `P=1` and `psi_P(n)=n`, so the two progressions give
`k=2n=1-p mod E`. Therefore `h` is a strictly positive integer and

`k-hE-1=-p`.

The recurrence for `E_A(r)` gives `E_A(r)=2^r mod H`. Since
`p=p0 mod ord_H(2)`, one has `E_A(p)=X mod H`, proving integrality of
`gamma`. Furthermore

`E_A(p)=2c-psi_A(p-1)>c`,

so `gamma` is eventually positive and grows exponentially in `p`.
The input `rho` from Section 3 grows only affinely. Hence

`sigma=gamma-rho`

is eventually a strictly positive integer, and the child definition
`gamma=rho+sigma` holds exactly.

## 6. Full strong auxiliary block, with positive witnesses

Because `p=3 mod 4`, `c` is odd. Put

`m=cp`, `f=chi_A(m)`, `Qaux=Delta psi_A(m)`, `i=Qaux/c^2`.

Expanding `(D+c sqrt(Delta))^c` shows `c^2` divides `psi_A(cp)`:
the linear term contains `c^2`, and every remaining odd term contains
at least `c^3`. Thus `i` is a positive integer and `Qaux=i c^2`.
The strong auxiliary norm holds exactly:

`Qaux^2=Delta(f^2-1)`.

Let `saux=p+2m`, so `saux=1 mod 4`, and define

`U=chi_Qaux(saux)/Qaux`, `y=psi_Qaux(saux)`.

For odd `saux=2baux+1`, the elementary odd-quotient polynomial identity is

`chi_Qaux(saux)/Qaux=Q_baux(Qaux^2)`,
`Q_baux(0)=(-1)^baux saux`,
`Q_baux(1-A^2)=(-1)^baux psi_A(saux)`.

Here `baux` is even. These identities prove that `U` is an integer and

`U=p mod c`, `U=-c mod f`.

For the second congruence use `Qaux^2=1-A^2 mod f` and
`psi_A(p+2m)=-psi_A(p)=-c mod f`; the latter follows immediately from
`chi_A(2m)=2f^2-1` and `psi_A(2m)=2f psi_A(m)`.

Set `j=(U-p)/c` and `o=(U+c)/f`. Both are integers. They are strictly
positive: `saux>=3`, `Qaux>=c^2`, and elementary Pell growth give
`U>=4Qaux^2-3>c>p`; the positive integer quotient defining `o` is positive.
Thus, with `R=-p`,

`U=jc-R=of-c`.

The Pell equation at parameter `Qaux` gives exactly

`Qaux^2(U^2-y^2)=1-y^2`.

This verifies both uses of the actual strong square; no weakened auxiliary
norm or sign assumption on the restored index was substituted.

## 7. Final domain and equation check

The supplied child coordinates are

`J,F,alpha,z,f,h,i,j,o,s,w,tau,eta,zeta,y,Z,delta,rho,sigma`.

Here `w=X/q^3`. Every one is a strictly positive integer for all
sufficiently large density hits. The input `x` was arbitrary and positive.
The definitions recover the desired `q,X,Y,E,k,a,c,H,Delta,A,gamma,D`,
`u,kappa,C,W,mu` exactly. Sections 3, 5, and 6 verify every one of the
eight retained child residuals. Therefore their sum of squares is zero.
The restored index is nevertheless negative at every such tuple.

The common-scale and retained positivity hypotheses were used directly.
At no point was the positive-index kernel theorem invoked to obtain
`p=R`, `X=2^R`, a positive packing bound, or `W>0`.
The former obstruction of coupling a free-density construction to a
sparse negative-root index is avoided by fixing the input Pell index
`v=u` and letting its positive projection witness `rho` grow linearly.

## 8. Evidence limit

This is an independent mathematical audit of the quantified construction,
including the actual source-contract fact that `d` is a power of five.
Only cached source text and receipts were read. No upstream Python module,
arithmetic schedule, compiler, or historical checker was executed; no
upstream repository file was edited or published.
Small newly authored arithmetic checks used during exploration concern a
special fixed context only and are not evidence for the unbounded
existence claim. The proof above, rather than those checks, establishes
the claimed full signed-child family.
All 16 files in the final packet's `source_manifest.json` were independently
rehashed from their cached bytes: every SHA256 and Git blob SHA1 matched.
The author's separate outer-only numerical fixtures and prime certificate
are supplementary and were not needed or represented here as materialized
full child zeros.
