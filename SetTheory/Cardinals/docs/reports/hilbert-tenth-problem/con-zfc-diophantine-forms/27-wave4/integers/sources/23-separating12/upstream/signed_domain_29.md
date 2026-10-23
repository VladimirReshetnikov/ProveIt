# Independent audit of signed-domain reduction

Source: ProveIt `3b201cdea32d2c816f5f3d20734051f25fd3ef14`, package `06-blank67`.

This note concerns the normalized P67/P68 polynomials and six-equation systems, and the ordinary-strong system and product P69. It is an ordinary proof, not a new kernel-checked result.

## Claim

In the normalized construction require positivity only for

`J,F,alpha,z,s,eta,zeta`.

Let `f,h,r,T,tau,y,gamma,u` range freely over the integers and replace the old multiplier `i` everywhere by `2r+1` and the old power scale `w` everywhere by `u^2`. The resulting equation has a solution if and only if the original positive-domain equation has a solution. Consequently replacing each of the seven positive coordinates by a three-integer positive surjection yields an equation in **29 unrestricted integers**. The two substitutions add three arithmetic operations before the positivity surjections. The affine multiplier does not raise degree; the square scale can raise total degree and must be audited in the emitted circuit.

The proof retains all original coefficient definitions and all original native-compiler theorems. It only changes the admissible witness domain and choice of strong auxiliary witness.

## Soundness of the wider domain

Write `i=2r+1`, so `i` is a nonzero integer, and `w=u^2>=0`. Keep all other polynomial abbreviations from package 06. Initially `X>=0`, whereas `Y,k,c,a` are positive (even when X=0, `a=Y`). Thus `A=a+2`, `Delta=A^2-1`, and `H=4a+3` are positive. The normalized product-factor proof gives

`N0=N1=NA=Ns=1`, `Nk=epsilon`, `Nt=nu`, `epsilon,nu in {-1,1}`, and `epsilon*nu=1`.

The proofs excluding negative norm units use squares and are unaffected by signs of the free coordinates. For the first norm, the exceptional case X=0 simply gives `N0=tau^2`, which cannot be -1; for X>0 the original consecutive-product lemma applies. In particular the normalized strong equation gives

`f^2-Delta*i^2*c^4=1`.

### The zero square scale is impossible

This argument works for the normalized product, ordinary product, and both systems. The main norm is 1; its negative unit is excluded by `Delta=0 or 3 (mod 4)`. If u=0, then `X=0`, `a=Y`, and `D=ac+gamma H`. Since `Delta=a^2+H`, reduction of `D^2-Delta c^2=1` modulo H gives `0=1 (mod H)`, impossible because `H=4Y+3>1`. Therefore u is nonzero and **w=u^2>0**. No rank lemma or growth estimate is needed for this boundary case.

Now X>=q and transport with `z>0` still implies `C>=0`, hence the original bounds

`3q+1<R<q^4-2`, `E>=q^4>R+2`, and `a>R+2`.

### Signed h

Because `k=R+epsilon+hE>0`, the inequality `E>R+2` forces `h>=0`. Thus `k>=R-1`; since `c>kY` and `Y>=q^3>=16^3`, one has `c>2R`. All other early Pell bounds follow as before: the first norm gives `k=2 psi_P0(n)`, the main norm gives `|D|=chi_A(p)`, `c=psi_A(p)`, and `P0>A,c>k` imply `p>n`. The index congruence gives `n>=(R-1)/2>=24`; hence `c>2p`.

### Normalized rank without the relaxed lemma

Let `f0=|f|`. The strong equation gives

`f0=chi_A(m)`, `psi_A(m)=|i|c^2`.

Strong divisibility implies `p|m`; write `m=pb`. In the binomial expansion of `(D0+c sqrt(Delta))^b`, where `D0=chi_A(p)`, divide the square-root coefficient by `c` and reduce modulo `c`:

`psi_A(pb)/c = b D0^(b-1) (mod c)`.

The left side is divisible by `c`, while `gcd(D0,c)=1`; hence `c|b`. Thus `pc|m`, and in particular `c|m` and `m>2p`.

### Signed auxiliary quotient

Let `rho=Delta |i|c^2>1`. Then `rho^2=Delta(f0^2-1)`, and the auxiliary equation is

`rho^2 V^2-(rho^2-1)y^2=1`.

It forces `V!=0` and `y!=0`. Pell classification of the positive absolute values gives

`rho |V|=chi_rho(ell)`, `|y|=psi_rho(ell)`, `ell>=1`.

Since `rho` divides `chi_rho(ell)`, `ell=2u+1` is odd. Put `sigma=sign(V)`. For the odd Chebyshev quotient `Q_u`, one has

`V=sigma Q_u(rho^2)`,

`Q_u(1-A^2)=(-1)^u psi_A(ell)`, and `Q_u(0)=(-1)^u ell`.

The polynomial definition of V supplies the congruences

`V=-c (mod f0)` and `V=-R (mod c)`.

Together with `rho^2=1-A^2 (mod f0)` and `rho^2=0 (mod c)`, they yield

`sigma(-1)^u psi_A(ell)=-c (mod f0)`,

`sigma(-1)^u ell=-R (mod c)`.

Squaring the first and using Pell duplication gives

`chi_A(2ell)=chi_A(2p) (mod chi_A(m))`.

The plus step-down lemma, applicable because `0<2p<m`, gives `ell=+p or -p (mod m)` (indeed modulo `2m`). As `c|m`, the second congruence yields `R=+p or -p (mod c)`. The bounds `0<R,p<c/2` force **p=R**. No sign of f,T,V,y is used, and no restoration of positive o,j is needed.

### No wrap and the two remaining unit signs

The original proof now applies verbatim: `2n=R+epsilon+vE` with `v>=0`, `n<p=R`, and `E>R+2` force `v=0`. If `epsilon=-1`, Pell duplication contradicts `kY<c<k(Y+1)`. Thus `epsilon=nu=1`, `R=2n-1` is odd, and transport gives `C>0`.

### Signed gamma

Set `r0=(R-1)/2>=2`. The lower-ratio estimate uses `c` and `|D|`, so it is unchanged:

`a>X^(r0+1)/3`.

Since `X>=16`, `X^r0>6*4^r0`; therefore

`0<X*2^R<a<H-1`.

Suppose `D=-chi_A(R)`. The recurrence gives `chi_A(R)-a psi_A(R)=2^R (mod H)`. Also

`(chi_A(R)-a psi_A(R))(chi_A(R)+a psi_A(R)) = 1+H psi_A(R)^2`.

The polynomial definition `D-ac=X+gamma H` then implies `X*2^R=-1 (mod H)`, contradicting the preceding strict interval. Hence `D=chi_A(R)`. The usual positive residue argument gives `X=2^R`; all remaining packing and native-window soundness is unchanged.

## Completeness with odd multiplier

Take the original canonical positive tableau and half-binomial witnesses at its final actual rank R. They satisfy `R=3 (mod 4)` and `c=psi_A(R)` odd. Instead of the old strong index `2cR`, choose

`m=cR`, `f=chi_A(m)`, `i=psi_A(m)/c^2`.

The expansion of `(chi_A(R)+c sqrt(Delta))^c` shows `c^2|psi_A(cR)`: its first square-root term contains `c*c`, and every later odd term contains at least `c^3`. Since `c` and `m=cR` are odd, `psi_A(m)` is odd; hence the integer quotient i is positive and odd. Thus `i=2r+1` for an integer r.

Set `rho=Delta psi_A(m)` and use `V=chi_rho(R)/rho`, `y=psi_rho(R)`. Odd R makes V integral. The same quotient identities, using `R=3 (mod 4)`, give `V=-c (mod f)` and `V=-R (mod c)`. Therefore

`o=(V+c)/f`, `j=(V+R)/c`, `T=(o+Rf)/c`

are positive integers; integrality of T follows by reducing `of+R=c(j+1)` modulo c and using `f^2=1 (mod c)`. This reproduces exactly the polynomial V. All other witnesses are the original positive witnesses. Thus completeness is preserved.

### Completeness with square power scale

Package 06's `proofs/blank_helical_proof.md`, sections "Completeness and all helical seams" and "The blank-input specialization of five-adic index control", explicitly permits the spatial width h0 and temporal height Htime to be sufficiently large powers of five. Thus `N=h0*Htime` is a power of five. The fixed exponent is `d=5^67`; consequently `t=dN` is odd. The final tuned rank has `R=3 (mod 4)` and in particular is odd. Since `q=2^t`, the canonical power scale

`w=2^R/q=2^(R-t)`

is an integer square: `R-t` is a positive even integer. Choose `u=2^((R-t)/2)`. This preserves the entire canonical witness tuple and verifies the extra restriction `w=u^2`. No new tuning, mask, coefficient, or compiler change is involved.

## Ordinary-strong systems and product

For a system using `rho=ic^2` and `rho^2=Delta(f^2-1)`, the signed proof works with the existing relaxed-rank lemma, whose size condition follows from `p>n>=24`. It supplies `|f|=chi_A(m)`, `p|m`, `c|m`, `m>2p`. The congruence `f^2=1 (mod c)` must be deduced *after* rank, from `c|psi_A(m)`; it does not follow by simply dividing the strong equation by Delta.

For completeness take `m=cR` and `i=Delta psi_A(m)/c^2`. This integer is odd because `a` is even at the canonical power-of-two witnesses, so Delta is odd. The same square-scale completeness and zero-scale exclusion apply. Thus the same **29-integer conversion** applies to the ordinary system.

For the ordinary product define `A0=Delta(f^2-1)`, `B0=(ic^2)^2`, `Ns0=1+B0-A0`, and `Na=A0(V^2-y^2)+y^2`. The finalizer is

`P69=N0*N1*Na*Nk*Nt*Ns0-1`.

Every factor is an integer unit. `Ns0=-1` would require `A0-B0=2`. However, `Delta=0 or 3 (mod 4)` and f squared is 0 or 1 modulo 4, so `A0` is 0 or 1 modulo 4; `B0` is a square and likewise 0 or 1. Their difference cannot be 2 modulo 4. Hence `Ns0=1`, `A0=B0` is a square, and the usual mod-four sign exclusion for Na applies. The first and main norms are positive units as before. The zero-scale proof uses only the main norm, so it precedes the relaxed-rank argument and causes no additional growth hypothesis. This proves the 29-integer conversion for ordinary P69 as well.

## Explicit positivity surjection

One convenient division-free choice is

`Pos(x,y,z)=x^2+x+y^2+z^2+1`.

It is positive for all integers and represents every positive integer. For n>=1, Legendre's three-square theorem represents `4n-3` as three squares; modulo four exactly one square is odd and the other two are even. Writing the odd square as `(2x+1)^2` and the even squares as `(2y)^2,(2z)^2` gives `n=x^2+x+y^2+z^2+1`. This is the same standard three-integer convention underlying the source package's 41-integer variant. Applying it to exactly seven coordinates, and leaving exactly eight free, gives 7*3+8=29.

## Metatheory and evidence boundary

The K215 endpoint states an unconditional biconditional with syntactic finite ZFC refutability (`BProv`). Its Lean/Rocq audit records are external kernel evidence, not an internally encoded ZFC derivation. The claimed ZFC-provable Diophantine equivalence is obtained by formalizing the ordinary arithmetic, finite-window, and model-theoretic calibration arguments in ZFC. This note provides no new formal-assistant build and no proof of Con(ZFC).

## Source dependency catalogue

All paths are relative to ProveIt and verified present at commit `3b201cdea32d2c816f5f3d20734051f25fd3ef14`. Package 06's original arithmetic/compiler pin is `cdd582bec13f908df3711fa9e05d1ddac368a5db`.

| Dependency | Exact source | Role |
| --- | --- | --- |
| Baseline polynomials and four constants | `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67/report.tex` | P67/P68, transport bounds, constants, full compiler reduction |
| Baseline Pell audit | Same package, `proofs/pell_lemma_audit.md` | Direct normalized rank, quotient identities, full local proof order |
| Blank helical construction | Same package, `proofs/blank_helical_proof.md` | Raw K215 local language; canonical width/height powers of five; final-rank tuning |
| Machine binding and metatheory | Same package, `proofs/k215_audit_notes.md` | Exact proof predicate and transition table; formalization scope |
| Asymmetric scale | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` | Lower ratio used for power recovery and new signed-gamma proof |
| Half-binomial kernel | Same research directory, `pell_kernel_half_binomial42.md` | Exact floor, valuation, positive converse |
| Normalized strong rank | Same research directory, `pell_fixed_affine_exponent52.md` | Direct rank divisibility argument |
| Half-binomial compiler | Same research directory, `complete75_half_binomial_compiler.md` | Mask and inverse-population modifications |
| Native compiler | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` | Carry-free convolution, clean-band and anchor synchronization |
| Ordinary strong rank | Same 1980 directory, `PELL_RELAXED_AUXILIARY_PROOF.md` | Relaxed norm rank under c>A Delta squared |
| Signed Pell congruences | Same 1980 directory, `PELL_SIGNED_PROOF.md` | Signed index step-down |
| Plus step-down and quotient identities | Same 1980 directory, `EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | Precise modulus4m statement and quotient polynomials |
| Five-adic tuning | Same 1980 directory, `EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` | Boolean subset residue coverage |
| Ordinary machine calibration | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` | Mathematical proof formalizable in ZFC |
| Lean endpoint | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` | Unconditional exact-machine biconditional with syntactic refutability |
| Rocq endpoint | `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v` | Independent endpoint in Rocq |
| Formal build records | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` | Fresh full build scope and later incremental records |

## Final manuscript caveats

1. Do not claim a minimum variable count: the new result is a reduction from the repository's comparable 41-integer polynomial to 29, with a degree/operation tradeoff. Classical nine-variable universal constructions use a different size metric and are not displaced.
2. Do not label these Diophantine results Lean/Rocq formalized. Only the cited machine endpoint has that status. No fresh endpoint build has been executed in this task.
3. State that the four enormous integer coefficients remain exact finite recipes. The new work changes the arithmetic expression and witness domain, not their height or the feasibility of fully materializing them.
4. All signed-domain claims must include odd i and square w. Simply evaluating the original positive formula over unrestricted integers is unsound.
5. The square w restriction is justified by the specific canonical five-power padding, not by claiming w is square on every original solution.
6. The odd i restriction similarly preserves existence through a new canonical auxiliary index m=cR; it need not hold of every earlier witness tuple.
7. For ordinary-strong rank, explicitly retain c>A Delta squared and prove it before using that lemma. Normalized strong rank does not need it.
8. The theorem is an equivalence provable by ordinary mathematics internalizable in ZFC, not a proof of either consistency or inconsistency. Under mere consistency, unprovability of Con(ZFC) is justified by the usual incompleteness hypotheses; two-sided undecidability requires a stronger soundness premise and should not be asserted from consistency alone.

