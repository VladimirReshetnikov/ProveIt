# Independent audit of the generalized compiler-numeral supplement

## Verdict and version binding

**PASS.** Independently reviewed supplement:
`../GENERALIZED-COMPILER-SUPPLEMENT.md`, SHA256
`69f64c16aed4f9b962ec82553186ffc25cae79cb6808bfe0a3e6136797c0ae60`.

The unchanged main proof is `../FULL-SIGNED-COUNTEREXAMPLE.md`, SHA256
`b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd`.
The existing main independent audit remains applicable to its exact stated
actual-compiler scope. This separate review checks the supplement's broader
algebraic scope, including every place where the earlier audit used odd `t`
or powers of five.

For the same eight-equation signed19 interface, the supplement correctly
proves infinitely many positive supplied-coordinate zeros with restored
`R<0` at every positive ordinary input, for every fixed integer `d>=1`,
`B=2^d`, positive odd integer `b`, nonnegative integer `K0`, and arbitrary
fixed integer mask ports `MC,MFsrc`.

This is an algebraic statement about that interface. It does not assert that
the broader numeral choices are compiler exports, invoke a compiler theorem
for them, transfer to raw29/positive21, or change a universal bound.

## 1. Initial exponent choice

For any fixed positive input, a positive integer `N` can be chosen with
`q=B^N>2d x+1`. Thus `t=dN>=1`, `q=2^t`, and the repunit
`J=(q-1)/(B-1)` is a positive integer. Neither `N` nor `t` needs a
powers-of-five condition.

Writing `t=2^a 3^b0 t0` with `gcd(t0,6)=1` gives `gcd(t0,12)=1`.
Therefore CRT supplies

`p0=7 mod 12`, `p0=1 mod t0`.

The second congruence is indeed vacuous when `t0=1`. Adding multiples of
`12t0` preserves both congruences and makes `p0>3t`. Prime by prime these
conditions give `gcd(p0,2t)=1`. They also give precisely the required
`p0=3 mod 4`, `p0=1 mod 6`, and oddness.

Consequently `X=2^p0` has the positive integer scale witness
`w=2^(p0-3t)`. No later step requires the exact earlier formula
`p0=12t+7`.

## 2. Scale selection, including even t

The supplement's Bezout proof establishes

`gcd(2^p0+1,2^(2t)-1)=3`.

Negative Bezout exponents are legitimate since the common divisor is odd.
Both numbers are divisible by three because `p0` is odd and `2t` is even.
Also `p0=1 mod 6` implies `X+1=3 mod 9`. Removing this sole factor of
three proves that

`D0=4q^3(X+1)/3` is integral and `gcd(D0,Q)=1`,

where `Q=q^2-1` is odd.

The changed parity case is handled correctly:

`D0=(-1)^t mod 3`.

This can be either one or two. At each prime dividing `Q`, the residues
zero and `-D0^(-1)` are distinct forbidden values for `s0`; at least one
permitted value remains, including at the prime three. CRT therefore
supplies `gcd(s0,Q)=gcd(1+D0 s0,Q)=1` for even and odd `t` alike.

More explicitly at three, if `D0=1`, the allowed `s0` is one; if `D0=2`,
the allowed `s0` is two. Thus in both cases `D0 s0=1 mod 3`.
The progression `ell=1+D0 s0 mod D0Q` is primitive, so Dirichlet's
theorem supplies a sufficiently large prime `ell>3`. With
`s=(ell-1)/D0`, one obtains `s>0`, `s=s0 mod Q`, and

`ell=2 mod 3`, `H=3ell`, `Y=sq^3`, `E=XY`.

Every decisive coprimality follows without assuming that `t` is odd:

- `Q` is coprime to `s` and to the powers of two `X,q`
- three does not divide `s`, and `ell` does not divide `s` because
  `ell=D0s+1`
- therefore `gcd(QH,2E)=1`
- `ord_H(2)` divides `ell-1` (hence also `2(ell-1)`), since `ell-1` is
  even and `H=3ell`
- `Q` is coprime to `ell-1=D0s`; neither three nor `ell` divides
  `ell-1`; hence `gcd(QH,ord_H(2))=1`

It follows that `gcd(QH,T)=1` for the stated
`T=lcm(4,2E,ord_H(2))`.

## 3. Fixed signs, input slack, and arbitrary masks

The strict inequality on `q` gives `alpha=q-1-2d x>0`.
Since `X>q^3>q` and `K0>=0`, `F=K0+X-q+1>0`.
The fixed input index `u=2d x+b` is odd and at least three even when
`d=1`, `x=1`, `b=1`. No upper bound on `b`, `u`, or `u/q` is needed.

For `A=Y(X+1)+2>=2`, the congruence
`psi_A(u)=u A^(u-1)=u mod Delta` holds for odd `u`, where
`Delta=A^2-1`. Also `psi_A(u)>u` for all `u>=3`.
Thus `delta=(psi_A(u)-u)/Delta` is a positive integer under the broader
hypotheses, including their smallest allowed input index.

The arbitrary signed integers `MC,MFsrc` occur only through the fixed
integer `M=(MC+q MFsrc)J`. Neither their signs nor native-mask ranges are
used elsewhere in the construction. Coprimality of the progression moduli
allows any resulting packing residue. The formulas

`Z=q^2-qF+(p+M)/Q`,
`rho=(Z+E_A(u)-1)/H`

remain integral by the same CRT argument. They have positive affine slopes
in `p`; arbitrary fixed mask signs alter only constant terms. Thus both
eventually become positive, and `W=1-Z` eventually becomes negative.
The computed input root remains exactly `chi_A(u)>0`.

## 4. Density, all Pell equations, and witness positivity

The two progressions for `p` still form one ordinary arithmetic progression
of step `TQH`, and `n=(1-p0)/2 mod E/2` is well-defined since `E` is even.
They imply `2n=1-p mod E` exactly as in the main proof.

For both parities of `t`, `q` and `Y` are even, so `A` is even and
`Delta` is odd. On the other hand,

`v_2(P^2-1)=2+p0+2v_2(Y)`

is odd because `p0` is odd. Hence the two real quadratic fields are still
distinct, their unit logarithm ratio is irrational, and the positive-length
interval density argument applies to the free progressions without change.
It supplies infinitely many unbounded positive pairs with
`Y<psi_A(p)/(2psi_P(n))<Y+1`.

This gives positive `eta,zeta`. The congruence gives the positive integer
`h=(k+p-1)/E` and restored index `R=-p`. The recurrence modulo `H` gives
integer `gamma`; its exponential growth dominates the affine `rho`, so
`sigma=gamma-rho>0` eventually. None of these estimates uses a lower bound
`q>=16`; the proof is direct and never invokes the positive-index kernel
theorem with its external bounds.

Finally, `p=3 mod 4` still follows from `p=p0 mod T`. Therefore `c` and
`m=cp` are odd, and `saux=p+2m=1 mod 4`. All integrality and sign steps
in the strong auxiliary construction follow unchanged, including
`c^2|psi_A(cp)`, `U=p mod c`, `U=-c mod f`, and positive integer `i,j,o`.

Thus every supplied coordinate in the exact nineteen-coordinate list is
positive eventually, and all eight retained residuals vanish. No implicit
positivity was imposed on signed intermediate registers or arbitrary mask
ports.

## 5. Source-interface and evidence limits

The native compiler relation `MFsrc=MF_native+B-1` remains the correct
identification when specializing to actual exports. The generalized theorem
instead treats the already paid `MFsrc` port as an arbitrary fixed integer;
it does not reinterpret arbitrary values as valid native masks.
Likewise `B>=16`, `b<B`, mask ranges, typed-word decoding, and powers-of-five
compiler conventions are not assumptions of the broader algebraic proof.

The prior literal residual mapping and full positive-coordinate audit apply
to the unchanged equation interface. The supplement changes the initial
parameter construction only. Its author-reported 512-case check concerns
the exponent/gcd selection lemma, not a finite full-zero certificate;
the independent verdict here rests on the argument above rather than those
finite cases. No upstream code or arithmetic schedule was executed, and
the approved main proof and source files were not edited.
