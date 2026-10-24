# Adversarial peer: signed three-root quadratic projection

**Accepted ordinary proof and literal121-operation equation.** The
fourteen unknowns are unrestricted integers. I found no gap in the
absolute-value main-Pell recovery, the chronology of the borrowed
signed prefix, the whole-product estimate for negative H, or either
unrestricted n map. The equation has exact degree312 by the stated
unbounded leading-form proof. This is existence equivalence with the
frozen145-operation integer endpoint, not equality of the two complete
polynomials or an application of a positive-domain theorem to signed
inputs.

The reviewed equation SHA256 is
`738c7adb164ecc7267bee75868f5ab49a9ce9c951684fd8761e0e0f790477828`;
the ordinary proof SHA256 is
`dfd78f5cf75133bdfd1a260be108fcac4663e71e97ca4a85dbf36f1a0d75da4c`.
The independent peer receipt pins both exact files and embeds fresh
normal/optimized checker and complete builder--check outputs.

## Exceptional branches are removed by the retained guard

The finalizer is still (1+S)(1+N)-1 with S=B^2. At an integer zero,
1+S is a positive integer divisor of1, so S=N=0. This reasoning
requires no sign assumption on the norm N. The unchanged guard gives
v!=0, G>0 and eta*zeta>0. Thus k!=0 and eta,zeta have one strict sign.
For x=|X| and m=|Y|, the literal q,W congruences give x>=64,m>=16.
The signed interval

```
|k|(m-1)<|c|<|k|(m+1)
```

then gives |c|>30. Consequently the retained parent's exceptional
c=0 branch cannot be a zero, delta>0, H!=0 and U!=0. All three
retained radicals are positive.

The weak-scale separation in the145 parent does not assume an integer
main root or cubic Y scale. Its auxiliary real d=sqrt(Dmain) is used
only in inequalities at arbitrary guard-admissible inputs; deleting it
from the norm does not invalidate those inequalities. If cT-R=0,
|c|<y<|c|+1<tau and f>2tau. Otherwise y>2f and f>2tau. These ensure
that no nonempty signed subsum of f,tau,y vanishes. The rational
factor equation therefore makes all three roots rational by the
multiquadratic character argument. The integer-square roots f,tau
are integral; the adjacent-coefficient descent makes y integral,
including negative V. This is before any main-Pell classification.

## Main classification really handles signed A,c,V

Set B0=|a+2|, C0=|c| and I0=|(2r+1)c^2|. The weak bounds give
B0>=3 and0<C0<=I0; the strong equation gives f>2I0. Both f and
I0 are positive integer Pell coordinates at B0. The auxiliary
coefficient is S0=(B0^2-1)I0>=2, with Q=S0^2. Classify
(S0*|V|,y), not the original signed V. Its index nu is odd because
an even abscissa is plus or minus1 modulo S0 and cannot be divisible
by S0.

The exact odd-index polynomial identity reduces at
S0^2=1-B0^2 modulo f. Together with V=-c modulo f, it gives
psi_B0(nu)=plus or minus C0 modulo f, incorporating both signs of
V and c. For f=chi_B0(m0), alpha^(2m0)=-1 modulo f. Folding any
integer index modulo2m0 and reflecting across m0 therefore yields
plus or minus psi_B0(p) for0<=p<=m0. Since

```
0<=psi_B0(p)<=I0,        0<C0,        I0+C0<=2I0<f,
```

the negative residue cannot occur and the positive residue cannot
wrap. Thus C0=psi_B0(p), p>=1. This recovers an integer main root
without assuming a sign of A,c,V, a projection congruence, cubic Y,
or integrality of gamma. The argument is stronger than merely
finding a rational main root.

## Cubic CRT and the borrowed prefix precede gamma

The new factor equation is

```
n+V+K/H+(v-q^2)/(2q^2)=signed integral roots.
```

For all signed q,H here, q is even and2 modulo3; H is odd and3
modulo q. Hence gcd(H,2q^2)=1. Reducing the undivided integer factor
equation gives2q^2|(v-q^2) and H|K. Therefore
v=q^2(2v_old+1), and the old signed cubic Y scale is available before
the signed index/ratio argument. No division by a possibly zero or
nonunit residue is used.

I read the actual borrowed `RESIDUE_AND_DETERMINANT.md` in the
immutable Constructive Reductions ZIP, SHA256
`37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0`.
The copied member is byte-identical. Its Section4 prefix through the
ratio estimate uses a main Pell norm but does not use the later
main-projection equation or gamma integrality. The new folding
classification supplies precisely that norm. Its initial definition
of a projected D does not appear in these intermediate arguments.

The determinant gives common strict signs of F,C,q and alpha, then
the authentic masks give Q0(Q0^2-1)<R<Q0^4-2 for Q0=|q|>=16,
independently of X's sign. At the recovered scale, |E|=xm>3R+1.
The first Pell coefficient is a consecutive product for X>0 and
m0(m0-1) for X<0, with positive parameter P0=|2XY^2+1| in both
cases. Hence |k|=2psi_P0(n0). Since P0>B0 and C0>|k|,
monotonicity gives p>n0.

The signed recurrence congruence either gives
n0>R or n0>=(R+1)/2. Standard growth then supplies C0>2p,2R and
the needed strong height. The direct positive strong Pell pair also
has C0^2|I0, yielding C0|m0 and m0>2p. For clarity this follows
without a gamma assumption: square-divisibility extraction gives
C0|m0; index divisibility gives p|m0, while m0=p is impossible and
m0=2p would imply C0|2chi_B0(p), contradicting C0>2 and coprimality.

The signed auxiliary step-down needs only V=-c mod f,
V=-R mod C0, C0|S0 and the norm. Squaring its first residue removes
the sign of c. The odd auxiliary index is plus or minus p modulo
m0 and plus or minus R modulo C0. Since C0|m0 and0<p,R<C0/2,
p=R. The negative first-index branch is impossible, and the positive
branch yields2n0=R+1. Every use of these conclusions is before gamma.

The normalization I_old=Delta*i*c^2 satisfies the old strong equation;
Delta*i is odd because q is even, hence Y and a are even and Delta
is odd. This is the needed multiplier parity for r_old; no unconditional
oddness of I_old or c is assumed. This parity license also precedes
projection. The absolute
ratio estimate then gives
m>(x-3)^r0/2-1 for R=2r0+1. The packing lower bound actually makes
r0 much larger than24; the stated r0>=24 is safe.

## The whole product handles negative H and both root signs

For all signed a,

```
|H|>=4(x-1)m-3>3xm>x(x-3)^r0.
```

For x>=64 and r0>=10,
`(x-3)^r0 >= (x/2)*61^(r0-1) > x*2^(5r0-6)` and
5r0-6>=4r0+4. Consequently
`|H|>2^(2R+2)*x^2`. All inequalities are strict at the stated
minimal branch; they are not asymptotic estimates.

Let sigma=sign(c). Since R is odd, psi_A(R)=psi_|A|(R)=C0 even
when A<0. The polynomial Pell projections are valid modulo the
possibly negative odd H. With Z0=sigma X they give

```
2^R*K=(Z0-2^R)*(2^R*Z0+1) modulo H.
```

H|K makes H divide the whole right-hand product. Each factor has
absolute value at most2^(R+1)*x, so the product's absolute value
is strictly below |H| and it is zero. The second factor is odd and
therefore cannot be zero for any signed Z0. Thus sigma X=2^R.
There is no cancellation of a composite-modulus factor, no primewise
choice of a quadratic branch, and no assumed positive X. With
d=sigma*chi_A(R), the actual signed integer main root satisfies
H|(d-X-ac). This is where gamma=(d-X-ac)/H is first proved integral.

Some sign branches may consequently be impossible for actual zeros;
the proof does not discard them in advance. In particular the
further X=2 modulo3 condition is compatible with the restored old
endpoint, but is not used as a hidden positivity hypothesis above.

## Both unrestricted witness maps are exact

For a new zero, K/H and gamma are integers. Change only
`n_old=n+K/H+gamma`. The old center equals the new center plus M*d;
after division by U this is precisely d/H. A suitable old
four-root conjugate vanishes, and the guard is unchanged. No sign
of n_old is required.

For an arbitrary old zero, its own extraction/CRT gives integral
roots and gamma. The full identity
`(X+ac)^2-Dmain=K-Hc^2` gives H|K. Choosing
`n_new=f+tau+y-V-K/H-(v-q^2)/M` using the positive root magnitudes
makes the new center equal f+tau+y. It is an unrestricted integer,
and every other variable and the guard stays unchanged. There is no
bounded choice, sign restriction or circular dependency in this map.
The literal graph confirms that n enters only its center addition.

Only after restoring an old zero is the old ordinary native/refutation
calibration composed. No coefficient tuple, positive-domain endpoint
or compiler theorem has been substituted for the signed source.

## Degree and complete literal verification

The new norm arguments have degrees72,48,56,72. The centered
omega=s-w has degree56: Z-UV has degree9 and the exact defect
identity bounds the cancellation. In the ordinary octic form the
inner term of degree128 is uniquely -4*t0*w0; the remaining
utws product has degree248. Thus the norm has exact degree256
and leading form16Q0^4U0^8V0^4L0^4. The guard square S has
degree56 with leading eta0^8. Their product dominates N+S,
proving exact degree312.

I independently recomputed the distinguished coefficient. Selecting
all12 h*a0 factors from k0^12 and all4 q0^4*z factors from R0^4
in that leading form gives

```
[j^140*w^48*v^60*h^12*r^16*c^32*z^4] P
                     =2^280*3^188*beta^140>0.
```

The exponent sum is312. This proves the lower bound on the actual
positive beta slice; sampled degree lines are only supplemental.

My checker imports no candidate producer or verifier. It manually
transcribes the complete formula, with q-1=beta*J and the grouped
subtractions made explicit, and proves universal equality to the
entire148-node DAG using exact shared associative/commutative terms.
It verifies all121 live binary operations:70 multiplications,
26 additions,25 subtractions, all14 inputs and all6 coefficients.
Both a changed K constant and a changed norm polarity are rejected.
All six complete gzip/raw payloads equal the frozen145 parent's,
including both cone scales and the already once-shifted MF.

I inspected and ran the candidate's full independent checker in a
scratch copy so its receipt-writing behavior could not edit the
reviewed folder. Normal and optimized runs pass the complete35-term
cleared norm, all retained/deleted prefix and finalizer maps,
topology/liveness, six actual payloads, signed controls and four
actual-tuple norm/final degree lines. Both full builder--check modes
also pass against the original candidate without writing it. Fresh
outputs are embedded and hashed in my receipt.

My additional controls cover372 weak-bound main recoveries across all
eight A/c/V sign triples,936 signed quadratic products,25 strict
height cases including r0=10, and468 unrestricted center-map
identities. They supplement the unbounded proof rather than establish
it by finite enumeration. The reviewed equation/proof bytes remain
unchanged. No Lean, historical H10 emitter or native coefficient
generator was run, and no consistency proof or new internal-ZFC
derivation is claimed.
