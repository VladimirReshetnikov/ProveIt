# Main-root and modulus guard consequences

This packet concerns the unchanged 1259-coordinate raw source underlying
the frozen 100-guard 967-variable family. All source variables are integers.
The proved change removes the 15 guarded seed abscissae X and six guarded
power moduli T, retaining base0.T and every other guard. There are 79
retained guards. The complete finite dependency and actual-row certificate
is included here. No new quartic coefficients or frontier are claimed by
this research packet. No Lean work is performed.

The claim is **pointwise**: at any zero of the original raw rows with
these79 guards, all21 omitted values are already nonnegative. Thus
63 fresh Legendre witnesses would extend the same body tuple to the
literal frozen967 equation. No private-coordinate orbit map is needed
for that final extension.

The omitted raw X coordinates are

    670,707,775,821,857,887,930,960,990,1020,1050,1080,1110,1140,1170.

The omitted raw T coordinates are730,742,753,764,798,810. Raw694/base0.T
is retained. The other retained private guards are all15 YminusK
values, shared_index.q4minus1/raw657 and Vquotient_minus1/raw1214.
All61 semantic-prefix guards are retained. This list has79 entries.

## 1. Independent semantic-prefix signs and positive exponents

First prove nonnegativity of all643 raw coordinates0..642 using only
the61 guarded values in that prefix. The first two preliminary row
identities give t/raw4>=1 and n/raw5>=2 from retained t0/raw0. Filter
the five-sign certificate to prefix rows and prefix operands; its five
ideal arguments for the factorial outputs, two quotients and endpoint
ut remain unchanged. Every preceding prefix sign inference has only
prefix dependencies. After the last target, add the two actual endpoint
defining rows36/37 to obtain the signs of raw41/42. No private X, T,
U, Z, Y or comparison sign is a premise of this prefix proof.

Strictly positive exponent constructors are checked separately; natural
k alone is insufficient. The15 seed exponents are

    raw4,86,90,110,122,44,46,48,50,52,36,54,56,136,58.

Raw4=t>=1. Raw36=M0+2>=2, and raw86 is its iterated square, hence
positive; this uses only the literal square rows, without evaluating
the array. Raw90=raw86+raw87*raw86 squared is at least raw86. Raw110
is t+raw107*t squared and is at least t. Raw122 is t plus raw104+2.
Raw44,46,48,50,52,54,56,58 are their retained encoded predecessors
plus1. Raw136=x+1>=1 because the prefix proof gives x/raw1>=0.
Consequently **every one of the15 literal seed exponents is at least1**.
No k=0 case occurs in this source. The certificate will bind these
constructors and every exact YminusK row.

Write each seed ordinate as Y=k+s from its actual index_at_most_Y row.
Its s=YminusK guard is retained, so Y>=k>=1 independently of X signs.

## 2. Initial carrier bound, independent of removed guards

Let n0=raw5=t+1 and T0=raw694. The exact original-row combination

    r644+r643+r642-r640-n0*r639+r641
      =2*A*n0-T0-n0 squared-1

and T0>=0 give A>=2: otherwise its left equality would imply
`2*n0 >= T0+n0 squared+1 >2*n0`. The discriminant is D=A squared-1.
This uses only retained t0 and T0 guards, not any omitted X or T.

Let W=raw643 and Z=raw646=1+raw645. The full actual frame row gives

    W=2+sum of the distinct raw argument coordinates
            in all21 triples(base n, exponent k, output m).

All these arguments lie in0..642 and were proved nonnegative above.
Hence W>=2 and every actual n,k,m is strictly smaller than W. The
bootstrap norm is exactly

    A squared-1-W cubed*(W+2)*Z squared=0.

Z cannot be zero because A>=2. Thus Z squared>=1. The identity

    A squared-W to the fourth
      =1+2*W cubed+W cubed*(W+2)*(Z squared-1)

shows A>W squared, without a Pell-index theorem. In particular A>W.
This weaker bound will prove the missing moduli positive for every
base already known positive.

We will also need the stronger bootstrap bound A>W to the W. Here is
an unbounded justification. Put a=W+1 and d=a squared-1. The pair
`(A,W*abs(Z))` is a positive Pell solution at base a. Every such pair
is `(chi_l(a),psi_l(a))` for l>=1. This classification follows by
descent: for x,y>0 with x squared-d*y squared=1, put

    x'=a*x-d*y,  y'=a*y-x.

One has y'>=0 since x<=a*y; x'>0 since
`(a*x) squared-(d*y) squared=d*y squared+a squared>0`; and x'<x
since x<(a+1)*y. The norm is preserved and the inverse is the usual
positive Pell step. Descent on positive integer x reaches(1,0), giving
the asserted finite index l. This argument has no sign assumption on
the original Z.

Modulo W, the Pell recurrence at a=W+1 gives chi_l=1 and psi_l=l.
Since W divides the ordinate W*abs(Z), W divides l, hence l>=W.
The recurrence also gives chi_l>=a to the l. Therefore

    A>= (W+1) to the l >= (W+1) to the W > W to the W.

No downstream power meaning or omitted modulus sign is used here.

## 3. Positive constructor bases and five missing moduli

Every actual distinct base except raw87/f0 is positive before power
interpretation. The literal constructors give

    raw5=t+1>=2,
    raw92=1+raw87*raw86 squared>=1,
    raw103=1+raw5*raw87>=1,
    raw112=1+raw107*t squared>=1,
    raw531=raw530+1>=1,
    raw530=M*(1+raw93+raw113)>=1,
    M=raw129=1+raw87*(raw59+1)>=1.

All their operands are nonnegative by section1; in particular raw87
need only be nonnegative, not strictly positive. The actual modulus
rows say T=2*A*n-n squared-1. Whenever n>=1, A>W>n gives
`A-n-1>=0` and

    T-A=(2*n-1)*(A-n-1)+(n-1)*(n+2)>=0.

Thus T>=A>0. This derives the five omitted moduli at raw730,742,764,
798,810. The base-f0 modulus/raw753 is deliberately postponed. No
argument yet interprets an actual power call whose base is raw87.

## 4. Signed-index recovery uses abs(X), not a source sign premise

The actual common product row gives

    V=(product over all15 seeds of Y squared)*(raw1214+1)>0.

Every Y>=1 and raw1214>=0 were established independently of X and T.
Thus each Y squared divides V. The common unit norm gives
`abs(U)>=A>=2`. The actual comparison base is
`B=1+4*V*(raw657+1)>=5`, with B=A modulo abs(U) and B=1 modulo4Y.

For each seed, put x=abs(X). Its main norm gives x>=A>=2. Set
`S'=S` if X>=0 and `S'=-S` if X<0. The actual congruence S=X modulo U
gives S'=x modulo abs(U); the comparison norm is unchanged, as is the
actual R=k modulo4Y congruence. Apply the pinned, previously reviewed
**signed comparison-index theorem** with natural

    A,B,x,Y,abs(U),k

and arbitrary integer V,S',R. All its hypotheses are now present:
three norms, Y squared dividing V, positive main/root/base values,
the four congruences and1<=k<=Y. It gives

    abs(X)=chi_k(A),  Y=psi_k(A).

This is a use of the theorem with different numerical parameters, not
an assertion that taking absolute values of S/R preserves an unsigned
criterion. R remains signed. There is no positivity premise on S' or
on a progression quotient. No actual source value has been modified.

This index step is independent of all power moduli and of f0>0. The
chosen supporting call for each seed below has a positive constructor
base other than f0. Each of the15 seeds has such an actual call.

## 5. A negative main root contradicts the small output bound

Fix a seed's selected literal power call. Its exponent is the same
k>=1, its n is one of the positive bases above, and its output m is
nonnegative by section1. Its T>=A was proved in section3. The exact
source power-congruence row is

    X-(A-n)*Y-m=T*h

with unrestricted integer h. Put a=A-n and

    p=chi_k(A)-a*psi_k(A),
    q=chi_k(A)+a*psi_k(A).

The Pell recurrence gives the exact identity

    p_(j+1)=n*p_j+T*psi_j(A),  p_0=1,

so p=n to the k modulo T by induction. The norm also gives
`p*q=1+T*psi_k(A) squared`. These statements require no coprimality
or modular inverse division.

If X<0, section4 gives X=-chi_k(A), so the actual source row says
`m+q=-T*h`. Consequently T divides **m*(n to the k)+1**. More explicitly, choose
integer c with p-n to the k=T*c. Then

    m*(n to the k)+1
      = -T*(m*c+h*p+psi_k(A) squared).

This follows from the identity

    m*r+1 = -m*(p-r)+p*(m+q)-(p*q-1),  r=n to the k.

But1<=m*(n to the k)+1. Also n,m,k<W, with n>=1,k>=1,W>=2, so

    m*(n to the k)+1
      <= (W-1) to the W +1
      <= W to the W
      < A <= T.

The second inequality follows from strict monotonicity of natural
integer powers: `W to the W>(W-1) to the W`. Thus a positive integer
strictly below T would be divisible by T, a contradiction. It follows
that every one of the15 original seed X values is positive. The proof
uses a bound on an actual nonnegative source output, not its intended
power meaning.

The selected calls use bases raw5,92,531 or530. They never use raw87.
Thus this sign-recovery stage does not assume f0>0 or T3>=0. The exact
seed/call/pair/modulus rows and their matching exponents will be
verified in the finite ledger.

## 6. Only now recover pow1 and the last missing modulus

Use the selected actual pow1 call for the seed exponent raw86. Its
base n=raw92 is1+f0*raw86 squared, hence positive even if f0=0. Its
output is V0=raw93; its modulus is raw730, already positive. Now that
this seed's X is positive, section4 and the ordinary positive Pell
residue give

    V0=n to the raw86 modulo T.

Both sides are nonnegative and strictly smaller than T: V0<W<A<=T,
and n to the raw86 <=(W-1) to the(W-1)<W to the W<A<=T. Therefore
`V0=n to the raw86>=1`.

The exact factorial ceiling/remainder identities give

    f0*C0=V0+s0,  C0=r0+s0+1>0.

Since V0>=1, f0>=1. Its base-f0 modulus/raw753 now satisfies T3>=A>0
by the same identity in section3. This is the only omitted modulus
whose positive-base premise was postponed. It is proved after the
independent raw92 call, before any use of a raw87 power call.

## 7. Pointwise guard regeneration and scope

All21 omitted raw values are now nonnegative at the original tuple.
No source body value was changed: abs(U), abs(Z) and S' were only
auxiliary numerical parameters used in mathematical proofs. All79
old guard values and their existing witnesses can therefore be kept.
Choose one Legendre triple for each omitted value and put the63 fresh
integer witnesses into their exact missing positions of the frozen967
equation. Conversely any967 zero restricts by forgetting those21
triples. This proves the integer-zero existence equivalence. The exact
actual-row/call ledger is bound to the proof by CERTIFICATE.json and the
independent checker described below.

The logical calibration and the signed-index theorem are inherited
from their pinned ordinary sources. No new internal-ZFC or Lean
transfer is asserted. Full new quartic coefficients and projected
counts are not yet materialized; they must be checked separately after
the dependency certificate and ordinary proof have been reviewed.

## 8. Exact finite audit and its scope

SOURCE_PINS.json authenticates the whole frozen source and prior packets,
including the original 1259-variable/1177-row builder, all 667 retained
variable identities, the actual arithmetic interfaces and the exact
reviewed signed-index manuscript. The included manuscript's byte hash
authenticates that supplied source; it is not independent authentication
of every upstream Git object mentioned in it.

CERTIFICATE.json contains the full expanded integer ideal combinations,
the sequential sign dependencies and the actual supporting-call choices.
The independent check.py imports no producer, optimizer or prior checker.
It recollects every polynomial from the original rows. In particular it
checks 575 sign rows and seven lower bounds from exactly 61 semantic
guards to all 643 semantic-prefix signs; all 431 positive-constructor
steps; all 15 strictly positive actual exponents; all 15 signed-index
instances; all 21 real power calls; all seven modulus cuts; and the
complete product, frame and bootstrap cuts. The selected calls are
0,1,5,7,9,10,12,13,14,15,16,17,18,19,20. Their bases are only raw5,
raw92, raw531 and raw530. The separately interpreted early call is
exactly pow1, with (base,exponent,output,X,Y,T)=(92,86,93,707,708,730).

The checker also collects eight universal polynomial identities and
rejects 15 deliberately corrupted certificates. Small recurrence and
endpoint controls cover negative roots and the smallest carriers. The
local example A=3,n=2,k=1,T=7,X=-3,Y=1,m=3,h=-1 is retained to show why
the strong carrier bound is necessary: it satisfies the local residue,
and m*n^k+1=T. It is not a zero of the complete source.

These finite checks establish the exact source binding. The unbounded
inequalities, induction, Pell descent and signed-index application are
the ordinary mathematical arguments in sections 1–7 and the pinned
signed-index theorem. Sampling is not their proof. The final 63 fresh
integer witnesses use Legendre's three-square representation of a
nonnegative integer by a^2+b^2+c^2+c, exactly as in the frozen guard
conversion. The remaining source semantics and consistency calibration
are inherited only after reaching the literal frozen 967 equation.
No new internal-ZFC or Lean theorem is asserted here.

From the repository root, the deterministic checks are:

```sh
python -B Computability/DiophantineConsistency/research/main-root-and-modulus-signs/generate.py --check
python -B Computability/DiophantineConsistency/research/main-root-and-modulus-signs/check.py
python -B -O Computability/DiophantineConsistency/research/main-root-and-modulus-signs/generate.py --check
python -B -O Computability/DiophantineConsistency/research/main-root-and-modulus-signs/check.py
```

VERIFY.json and VERIFY_OPTIMIZED.json record the two checker modes.
MANIFEST.json closes this packet's file set. Full new quartics and their
monic projection families remain a separate construction step.
