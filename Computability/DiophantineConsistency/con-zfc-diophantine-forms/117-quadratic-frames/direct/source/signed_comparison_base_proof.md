# Removing the comparison-base sign by an existential lift

This ordinary arithmetic note starts from the unchanged 1259-coordinate,
1177-row source and the independently reviewed 79-guard research packet
`research/main-root-and-modulus-signs`. In addition to its 21 omitted guards,
omit raw657, `shared_index.q4minus1`. Keep the other 78 guards. The result has
the same existence of integer source zeros. The extra removal is existential:
raw657 need not be nonnegative at the original tuple. No new quartic,
projected variable count, Lean theorem or internal-ZFC calibration is claimed.
The incoming ordinary source and consistency calibration remain the same
separate dependencies as for the frozen 79-guard packet.

The new ingredients are a signed comparison-*base* extension of the pinned
signed-index theorem, followed by a small lift using the existing common
unit. There is no need to select a new cofinal common Pell index or solve a
new simultaneous CRT problem.

## 1. Signed comparison-base lemma

Use the notation and all hypotheses of the exact signed comparison-index
theorem copied in the 79-guard packet, except permit an integer B with
abs(B)>=2 in place of natural B>=2. In particular A>=2, x,Y,U,k are natural,
U>=2,1<=k<=Y, V,S,R are integers, and

    x^2-(A^2-1)Y^2=1,
    U^2-(A^2-1)V^2=1,
    S^2-(B^2-1)R^2=1,
    Y^2 divides V,
    B=1 modulo4Y, B=A modulo U,
    S=x modulo U, R=k modulo4Y.

Then x=chi_k(A), Y=psi_k(A) still follows. Here is the full change to the
previous proof; all of its squared-divisibility and short-interval steps are
unchanged.

Put b=abs(B), e=sign(B). Classify at positive bases A and b:

    x=chi_i(A),Y=psi_i(A),
    U=chi_n(A),abs(V)=psi_n(A),
    S=epsilon*chi_h(b),R=delta*psi_h(b),

where epsilon,delta are independently in {1,-1}. The old argument gives
i>0,n>0,i<=n and Y dividing n. The Pell polynomials satisfy, by their
recurrences,

    chi_h(-a)=(-1)^h*chi_h(a),
    psi_h(-a)=(-1)^(h-1)*psi_h(a).

For h=0 the second expression means the same zero ordinate; no division or
negative power is used. Base congruence and b=e*B give

    chi_h(b)=e^h*chi_h(A) modulo U.

Consequently chi_h(A) is plus or minus chi_i(A) modulo chi_n(A). The old
half-period sign change and abscissa residue classification imply
h=plus or minus i modulo2n, with the endpoint i=n still allowed.

Modulo4Y the base b is e. Directly evaluating the same recurrence at1 and
-1 gives

    psi_h(b)=e^(h-1)*h modulo4Y.

The signed R congruence therefore gives h=plus or minus k modulo4Y.
As Y divides n, combining these statements gives i=plus or minus k
modulo2Y. Finally 1<=i,k<=Y implies i=k, including Y=1 and i=n. This proves
the generalized lemma. Neither S, R nor either progression quotient is
assumed natural, and no step uses the sign of B.

## 2. Actual 78-guard soundness before any lift

The independent 643-prefix sign proof, all positive exponent constructors,
retained base0 modulus and the bootstrap bound A>W^W are unchanged: their
exact source identities do not use raw657. The ordinates satisfy Y>=k>=1
from the retained 15 index slacks. The retained product factor/raw1214 gives

    V=(product of the15 Y^2)*(raw1214+1)>0.

The common norm gives abs(U)>=A>=2. Write q4 for raw657. The actual rows give

    B=1+4V(q4+1), B=A modulo U.

If q4>=0 then B>=5. If q4=-1 then B=1, which is impossible: the nonzero
integer A-1 is strictly smaller than abs(U) but would be divisible by U.
If q4<=-2 then B<=1-4V<=-3. Thus abs(B)>=3 in all possible cases. In
particular no degenerate comparison norm at B in {-1,0,1} is being classified.

For each possibly signed main X, use x=abs(X) and S0=sign(X)*S as numerical
proof parameters, exactly as in the frozen 21-sign argument. Apply the new
lemma at U0=abs(U) and the *original signed B*. It gives abs(X)=chi_k(A)
and Y=psi_k(A), without a q4 sign. The selected positive-base source calls
then exclude every negative X by the same small positive multiple
m*n^k+1 of T. The separate raw92/raw86/raw93 call gives f0>=1, and only
then gives the final omitted modulus sign. Hence all 21 omitted main-root
and modulus values are pointwise positive even in this 78-guard source.
This imports the already reviewed proof with its sole B-positivity use
replaced by the explicit generalized lemma; it does not interpret the power
calls before the necessary signs.

## 3. Lift only the comparison witnesses

Keep all 643 prefix values, W,A,Z,U,V, every main X,Y and every power
quotient. In particular U is allowed to remain negative. Let

    t=abs(q4)+1,
    q4new=q4+abs(U)*t,
    Bnew=B+4V*abs(U)*t,
    bqnew=bq+4V*sign(U)*t,

where bq/raw658 is the old unrestricted quotient B-A=U*bq. Since
abs(U)>=2, q4new>=abs(q4)+2>0. The two defining equalities persist:

    Bnew=1+4V*(q4new+1)>=5,
    Bnew-A=U*bqnew.

For each of the 15 seeds set

    Snew=chi_k(Bnew), Rnew=psi_k(Bnew),
    sqnew=(Snew-X)/U, rqnew=(Rnew-k)/(4Y).

These are integer witnesses. Indeed Bnew=A modulo U and the already
oriented main root X=chi_k(A) give U dividing Snew-X. Also Y^2 divides V,
so Bnew=1 modulo4Y and base-one reduction gives4Y dividing Rnew-k. The
fresh comparison Pell norm is exact. The quotients sqnew,rqnew,bqnew need
not be nonnegative and have no retained guard. No coprimality of the
different Y values is required.

This changes exactly 62 private free slots: q4,bq and four comparison slots
for each seed. Reevaluate their topological integer gate descendants. The
fresh actual-row audit proves the complete use boundary, without relying
on variable names or a macro-privacy assumption:

* Exactly141 unit gate rows are affected. Every source gate, including a
  square-difference gate, has an exact earlier-coordinate polynomial
  definition with unit coefficient, so reevaluation stays integral.
* Exactly46 nongate constraints are affected: the15 comparison norms,
  their30 congruences and the single B_mod_U row616.
* Each of those46 constraints has a complete original-row ideal identity
  whose only nongate row is that constraint with coefficient1. Its target
  norm or congruence is satisfied by the displayed fresh witnesses, so the
  original constraint vanishes once the defining gate rows vanish.
* No source prefix value, power argument or power quotient changes. All
  16 main index pairs, including the derived pair/raw921,922, remain fixed.
  The common norm, full product V, discriminant and bootstrap values remain
  fixed. No other retained guard value changes.

All unaffected original nongate rows remain zero, while all gate rows and
all46 changed constraints have just been restored. This is a complete
integer source zero with q4new positive and the original other78 guards.
Adjoin a fresh Legendre triple for q4new to reach the 79-guard source (and
then the frozen parent). Conversely any 79-guard zero gives a 78-guard
zero simply by forgetting the q4 triple. Together with the frozen 21-sign
argument this proves the claimed zero-existence equivalence. There is no
claim that the old q4 value itself has become positive.

## 4. Exact audit and limits

`audit.py` imports no author source builder, checker, optimizer or emitter;
it reuses only the small polynomial collector of the separate independent
21-sign peer. It authenticates the sealed 79-guard research packet and
whole frozen original source pins. It checks all1029 actual topological
unit gate definitions, computes the exact62-slot/141-gate dependency
closure, and independently collects all coefficients of the46 unit
constraint ideals. Its receipts list every changed slot/gate/constraint.
They also check that the other78 guards, all main pairs and every actual
power argument and quotient are outside that closure. Both complete lift
identities are collected over a free integer polynomial ring.

The normal and optimized Python modes both pass. Their18 exact negative-B
Pell lift fixtures include both signs of U;78 recurrence controls test the
negative-base parity identities. These finite fixtures are diagnostics;
Sections1–3 give the unbounded proof. No full new SOS or projected counts
are inferred from this dependency packet. No Lean work is performed.

```sh
python3 -B Computability/DiophantineConsistency/research/comparison-base-sign/audit.py --output /tmp/comparison-base-normal.json
python3 -B -O Computability/DiophantineConsistency/research/comparison-base-sign/audit.py --output /tmp/comparison-base-optimized.json
```
