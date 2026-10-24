# Paired index-slack replacement with a local factorial bridge

This is research only. It does not remove guards from any accepted
equation or claim new variable/coefficient counts. All accepted packets,
the canonical page and Lean sources are unchanged.

The proposed domain change starts with the frozen 78-guard source:

* Replace raw1214>=0 by V/raw656>=1, using the same kind of three-square
  guard on V-1.
* Replace the two separate guards on the seed slacks for indices
  t/raw4 and k122/raw122 by one guard on their product. The existing
  index_at_most_Y rows identify these actual values as Y_t-t and
  Y_122-k122. Their product is already quadratic, so this guard does
  not require an extra product gate merely to state a quadratic row.
* Keep every other original guard, including the seed slacks at
  K/raw86 and k90/raw90. Keep the current t0/base0.T bootstrap premises.

Original zeros satisfy these new guards: all old slacks are nonnegative,
and the product formula already gives V>=1. The reverse map is pointwise
regeneration of the three removed old guard triples. The complete ordinary
local source proof is in LOCAL_FACTORIAL.md; its exact original-row cuts
and dependency checks accompany this research. A new projected quartic
family remains a separate materialization and review task.

## 1. The carrier excludes zero ordinates

The unchanged row identity is

    V=(product over all15 seeds of Y^2)*(raw1214+1).

V>=1 forces all 15 Y nonzero. The squared product is then a positive
integer, so raw1214+1>0 and raw1214>=0. This recovers that old guard
pointwise without assuming any Y sign or index upper bound.

All 643 prefix signs and A>W^W still follow from their unchanged
premises. The signed comparison-base proof still excludes B=1 and
gives abs(B)>=3, because its only needed product fact is V>0. It
therefore remains available with signed Y after replacing Y by abs(Y)
in the numerical theorem parameters.

## 2. Even positive index eliminates the small ordinate branch

Let a seed have positive even index k<W and Y!=0. Pell classification
of (abs(X),abs(Y)) at A>=2 gives an index i>=1. If abs(Y)=1 then i=1.
The signed abscissa residue/half-period argument gives the comparison
index h=plus or minus1 modulo2n, hence h odd. The signed ordinate
congruence modulo4 gives h=plus or minus k modulo4, impossible for
even k. This uses Y^2 dividing V, not the missing YminusK guard.

Otherwise abs(Y)>=2. Classification gives i>=2 and hence
abs(Y)>=psi_2(A)=2A>W>k. The signed-B index theorem now has the required
short-interval premise k<=abs(Y), so

    abs(X)=chi_k(A), abs(Y)=psi_k(A).

If an actual supporting call has 2<=n<W and 0<=m<W, its positive
modulus T>=A and A>W^W orient both coordinates. Write
p=chi_k-(A-n)psi_k and q=chi_k+(A-n)psi_k. Then
p=n^k moduloT and p*q=1 moduloT. The three unwanted signs imply:

    X<0,Y>0: T divides m*n^k+1;
    X>0,Y<0: T divides m*n^k-1;
    X<0,Y<0: T divides m+n^k.

The first and third are positive and strictly belowT. In the second,
the absolute value is strictly belowT, and equality to zero would
require m*n^k=1, impossible for n>=2,k>=1. Thus all three signs are
excluded, and X,Y are positive at the original tuple. Since k is
even and at least2, Y=psi_k(A)>=2A>k: the original slack is strictly
positive, which is the feature needed in the product argument.

## 3. Opposite parity of the two chosen indices

The exact raw constructors are:

    raw36=y+1,
    raw63=t+x+y+M0+2,
    K=raw86=raw63^(2^23),
    base103=1+(t+1)*f0,
    k122=t+raw104+2.

These correct two mislabeled register descriptions in the frozen
21-sign note's explanatory prose. Its full 431-step literal positive
constructor certificate already uses the correct original rows, so
none of its positivity conclusions depends on the mislabeled formulas.
Here raw63>=3 and K>=3; there is no assumed parity of K.

Keep the K and k90=K+f0*K^2 seed guards. The local source
bridge in LOCAL_FACTORIAL.md establishes factorial0.output f0=K!,
hence f0 even. Therefore base103 is odd. Its actual power row is

    X_t-(A-base103)*Y_t-raw104=T103*h.

For odd base103, T103=2*A*base103-base103^2-1 is even. Reducing the
main norm modulo2 gives

    X_t-(A-1)*Y_t=1 modulo2,

since z^2=z modulo2. The displayed actual residue therefore makes
raw104 odd. This parity argument does not interpret the t-index power
and does not assume its missing slack sign. Consequently k122 and t
have opposite parity.

The selected calls have bases t+1>=2 and raw531=raw530+1>=2,
respectively. Whichever index is even has strictly positive slack
by section2. The new product guard then forces the other slack to be
nonnegative. This recovers both original index guards pointwise.

## 4. The local source obligation is closed

LOCAL_FACTORIAL.md gives the complete unbounded bridge using only calls
1,5,6 at the retained K and k90 seeds. In order it proves raw93>=1,
f0>=1, radix raw530>raw93, exact choose0 digit extraction and
f0=ceil(raw93/raw91)=K!. All three actual digit/division bounds are
checked from complete original-row ideals. The bound on every coefficient
through K prevents lower-digit carry; no upper-digit or other power
meaning is required. The self-referential factorial radius is handled
by a strict rational-product bound, including the small boundary cases.

The same document verifies the new V-1 predicate recovers raw1214 and
all nonzero ordinates before the even-index argument, and closes both
directions of zero-existence at the unchanged source body. Neither a
full21-power interpretation nor the two omitted index guards are used
to establish the local bridge. The separate A/bootstrap-guard exchange
is not used here. No projected metric or new quartic family is claimed.
