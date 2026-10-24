# Directly enumerate the same language and rebuild its complete native tuple

This ordinary research replaces the sorted-rank definition of the fixed
943-tile BFS language by a direct enumeration. It does not change a machine
action, tile, edge color, native support position, mask, radix, arithmetic
kernel or input domain. It DOES change DC and K, so its whole native and
controller interface is established afresh below. No equality of the old
and new specialized polynomials or pointwise reuse of packed F,C,R/native
witnesses is asserted.

The standalone equation.pdf/equation.tex retain the complete current
98-operation, exact-degree360 arithmetic front. All fixed constants are
printed through the unchanged436-character seed and the new finite tile
table. There are no hidden coefficient files in that specification.
Delivered binary payloads are independently checkable copies of the
printed constants. The seed is data, never executable machine code.

## 1. Exact enumeration and complete conjugacy

Decode the same430 actions from the fixed seed, retaining the complete
breadth-first state permutation pi on215 active states and halt215.
Every transition(q,b,v,m,u) becomes(pi(q),b,v,m,pi(u)); blank state0 and
halt215 are fixed. Thus the renaming commutes with every machine step,
not just a finite sampled run.

Use the printed head labels h(q,b)=2(q+1)+b and target sets R/L.
Their sorted ranks give r_q=6..204 and l_q=205..249. The new table puts
Start at0, Forbidden at1, transitions at2..431, halt passes at432..433,
plain passes at434..435, right moves at436..833 and left moves at834..923.
Indeed424+2r_q+b and424+2l_q+b run through those complete intervals once.
Cleanup924..927 uses j+430 floor(j/2)=(0,1,432,433). Fixed control tiles
occupy928..930, followed by the three497+t indices931..933. The last
formula934+3a+b-6 floor(a/4),a in{0,1,4},b in{0,1,2}, covers934..942.
Consequently all indices0..942 occur exactly once. Comparing every tuple
with the old BFS language proves that this is exactly its tile SET.

The literal initializer is(3,436,4,4). The decoded first action has
(v0,d0,u0)=(1,1,1), so its last coordinate is h(1,0)=4. This is the
renamed original initializer at target93, not an accidentally retained93.
The entire typed-color conjugacy is unchanged: preserve horizontal0..5,
map each old right/left target color to the corresponding pi-target rank;
preserve vertical0/1 and434..438, and map h(q,b) to h(pi(q),b).
These are bijections on all250 horizontal and439 vertical colors. They
map every one of the original943 tiles onto the new set and fix Start
and Forbidden. They preserve every local edge equality, blank-start
condition, forbidden condition and padded/periodic tiling interpretation.

There is additionally an exact selector permutation from the old sorted
BFS list to the new direct list. It fixes selectors0 and1. No new graph
isomorphism or machine-calibration assumption is needed to reorder that
same finite set; the inherited Wang943/refutation theorem applies through
the complete color and transition conjugacy just described.

## 2. The regenerated native clauses, masks and carry bounds

Retain rho=2^67,L=8807,d=590069,B=rho^L and the printed support E of
986 positions. For tile t_i=(w,n,e,s), define

    v_i=w+2^8*n+2^17*e+2^25*s+127*2^34,
    c_i=1+2^10*(2^41-v_i), 0<=i<943.

The same38 copy and3 anchor coefficients are2^(10+j), one per payload
bit j=0..40. Both dummies1063/1064 still have coefficient0. Every label
has the same8/9/8/9-bit bound and the four occupied bits plus three anchor
bits are unchanged. Therefore1<=v_i<2^41 and all c_e are nonnegative.
The displayed Phi polynomial equals sum_e c_e*x^e exactly, including all
copy/anchor coefficients and its two zero dummy coefficients.

Apply the unchanged aggregate complement lemma at a=10,m=41,N=943.
For Boolean selectors and copy bits, its masked sum is valid exactly for
an empty cell or one selected tile whose full41 payload bits agree with
the copies. That lemma is symmetric in selector indices. The new selector
permutation, fixing0/1, therefore preserves the entire local language,
including distinguished Start and Forbidden cells. It does not assume
that the packed numeric words themselves stay equal.

Regenerate the complete coefficients

    DC=rho^30+rho^62+rho^1100+rho^2201
        +sum_e c_e*(rho^(4393-e)+rho^(5495-e)), DR=rho^42,
    K=DC+B*DR, beta=B-1,

and MC,MF_native from the printed unchanged mask/support formulas.
MF_source=MF_native+beta is shifted exactly ONCE. Beta, MC and MF_source
are byte-identical to the old coherent BFS tuple. New K has592884 bits
and raw SHA256
0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f.
The four values are nevertheless treated as one regenerated coherent
tuple, not an arbitrary substitution into a K-specific source theorem.

The full66062 basis identities are recollected with this new DC. At every
tested copy/anchor target, all current, spatial and temporal coefficients
are the same prescribed Boolean-copy interfaces; at both clause targets
they are exactly the new c_e. The support/anchor intersection facts depend
only on E: the two clause bands are disjoint and the two anchor bands
intersect only at0. The old whole-cell rotation/alignment proof therefore
uses precisely its previous support and parity premises. Occupied bits
still propagate occupation and the local tests give exactly the same
Wang-language tilings.

The multiset{v_i}, hence sum_e c_e, is unchanged by this permutation.
The exact carry threshold remains118788496120850159560<rho. This is the
ACTUAL old BFS threshold; the original unrenamed compact44 tuple has a
different threshold and is not used as an equality premise. All padding
bounds and dummy safety estimates remain: largest unshifted product
exponent8791, tested zero padding8792..8805,2 max(E)<8807, and2mu+4<rho.
Mask populations remain pc(MC)=590069-986,pc(MF_native)=986, with
MC=2 mod4,MF_native=4 mod8 and0<MC,MF_native<beta. Also0<DC<B.
Thus every finite premise of the uniform native soundness proof holds.

## 3. Rebuild the cofinal actual-rank controller for the NEW DC

The selector permutation can change the native packed F,C and actual rank
R. They are not transferred pointwise. Completeness starts with a fresh
padded halting tableau and encodes each tile by its NEW selector. Its
native copied edges, masks and anchors are valid by Section2. The fresh
actual rank R0 is then corrected using the controller below.

Keep the existing prime lambda=581197,k=lambda-1=581196. The radix B is
unchanged. Its exact orders modulo67,8807,lambda remain66,4403,581196,
and B^k modulo lambda² remains182964883980, different from1. Thus the
lambda-adic lifting valuation is1. These primality/order/lift facts are
verified again independently. Only the controller's DC-dependent bracket
needs new values. For H0=1+B*DC+B²*(DR+1), the new residues are

    prime      B      B²-1       H0
    67         46     38         23
    8807       456    5374       3359
    581197     348469 573553     404489.

Every listed factor is a unit. The same rectangular/helical padding
lemma permits independent large spatial width w and time height h, powers
of lambda. Put N=wh=lambda^n,q=B^N; choose N>d*lambda² and h>lambda.
The order certificates give q=B^w=B modulo d*lambda. Changing a safe low
dummy1063 bit in native cell j changes the fresh actual packed rank by

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q²-1)*[1+q*(DC+B*DR+B^w)].

This is the inherited coefficient-independent dummy identity with the NEW
DC/K substituted in its formula. Modulo each prime divisor of d*lambda,
its nonconstant factors are precisely B²-1 and the new H0. Hence
GCD(Gamma,d*lambda)=1, and so GCD(Gamma,dN)=1 for this whole fresh tuple.
No old DC, F,C, R0 or Gamma value is reused.

For completeness reproduce the Boolean subset step. Set T=N/lambda,
C0=d*lambda. Since B^k=1 modulo d and has order T modulo lambda^n,
its first T powers are exactly{1+C0*z:0<=z<T} modulo dN. Every residue
modulo dN is a Boolean subset sum of

    {B^(2+k*j):0<=j<T} union{B³}.

Normalize the desired residue by B^-2. Choose epsilon=0 or1 so subtracting
epsilon*B leaves a nonzero residue modulo lambda. Let a be its least
residue modulo C0; then1<=a<C0<T and GCD(a,T)=1. Write the target as
a+C0*u and choose z0 with

    a*z0+a(a-1)/2=u modulo T.

The a distinct orbit coordinates z0,...,z0+a-1 modulo T sum to the target;
include B³ exactly when epsilon=1. All bit choices are Boolean. The
largest cell index is at most N-T-lambda+3. Since w<T, its translates by
one and w remain below N and avoid the origin; the separate3 is distinct
because k>1. The same safe no-wrap dummy theorem applies.

Apply this subset construction to(R0-dw)*Gamma^-1 modulo dN. Fresh dummy
choices then make the actual rank satisfy R=dw modulo dN, as required by
the source's temporal rotation. Dummy coefficients remain zero and all
label/carry/mask constraints survive. The odd d,N and unchanged population
and low-bit conditions still give pc(R)=3dN+2 and R=3 modulo4. The inherited
odd/square-scale padding freedom is therefore present for arbitrarily
large canonical tableaux, at the same d and lambda. These are cofinal
completeness promises, not restrictions imposed on arbitrary soundness
witnesses.

## 4. Whole source and arithmetic-kernel equivalence

Soundness uses the new native constraints to recover its fresh tiling,
then the complete color/transition conjugacy to obtain the original
blank-halting run and finite syntactic refutation. Completeness encodes a
refutation's padded run with new selector bits, regenerates the rank as
in Section3 and invokes the uniform native compiler/Pell converse with
this new coherent tuple. It chooses fresh F,C,R and all arithmetic/Pell
witnesses. The new index data are never identified with old native words.

This supplies exactly the normalized positive source interface and cofinal
canonical promises used by the accepted index-weight98/360 ordinary proof.
Its local arithmetic argument is uniform in the four ports satisfying
beta odd,beta>=31,K>0,0<MC<beta<MF_source<2beta, all verified here.
Its source soundness constructs the prescribed fresh unscaled witnesses;
its completeness uses the canonical family supplied above. Thus that
whole ordinary ten-positive proof composes with this new native theorem.
The original K-specific theorem is not invoked by numerical equality.

The standalone printed arithmetic front is BYTE-IDENTICAL to the sealed
current98/360 page's front and has the same universal free-port source
binding. The new polynomial.json preserves every arithmetic row/domain/
operation and changes only its whole coefficient binding and provenance.
Every fixed numeral is also reconstructible directly from the full
printed recipe, including the same436-character seed, all62 alphabet
characters and every indexed tile. All98 operations remain live.
The exact degree360 leading coefficient2^20*beta^184 is independent of K,
MC,MF, and beta is unchanged and nonzero. Hence the current degree proof
still gives exact degree360 for this complete new specialization.

The full printed recipe shrinks2393 to2343 nonwhite characters and the
whole page3217 to3167, a saving of50 in BOTH metrics. The complete standalone
PDF is one Letter page, with no overfull boxes and unchanged9-point body
and seed type. TeX source shrinks5638 to5433 nonwhite characters. All new
index explanations are counted; the gain is not inferred from seed bits.

This is an ordinary composed source/calibration proof with complete finite
premise audits, not a new Lean/internal-ZFC derivation or a proof of ZFC
consistency. No canonical page, common report, frozen coefficient tuple,
source packet or paused Lean file is changed by this research packet.
