# Independent audit: remove the derived-label range

## Scope and notation

This audit concerns the composition of the factorial-free,
linear-radius binomial CRT front with the pooled-power certificate.
It changes the weight scale to F=t^K with K>=D t, retains strict ranges
0<=a,b,c,d<t, deletes the separate binomial range for the derived
label sum J(a,b,c,d), and relocates the semantic Pell anchor to the
actual global row-index representative C. All variables of the final
polynomial remain unrestricted integers. Variable powers below are
the mathematical meanings of polynomial Pell certificates.

The final principal source retains the original C222 calculus and uses
D=2^20, t=128+4z^2, K=t^4. Its separate 213/214-coordinate companion
families use t=16+4z^2 and K=2^20 t. The final bound for the OLD calculus
comes from the independently source-bound constructor-depth certificate:
maximum constructor depth 19 gives label<t^(2^20-1) for t>=16.
Consequently K=t^4>=D t at every principal horizon.
The separately audited fixed-role seed calculus is an optional logical
experiment and is not used to calibrate the principal equation.

The inherited papers distinguish the actual arithmetic representative
C from the private Pell ordinate also formerly called C. Here the
private ordinate is denoted Ycap. The nominal anchor index is C.

The audit inspected the exact local copies of 157-linear-crt's main
proof, 158-pooled-powers' strict-horizon and pooling proofs, and the
round-17 signed-anchor and orientation-first proofs. It does not certify
an emitted variable count or compile a new proof-assistant development.

## 1. A sufficient label bound without a range equation

The strict schema-parameter tests recover local values a,b,c,d<t.
Let D be a fixed positive integer such that every formula label used
by any local axiom, modus ponens, or generalization branch satisfies

    0 <= label <= L=t^D

on that box. The exact finite syntax majorant certifies such a bound.
The inherited coarse D=2^22 is sufficient, but the final old-C222
constructor-depth certificate justifies D=2^20 under t>=16, as stated
above. A different generic base-2 ledger had also bounded the optional
fixed-role seed syntax by individual exponent 1,767,290 and aggregate
exponent 1,767,294. Those older ledger values are not the justification
for the final old-calculus choice D=2^20.

There is no need to recover J(local)<t. A polynomial label evaluated
on the global representatives still reduces to its correct local
value modulo the selected prime power, because all operations have
integer coefficients. The local amplification bound is retained:
the entire nonnegative local constraint is less than 2^x and hence
less than the selected amplified prime power. This licenses exact
decoding even though individual labels can exceed t.

## 2. Exact product separation at F=L^t

Discard factors with label zero, whose weights equal one. Suppose the
two products of weights 1+jF agree; all remaining labels satisfy
1<=j<=L. The conclusion side has at most t factors and the premise
side has at most 2t+1, including the target factor. Let r be the smaller
factor count, so r<=t. If the counts differ, the larger-count product
is at least (F+1)^(r+1), and the smaller is at most

    (1+L F)^r <= L^r (F+1)^r.

Equality would force F+1<=L^r<=L^t=F, a contradiction. Thus both
counts equal some m<=t. For m=0 both multisets are empty.

For m>=1, replace F by an indeterminate z in each product. Every
elementary coefficient e_k, 0<=k<=m, is a positive integer and

    1 <= e_k <= binom(m,k) L^k
       = binom(m,m-k) L^k
       <= m^(m-k) L^k <= L^m <= F.

Here m<=t<=L. This includes k=0 and k=m; no strict upper bound on
the individual coefficients is asserted. Corresponding coefficient
differences have absolute value at most F-1, which is the strict
bound needed. If their difference polynomial were nonzero, its lowest
nonzero coefficient would be a nonzero multiple of F after evaluation
at z=F, impossible. Therefore the two polynomials agree identically.
Their distinct rational roots -1/j recover exactly the multiplicity
of each positive label. This proves the inherited Horn-flow conclusion
with the enlarged labels and F=t^(D t), including the boundary case
m=t and maximal leading coefficient F.

For comparison, F>(L+1)^t is another sufficient condition: it bounds
all coefficients strictly without needing the positivity refinement.
That stronger condition is unnecessary for the proposed final scale.

## 3. The signed Pell anchor is independent of syntax

The orientation-first anchor proof first uses a signed nominal index
h, the square frame |h|<W, the squared cap |Ycap|>|h|, and the
comparison congruences. It proves h!=0 and that the classified anchor
index equals |h|. Every other principal classified index is then
smaller than |h|<W. The pooled abscissa and ordinate errors orient all
pairs to their canonical signed indices. None of these arguments
requires h to be a syntax polynomial, nonnegative, or a power output.

Thus h may be replaced by the actual encoded row-index representative
C. Include its pair as the anchor, retaining its term in the pooled
orientation row and omitting only its duplicate term from the cap.
Before arithmetic signs are known, C is allowed to be signed.
The cap/comparison argument excludes C=0. Once |q+1|>=2 has been
proved, the existing (q+1)^C request makes C nonnegative, so it is
then positive. C is literally parameterized as 2c, providing evenness
needed for canonical odd-auxiliary completeness.

The former derived-label pair can be reassigned to the new exponent
D t of the individual power request F=t^(D t). The existing t pair
must remain, because q^t is still needed. D t is an affine expression
in the retained horizon; it must be present in the square frame and
in the appropriate orientation term. The old J numerator, range
quotient, normalized remainder, and all dead J computation gates can
then be deleted. Exact counts depend on the emitted circuit, not
on this proof description.

## 4. Acyclic soundness bootstrap

Use either final horizon and growth-index choice above, F=t^K, R=F, C=2c,

    H=2+4(C+sum of the eight other representatives),
    y=F(2v+1),
    B h_B=C+F+1,
    x=F+1+(y+1)u0,
    x=1+[1+(t+1)y]ut.

The signed anchor/frame and orientation argument precedes all power
interpretation. Since t>=16 and K>=D t>0, the first request authenticates
F as a positive even integer, with F>=t^t>=2^64. The right side of
B h_B=C+F+1 is odd even before C's sign is known. Hence B is odd
and nonzero. H=2 modulo 4 at every signed assignment, so |BH|>=2.
The unchanged individual request q=(BH)^x gives x>=0.

The odd multiplier in y makes |y|>=F, so
|1+(t+1)y|>1. The terminal endpoint excludes x=0. Consequently
|q|>=2. The q-block request q^(y+1) now forces y+1>=0, excluding
negative y, whose magnitude would be at least F. Thus y>=F>0.
The initial endpoint then gives u0>=0 and x>=F+1. The terminal
endpoint gives ut>=1 and x>=2+(t+1)y. Therefore x>=3 and
|q+1|>=2. All ordinary representative requests are now interpreted
and their indices are nonnegative. H is positive.

The first binomial recovery proof in 157 applies verbatim with the
larger F: for j<=t the coefficients of (q+1)^(F+t) are bounded by
(F+t)^t<=2^[t(F-1)], while |q|>=2^x and x>=2+(t+1)F.
The signed low remainder is less than |q|^t/32. The common norm
gives a half-width normalized remainder, so uniqueness recovers
the true digit. Since |B|<=|BH|<|q|/2 and the true digit is
less than |q|/32, its congruence with B is equality. Thus
B=binom(F+t,t)>0, and q,N are positive.

No derived-label request was used in this schedule. The other range
digits are bounded using only H's domination of the actual ordinary
representatives and lower indices <=x. The exceptional J coefficient
bound is no longer needed. The local source estimate Rlocal^E<2^x
is unchanged because y>=F, x>=2+(t+1)y, and the retained old-calculus
local majorant remains within the inherited fixed E=2^23 budget.

## 5. Cofinal completeness and order of construction

Start with a finite original-C222 refutation. Choose a cofinal horizon
t=128+4z^2 (or t=16+4z^2 in the affine-growth companions) exceeding
its length and every schema parameter and guard
witness used in the finite proof. There is no need to bound formula
labels by t. Form F=t^K and all pending-state products with the
new weights. Choose an arbitrarily large positive odd multiple w of
the odd part of t!, and set y=F w. Since
v2(F)=K v2(t)>=2t>v2(t!), t! divides y. Make y exceed every
pending state and F. The pairwise coprime beta moduli then give an
arbitrarily large x with the intended endpoint and row data.

Now compute B=binom(F+t,t) and N=B^x. These are independent of C.
The usual binomial-CRT theorem applies because F>=t^t>L_t^2.
Moreover B is odd: v2(F)>floor(log2 t), so v2(F+i)=v2(i)
for 1<=i<=t, and the numerator/denominator valuations cancel.

Construct the ordinary representative classes at precision N^2.
First fix the eight non-index representatives in their required
classes. Then choose C in its required class modulo N^2, even and
arbitrarily large, exceeding every other requested exponent,
including K, t, F+t, x, y+1, and all ordinary representatives.
This is possible because N^2 is odd: addition of N^2 switches
parity, while addition of 2N^2 preserves evenness and is cofinal.
The relation B | C+F+1 is preserved because B divides N^2.

Only now define H from these actual representatives, and set
q=(BH)^x. Then form all requested powers and the actual square
frame, and finally choose the Pell center A. Enlarging C increases
H and q, so it cannot destroy the binomial coefficient domination;
N divides q because q=N H^x. There is no dependence of the prior
CRT modulus N^2 on C or q.

All non-anchor indices are strictly below the even nominal anchor C.
The canonical growth estimate in the inherited cap proof gives its
required positive square slack. Its odd auxiliary construction uses
the evenness of C exactly as before. The canonical power requests,
the pooled quotient coordinates, normalized digit remainders, and
the universal ternary quadratic representation fill the remaining
rows. Removing one remainder only improves the common norm's budget.

## Verdict and artifact obligations

No circularity or cofinality conflict was found in this transformation.
The order t,F,path,y,x,B,N,representatives,C,H,q,frame,A resolves
the potentially dangerous dependency. The exact finite circuit must
still verify all changed actual offsets, the C=2c parameterization,
the K request/pair assignment, all frame atoms, the moved anchor
and its cap/orientation occurrences, deletion of the full J range,
and the new local-label bound. For the principal equation this arithmetic
proof composes with the original C222 calibration. The fixed-role seed
calibration is a separate optional application of the same arithmetic
argument with its own syntax bound. This is an
ordinary ZFC-formalizable argument, not a freshly compiled Lean
or Rocq theorem and not a proof of Con(ZFC) itself.

