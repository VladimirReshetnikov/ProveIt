# Independent review: the 407-natural / 888-integer direct quartics

**Accepted at the ordinary mathematical level.** I found no gap in the
projected source, low-digit radix reuse, additive index certificates,
natural restoration or integer sign/projection arguments. Both full
normal and optimized replays passed. A separate checker imports no
delivered module and verifies the raw export, every coefficient in all
five equations and the source/provenance bindings. Lean remains paused.
This review does not supply a new kernel theorem or an encoded internal
object-ZFC derivation.

The immutable archive is
`docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip`, SHA256
`59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59`.
It contains 130 members; all 129 entries of `SHA256SUMS` match actual
bytes. Review scratch is `/tmp/proofs62ff-407888-review`.

| Domain | Variables | Residuals | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| Natural source | 690 | 606 | 4 | 3,762 | 63,905,979 |
| Natural | **407** | 323 | 4 | 8,420 | 83,843,774 |
| Natural | 410 | 326 | 4 | 7,029 | 211,184,624 |
| Integer | **888** | 470 | 4 | 10,156 | 2,445,790,974,704 |
| Integer | 917 | 499 | 4 | 6,986 | 63,906,036 |

Naturals include zero; integers are unrestricted. All coordinates occur.
The 407 point improves the just-frozen 502-natural candidate in all listed
size measures. The 410 point trades three coordinates for fewer terms.
The 888 point improves the former 1,190-integer count, with a much larger
coefficient height; 917 retains the lower-height alternative. These are
specific direct-quartic tradeoffs, not global minimality claims.

## 1. The eight-column source preserves the actual rules

I read the complete rule table in `report.tex`, the inherited projection
proof and `build_projected.py`. The four parameters a,b,c,d remain free.
The truth and eight unconditional axiom alternatives have premises 0,0;
the ninth axiom alternative retains its bundle guard. Modus ponens is
parameterized by `(a,I(a,b)) -> b`; generalization by `(b,0) -> A(a,b)`.
These are exact substitutions in the original rule instances. The
constructor DAGs used for all nine axiom labels and the generalization
label match the authenticated old source.

The projected accumulator alternatives are correspondingly
`S_next*w(v)=S*w(p)*w(q)`, with `w(j)=1+Mj`. Their product vanishes
exactly when one permitted rule and its update hold. Truth gives
`S_next=S`. The guarded alternative uses
`((c-a)^2(c-b)^2-(d+1)^2)^2`; its zero condition has not lost either
sign of `(c-a)(c-b)`. For natural parameters a suitable d exists exactly
when c differs from both a and b. The two beta reconstruction squares
stay outside this disjunction, so an unselected branch cannot bypass
them.

A finite proof can be expanded to a tree, padded with zero-balance truth
rules and assigned a horizon t at least its length and all four parameter
values. This justifies bounding the four schema columns by t without
bounding arbitrary axiom labels by t. The other columns are S,S_next<=y
and the two beta quotients <=x. Completeness chooses y after the finite
accumulator trace, then its beta code x; its canonical quotients are
automatically <=x. Soundness recovers strict remainders from
`S,S_next<=y<1+(i+1)y`. No deleted remainder slack is used.

The carrier is `M=((t+1)^t)^(2^22)`. A literal 266-gate majorant bounds
every label plus one by `(t+1)^(2^22)`. The one-sided degree bootstrap is
valid: if `prod(1+v_i M)=(1+M)prod(1+p_i M)(1+q_i M)`, the left side
is strictly less than `M^(t+1)`. Nonnegative coefficients force the
right polynomial's degree to be <=t. Each side then has at most t
nonconstant factors, so its value at 1 is <=M. Because its constant
coefficient is 1, each individual coefficient is <M. Base-M uniqueness
gives the polynomial flow identity. The usual outside-the-closure linear
functional proves target derivability even with cycles and repeated
premises. There is no bounded-refutation substitute for the unbounded
source theorem.

## 2. Radix reuse avoids a circular product estimate

Let `R=2+t+x+y+M0`, `H=R^(2^23)`, `rho_n=(n+2)^(n+2)` and
`V_n=(rho_n+1)^n`. The reused radix is

```
q=B*(V_H+1),    sum_(j=1)^8 a_j+g=8B,
```

where every encoded column a_j is positive. Only three binomials are
represented exactly: those inside the H-factorial, t-factorial and
modulus-product formula. The other eight graphs represent divisibility
by B, which is all the range certificate uses.

The low-digit lemma is exact: bounding `binom(n,j)<q` only for j<=k
suffices to identify `floor((q+1)^n/q^k) mod q=binom(n,k)`. Arbitrarily
large higher coefficients only affect a multiple of q in that quotient.
If B divides q, divisibility of the quotient by B is therefore equivalent
to divisibility of the binomial. The two fused rows express precisely
that quotient and its Euclidean remainder; no digit/high-part variable
is silently constrained.

The order of the unbounded soundness proof is important and correct:

1. The shared frame proves all 23 requested powers pointwise at their
   present inputs. Every exponent is positive by literal construction.
   Every base, including the proposed radix, is nonzero because its
   natural modulus row `2An=T_n+n^2+1` excludes n=0. Thus q>0 and its
   definition gives B>=1, without first identifying the CRT product.
2. For n=H or t, rho_n>=n and the lower binomial coefficients through
   index n are at most `binom(rho_n+n,n)<=V_n`. Since H>=t,
   `V_t<=V_H<q`. Their exact digit graphs are correct, and the inherited
   factorial identity identifies the proposed outputs as H! and t!.
3. Let T=H! and `Q=(1+(t+1)T)^t+2`. The raw division/remainder rows
   already give B<TQ, independently of the product formula's validity.
   With `e=t(H+1)`, the inequalities T<=H^H and t+2<=H give
   `Q+t<=H^(e+1)`. The aggregate bound gives each a_j<8TQ, hence
   `a_j<H^((t+2)(H+1))`. The same upper bound applies to Q+t.
4. Every remaining lower index is <=R. Since H>=R^4, in particular
   `R(R+2)<=H`. Consequently every required low coefficient is at most
   `H^(H(H+1))`, strictly below
   `V_H>(H+2)^(H(H+2))`. All exact/fused binomial extractions are valid.
   Only now is the inherited formula used to identify B with
   `prod_(i<t)(1+(i+1)T)`.

The endpoint rows already force R>=4; all uses of the eight-column count,
positivity, t+2<=H and the range-index bounds are licensed. No estimate
derives B<TQ from the very product formula it is trying to validate.

For completeness, choose genuine source and factorial values first, then
the true product B. Every CRT column admits a positive representative in
[1,B], so the aggregate slack is natural. Set q as displayed, choose
Euclidean witnesses, and only then choose the common Pell frame. There
is no unknown global fixed point.

The index equality `1+(C+1)T=B` is also exact and complete. Since t>=1,
the true B is >=1+T and congruent to 1 modulo T, so
`C=(B-1)/T-1` is natural. It has residue i modulo each `1+(i+1)T`.
The new equality deletes an unnecessary quotient without excluding any
valid finite source certificate. Its use does not require a chosen CRT
index to survive unchanged.

## 3. Additive indices and signed natural restorations

There are 18 distinct exponent atoms but only 15 seed tests. The three
indices H+2,t+2,t+1 are constructed from H,t and the literal pairs at
1 and 2. The identities

```
X_(u+v)=X_u X_v+(A^2-1)Y_u Y_v,
Y_(u+v)=X_u Y_v+Y_u X_v
```

give total natural restorations, with D=A^2-1 introduced by its exact
row. All actual dependencies point to earlier arithmetic nodes. Recover
the 15 seeds by their indexed-Pell tests, then induct through the three
derived pairs. Only seed ordinates belong in the common auxiliary
product; the derived pairs require no extra index theorem hypothesis.
The original frame still bounds every requested base, exponent and output.

For simultaneous completeness the finite-unit period construction modulo
`4 product_seed Y_i^2` supplies U,V. Its norm gives gcd(U,4V)=1, so the
common auxiliary base can be chosen in both required congruence classes
and larger than A. This is the same valid common-witness argument as in
the synchronized parent, now for a smaller seed set.

The two natural contractions allow two restoring polynomials with signed
expanded coefficients. Their exact certificates write each as a positive
rational sum of affine squares plus a nonnegative-coefficient remainder.
They are therefore nonnegative at every natural tuple; their integer
coefficients ensure integrality. Every substitution is exact in every
remaining row and preserves degree two. Reverse restoration gives natural
preimages. The rational certificate is not a claim that the restoring
polynomial has nonnegative coefficients or that finite sampling proves
its sign.

## 4. The integer equations retain a complete sign proof

The 690-coordinate natural source is guarded at 167 selected coordinates;
the other 523 signs follow from actual existing rows. The independent
checker accepts either `c*x=P`, c>0 with nonnegative monomials whose odd
variables already have signs, or an exact affine-square P. Each inference
is tied to a literal original row. It establishes every source-coordinate
sign before any arithmetic macro is interpreted.

For each seed the fresh guard `x=a^2+b^2+c(c+1)` forces integer x>=0
and represents every natural x by the three-square theorem applied to
4x+1. The augmented system has 1,191 unrestricted coordinates. Signed
monic elimination then removes 303 or 274 coordinates, always substituting
into every row, including every guard. Its restoring polynomials need
not preserve naturals: first restore the full integer parent in reverse
order, then apply its guards and ordered sign proof. This is the correct
order and closes the potential signed-restoration gap.

## 5. Provenance and independent checks

All 51 retained upstream files are byte-identical members of the full
reviewed synchronized archive, SHA256
`ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf`.
All seven logical calibration pins match actual Git blobs at
`08200eb10fde2db408c69dffd840d6920a569b1f`. The ordinary calibration is
the named unconditional `KEndpoint.c222_iff_zf_refutation` followed by
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Its immediate
sources are included; this pause does not rebuild their transitive Lean
closure. The source encodes the numerical calculus, not a native machine
window, so no mixed native-port tuple is involved.

After inspecting the executed chain, I ran `verify.py --receipt ...` in
normal and optimized Python. Both reproduce all final coefficient and
certificate files in temporary directories and pass all arithmetic,
majorant, natural-restoration and integer-sign checks. The fresh receipts
are `/tmp/proofs62ff-407888-review/NORMAL.json` and `OPTIMIZED.json` and
are embedded in the separate review JSONs. Incoming files and extracted
defining artifacts were not edited. No Lean, TeX, inherited H10 emitter,
machine search, package installer or network command ran.

`tools/review_quartics407888.py` imports no delivered code. It additionally
checks every raw positive triangular gate, every one of the 17 signed
difference-square identities, every omitted affine restoration and the
entire raw-to-source690 export. It reconstructs every coefficient of all
five SOS polynomials and checks all coordinates live. Its independent
arithmetic controls deliberately include examples whose unused higher
binomial coefficients exceed the radix, as well as the canonical index,
positive eight-column CRT representatives, factorial low-digit bounds
and the new radix exponent inequalities. These are transcription controls;
the preceding unbounded arguments establish the mathematical equivalences.

There is no proof of Con(ZFC), consistency decision, or claim that a
checked external equivalence is already an emitted object-language ZFC
proof. The new ordinary constructions preserve the accepted refutation
source; the separate formalization obligation remains open.
