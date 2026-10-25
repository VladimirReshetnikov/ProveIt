# Exact constant-recipe simplifications for the frozen three-anchor47 proposal

This separate CODE-FREE author note gives complete representation identities.
It edits no frozen source and changes NONE of the four integers or polynomial.
The structural improvement is a direct geometric MC recipe that no longer
inspects3297 coefficient digits. A second identity allows the old unshifted
tile table to supply the positive-label coefficients using one common bias.
No measured printed-glyph, TeX, page-fit or byte saving is asserted; the shorter
construction need not give the shortest printed spelling.

The exact reference is research/compact66-three-anchor-radix47: MANIFEST897B
SHA256 a79ae12654443d1a211e09028de8be34f1521bee770524ac2dea41a8d1c651a4,
README33901B SHA256 d3e85e5418b421b46f8e9345026ac19fd3dd6ba566822af749238bcadcc51c6f,
PINS20022B SHA256 9eb135bf6e6439797b61a958dbb0a2d20f6f2283184f34a8298c8655845ca3c0.
That complete adapter is an UNREVIEWED author proposal, not accepted by this
note. The identities here are unconditional algebraic equalities to its recipe;
they do not independently approve its native/Pell argument.

## 1. Whole MC without coefficient-digit extraction

Retain rho=2^47,B=rho^8807,beta=B−1 and G_m(x)=sum_(j=0)^(m−1)x^j.
All980 nonzero Phi47 positions are specified by the exact support polynomial

    S(x)=G_943(x)+x^983*(1+x^30)*G_9(x)
         +x^1003*(1+x^20)*G_8(x)
         +x^1095*(1+x^1100+x^2201).

Its intervals are943 selectors, the two9-bit label bands983..991/1013..1021,
the two8-bit label bands1003..1010/1023..1030 and all three anchors. They are
disjoint. It includes selector1 and excludes both zero-coefficient dummies.
Each of its coefficients is1 and every other coefficient is0. Thus the WHOLE
low-mask constant can instead be defined by

    MC=beta+rho-(rho+3)*rho^1063-G_943(rho)
       -rho^983*(1+rho^30)*G_9(rho)
       -rho^1003*(1+rho^20)*G_8(rho)
       -rho^1095*(1+rho^1100+rho^2201).                 (M)

Proof: every reference coefficient c_e is0 or satisfies0<c_e<rho. Therefore
floor((D_rho(Phi47(rho),e)+rho−1)/rho) is precisely the support indicator S_e.
The entire3297-term sum in the reference MC is S(rho), giving(M). Equivalently
sum_(e in E3,e!=1)rho^e=S(rho)−rho+rho^1063+rho^1064; after the extra2 at1063,
its original positive-support definition gives the same expression directly.
This proves the complete integer equality, including the forbidden selector,
both dummy holes and extra upper dummy, not just a sampled bit or residue.

Only geometric sums already used elsewhere in the recipe remain in(M). The
MC-specific digit extraction and its3297-term outer sum disappear. The generic
D_b operator REMAINS necessary in the action decoder; this note does not claim
that all floors or the seed's digit decoder can be removed from the page.

## 2. Positive colors from the old table with one bias

Let the ENTIRE old indexed table define(w_i,n_i,p_i,s_i), as printed in the
reference section1. Define the fixed constant

    a_*=2^34-(1+2^8)*(1+2^17).

Then the COMPLETE Phi can be printed directly as

    Phi47(x)=sum_(i=0)^942
       [1+2^11*(a_*-w_i-2^8*n_i-2^17*p_i-2^25*s_i)]*x^i
       +2^11*x^1003*(x^20+2^17)*G_8(2x)
       +2^19*x^983*(x^30+2^17)*G_9(2x)
       +2^45*x^1095*(1+x^1100+x^2201).                 (P)

For every943 index, expand(1+2^8)*(1+2^17)=1+2^8+2^17+2^25. The selector
coefficient in(P) is exactly1+2^11*(2^34−u'_i), where
u'_i=(w_i+1)+2^8*(n_i+1)+2^17*(p_i+1)+2^25*(s_i+1). Every34 label control,
three anchors and every unlisted zero are unchanged. This is equality of the
ENTIRE formal polynomial before any numerical substitution or evaluation.
The positive semantic colors are STILL t'_i=t_i+(1,1,1,1), not t_i itself.
Keeping the old table is a constant-spelling choice; the full bijection and
occupation proof in the reference retain exactly their positive-label meaning.
The actual shifted field bounds give u'_i<2^34, so every selector remains
positive and S is exactly the same980-position nonzero support.

This adapts the universal selector-distributivity approach already discussed
in compact-tile-parameters and direct-tile-coordinate-coefficients. It is not
another claimed cancellation of the old127-prefix or a new native encoding.
No source size or glyph count was calculated. Whether a_* plus(M) is shorter
than the current complete printed alternatives remains an actual-page question.

## 3. Whole tuple, proof boundaries and stopped leads

Beta and MF_source retain their literal definitions, including the exact
LOW24-at7694 padding and single native-to-source shift. Whole Phi identity(P)
gives the same K; whole support identity(M) gives the same MC. Thus the ENTIRE
tuple(beta,K,MC,MF_source), every P66 coefficient and every mathematical
solution are POINTWISE identical. In particular all frozen184-to22 carries,
occupied clause out1 and named resets,982/870 populations,47-phase alignment,
canonical subsets,ordinary deltaF,full47L controller and positive P66 maps
have exactly the same premises. No global proof obligation is being bypassed
by changing an encoding. H47 and any future admissible-prime condition are also
identical; this spelling cannot repair a failed finite unit.

All NEW finite H47/lambda conditions remain UNKNOWN and require separate
discharge. No49 theorem, old unit, optional kernel profile, R1 result, source
specialization or page endpoint is accepted here. Colorfield repacking would
change the copy kernels and predecessor exclusions, so no additional marker
deletion or lower radix is claimed without another complete proof. Those leads
were left open rather than promoted from a local coefficient observation.

The exact reference three files and both prior-art notes were read/authenticated;
new mathematics here is only distributivity and finite-support identities by
hand. No candidate/helper/import/AST/evaluator/application, coefficient array,
modular or prime search, source/TeX/PDF/Lean action ran. This author wrote only
this new note, with no parent/main/probe/review/source edit and no commit.
