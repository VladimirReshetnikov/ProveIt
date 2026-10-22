# Independent review: signed quotient in the inputless construction

The following review checks the adaptation required before applying the
repository's `complete92_norm_unit_guard` and
`complete90_signed_root_elimination` arguments to the fifteen-variable
Start-only polynomial of package 06. It is a mathematical source review,
not a Lean/Rocq certification or a verification of actual halting.

## Conclusion

The signed-quotient extension is valid with the Start-only compiler
constants. No additional input witness is needed. The weaker Start-only
packing bound is sufficient. Consequently the algebraic root-elimination
arguments yield fourteen positive unknowns with the stated polynomial
degrees 293 and 342, provided their emitted circuits and coefficient recipe
are those separately checked in this package.

## 1. Bounds and order of proof

Allow only the auxiliary quotient T to be signed, while f and all other
supplied witnesses remain positive. The normalized strong factor and
auxiliary norm have the same unconditional modulo-four unit exclusions
as in `complete84_signed_quotient_absorption.md`. The input factor has
simply disappeared; it is not used by the first/main/auxiliary index proof.

The transport bootstrap still gives C>=0. It is essential not to claim
C>0 at this point: the same exceptional zero-boundary transport factor
can equal -1. With C=q-F-alpha, positivity of alpha yields q-F>0, and
the Start-only bounds give

    R < q^4-q^3+q^2-1 < q^4-2,
    R+2 < q^4 <= E,
    R<a.

These bounds suffice for every use of the upper estimate in the signed
p=R argument. There is no need to import the stronger historical bound
R<q^4-q^3. Absolute-value auxiliary Pell classification, direct normalized
rank, and the two squared/unsquared residue comparisons recover p=R.
The index sign then becomes positive by the same ratio contradiction;
the transport sign becomes positive by the product equation. Only now
does transport force C>0. Thus C+F<q and C,F>0 are available before
population decoding.

## 2. Power and half-binomial extraction

Sections 2 and 3 of `complete84_signed_quotient_soundness_scout.md` depend
on odd R, the first/main index relation, X=wq, Y=sq^3, and the strict ratio
kY<c<k(Y+1). They do not use the input bridge, its witnesses, or its
norm. Their lower ratio bound proves X=2^R. The exact upper ratio and
central-binomial expansion yield the same half-binomial value of Y and
the threshold pc(R)>=3dN+2. No auxiliary sign or residue R=3 mod4 is
assumed in these steps.

## 3. The exact Start-only word identity

Replace the old packed variable Z by C in the population step. Define

    S_word=(C-1)+qF,
    T_C=MC J+1,
    T_F=MF_native J-1,
    T_word=T_C+q T_F.

Because C,F>0 and C+F<q, one has 0<S_word<q^2. The literal Start-only
definition of R satisfies exactly

    R=(q^2-S_word)(q^2-1)+T_word.

Indeed its gap is q(q-F)-C. The shifted coefficient MFsrc=MF_native+B-1
is indispensable for this identity. The population lemma forces

    (C-1) AND (MC J+1)=0,
    F AND (MF_native J-1)=0.

The same low-bit mask conditions hold for the authentic Start-only
coefficient recipe: MC=2 mod4, MF_native=4 mod8, and J=1 mod4.
Thus C=1 mod4. Reducing the literal R gives

    R=C+MC J=1+2=3 mod4.

This conclusion is obtained before auxiliary positivity and does not
need a globally unique Start or an input End marker.

## 4. Restoring the auxiliary sign

The stronger chi step-down yields

    ell=epsilon R+2m z, epsilon in {-1,1}.

Keep e=sign(V), r=(R-1)/2. The two original unsquared congruences
V=-R mod c and V=-c mod f imply the ordinary sign equalities

    e*(-1)^(r+m z)=-1,
    e*(-1)^(r+(m+1)z)=-1,

using c>2R and f>2c. Dividing them forces z even. Since R=3 mod4,
r is odd, and hence e=+1. Therefore V>0. Finally
cTf=V+c+Rf^2>0 forces T>0. Both congruences are needed: retaining only
the congruence modulo f would leave a parity twist.

This proves that the signed-T zero set equals the positive-T zero set
on the actual Start-only compiler slice. As in the original source,
the only direct consumers of f are f^2 and Tf. Simultaneous negation of
f and T preserves every computed value, so the signed-f zero set with
T positive also has f>0.

## 5. Algebraic reconstruction after deleting f

For the normalized source define D_r=1+Delta i^2 c^4, b=c+R D_r,
u=cT, Q=(Delta i c^2)^2, and the usual A_r,B_r of the root-elimination
construction. Off zeros, D_r>c>0 and R is an integer, so b is nonzero.
Thus B_r=2Qub is nonzero throughout the retained positive domain.

For the product/unit-guard polynomial, the guard
1+A_r^2-D_r B_r^2 is 0 or1 plus1 modulo4 because B_r is even, and
therefore cannot be -1. The product equation forces the local norm to
zero and the retained factor product to one. The quotient A_r/B_r is a
rational square root of the integer D_r, hence is an integer. The exact
auxiliary remainder restores the parent zero. The signed-f result above
makes this root positive. The outer norm polynomial uses the analogous
nonzero denominator P4 B_r and gives the same restored root.

No failure of the inputless adaptation was found. The statement concerns
the authentic coefficient recipe; arbitrary assignments to the four
numeral ports are not covered by the signed-domain theorem.

## 6. Four-cell replacement coefficient contract

The new `four_cell_compiler.py` was also reviewed for the arithmetic
invariants consumed above. With a=439, its four slots are
(1,0),(1,1),(1,2),(2,1). The two horizontal and one vertical overlap
targets correspond respectively to the DC shifts H+a and 3a and the
DR shift H. The reduced overlap census is 3a. The four anchor positions
and the two separated clause bands retain their stated strict margins.

Write m=2pc(mu)+3a+2. There are m+1 native positions. The MC mask removes
the bit at every native position except selector1 and also removes the
additional ignored dummy bit. Hence pc(MC)=d-m-1. The high mask MF0 has
population 2pc(mu)+3a+2=m; adding its separate low bit4 gives
pc(MF_native)=m+1. These add to d. Since selector0 is a native position
and selector1 is omitted from the subtraction, the low residues are
MC=2 mod4 and MF_native=4 mod8. No high support enters these low residues.
Thus every low-mask and population hypothesis of Sections 2--4 remains
valid with this new recipe, provided all four ports are taken together.

The shifted initialization condition is also consistent with the domain
argument: an H center requires an initial phase at the following center,
and a non-H, non-V center forbids a following initial phase. Vertical
propagation handles the remaining V case. Globally this is the original
predecessor-H rule written at the preceding time. The distinguished Start
(L,Q,R,1) has distinct current and following center codes, excluding zero
temporal shift. The excluded tile (V,V,0,V) is locally allowed at its own
center but globally impossible, because its left neighbor would have
adjacent V centers. No genuine computation is removed by excluding it.

The reviewed numerical layout has b=5^13, cell length L=5^15, d=5^28,
and one ignored dummy position. These are coefficient-recipe parameters,
not materialized coefficients. The checks above establish the specific
contract needed by the signed-domain reduction; the separate compiler
proof supplies its full soundness and completeness.

## Reviewed source dependencies

- Package 06: `proofs/fixed_blank_67_proof.md`.
- `complete84_signed_quotient_absorption.md`, Sections 1--3.
- `complete84_signed_quotient_soundness_scout.md`, Sections 1--5.
- `complete92_norm_unit_guard.md`, Sections 1--5.
- `complete90_signed_root_elimination.md`, Sections 1--5.

The mathematical review is independent of the fresh circuit builder's
finite algebra and degree diagnostics, and does not convert them into a
formal proof of the inherited compiler.
