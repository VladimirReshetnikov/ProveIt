DEPTH-PRESERVING CAYLEY NORMAL FORM
=================================

Companion artifacts for the ProveIt continuation, pinned against repository
commit 570b0567f311cf1890865065896be2665f469e4f.

This contribution constructs an algebra retraction for the full convergent
Cayley shuffle ideal whose output never increases series depth. It proves
an exact filtered polynomial description and gives finite Witt-character
formulas for the quotient dimensions at every weight and depth. It does
not assume that the corresponding complex periods are independent.

The full Cayley ideal projector, its weight-seven total dimension 7518,
and nonmembership of the frozen S6 target were already established in the
inspected golden-cayley-double-turning report. The new contribution is the
depth-preserving representative, the exact filtration, and the associated
dimension refinement. The S6 numerical conjecture remains unresolved.

Files
-----
article/05_cayley_depth.tex       Complete mathematical section and proofs.
article/cayley_references.tex       Bibliography entries used by the section.
depth_projector.py               Exact rational normal-form implementation.
cayley_filtered_counts.py        Exact all-weight character/Hilbert formulas.
verify_depth_projector.py        Independent finite verification suite.
depth_projector_verification.json  Generated verification receipt/tables.
project_s6_depth.py              Frozen, attributed S6 target and projection.
s6_oriented_normal_form.json     All 30 rational normal-form coefficients.

The four Python files use only the Python standard library. No upstream
repository Python file is required. Run from any directory:

    python /path/to/verify_depth_projector.py
    python /path/to/project_s6_depth.py

The integrated verification script writes its JSON receipt in verification/ by default. Its default
checks use exact integers and rational fractions: all 780 words of weights
1 through 4; 2150 shuffle products; independent consecutive-cut versus
permutation Eulerian formulas; and independent, fraction-free integer
linear algebra for the whole Cayley ideal in each depth through weight 4.
The all-weight result rests on the supplied proofs, not finite testing.

Conventions
-----------
Outer-letter-first words; adapted alphabet codes are Z=0,Y=1,H=2,B=3,X=4.
In original forms, X=c-b, Y=a-abar, H=a+abar-b; see the LaTeX section for
the complete form definitions and admissibility conditions.

The normal form is not generally pointwise fixed by Cayley C. It satisfies
Pi C = Pi, Pi^2 = Pi, ker(Pi|A)=J and Pi(F_D A) subset F_D A. The equation
C Pi = Pi is intentionally not asserted. For example Pi(ZY)=ZY but
C Pi(ZY)=YX. All depth-minimality claims refer to A/J alone.

At weight 7, the K-odd exact-depth dimensions are
    1, 34, 347, 1582, 3115, 2123, 316.
Their sum is 7518. Depth at most 4 has dimension 1964, so the complete
Cayley ideal intersects the 2546-dimensional bounded ambient space in
dimension 582. The 23-dimensional balanced unmultiplied anti-invariant
space is a different, smaller object; products are essential.

The frozen S6 target's oriented normal form has 30 adapted-word terms,
all of depth at most 2. It remains nonzero, including coefficient
[Z^5 Y H] = -166348800. This is a formal ideal statement only, and is not
a proof or disproof of the proposed numerical S6 identity.

LaTeX integration
-----------------
The section expects amsmath, amssymb, amsthm, booktabs and hyperref, plus
the theorem environments theorem, lemma and proposition. It provides a
fallback shuffle macro only if one is not already defined. Include the
bibliography fragment inside an existing thebibliography environment.

Do not package the temporary modular-search files, upstream copies or
duplicate baseline sources in this working directory as new deliverables.
