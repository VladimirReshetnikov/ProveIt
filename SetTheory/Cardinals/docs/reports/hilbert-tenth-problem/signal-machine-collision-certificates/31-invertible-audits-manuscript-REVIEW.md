# Independent Report 61 manuscript review

Date: 4 October 2026 UTC. Reviewer: independent manuscript-review task.

## Verdict

**PASS for the exact final source and 19-page PDF bound below.** All requested mathematical topics and every final rendered page were reviewed. The generic scale-dimension qualification and production issues in the correction log are resolved. No remaining mathematical or visual correction is required. This is conventional review with exact arithmetic support, not proof-assistant certification.

## Scope and protected inputs

The manuscript under review is the Report 61 modular LaTeX source in the release directory. The source authority is the frozen proof SHA-256 `dc97e30c56817370138d6be760d44a5df031743a0ee1011cca39381b67bb0cec`. Its positive-compiler dependency has SHA-256 `e0ddd64cdbbb5c7f448266ab58f1dfeb2868892ac0f230632b2337e4d0bed065`. The preceding independent scientific review has SHA-256 `8e8d6158cf3e3bcfe384deb92c19684ca01715ae82612db6eba28158e2b61819` and its manifest `dbbc49723fad5b5ab34cd8dab1b8824d66d22b50e384d948e1de0576b7e16aef`. These pins were directly recalculated and agree with the manuscript.

Frozen scientific programs, stored schedules, old constructors, simulators, and proof-assistant artifacts remain inert. The reviewer read the mathematical source and dependency as data. The newly authored `review_static_identities.py` was displayed in full before execution; it imports only the Python standard library and reads no scientific source file. Its receipt records 47 exact rational equalities and 23 whole-interval positivity certificates. It does not select events, advance machine states, or sample trajectories.

## Mathematical review

### Full outgoing section isomorphism

For source H_a=ker(h_a), target H_b=ker(h_b), and constant velocity v transverse to both, P_b(q)=q-v(h_bq)/(h_bv) sends H_a to H_b. Substitution of h_a q=0 into P_a P_b q gives q, and exchanging a,b gives the other inverse. The manuscript proves both directions. The ambient kernel Rv is transverse to the source; it is not a kernel of the restricted map. Positional identification at binary events remains invertible even when the labels change, because the coincident input and output coordinate pairs share their contact value.

The proof correctly fixes every occurrence/order/phase chart, allows repeated labels without collapsing positions, and excludes remote simultaneous events. The full open chamber is used to identify a proposed linear law uniquely, not to manufacture transversality. The common translation vector is fixed by flights and collision identifications, giving an honest quotient isomorphism. Subtracting a moving anchor is a valid quotient chart. The dimensions n−1 before translation and n−2 after translation are correct; scale normalization leaves n−3 when the remaining quotient point is nonzero, as holds for n≥3 with a positive remaining gap. The final text explicitly handles n=2 separately: its translation quotient is zero-dimensional and scaling is trivial. The five-signal dimensions 4,3,2 are unaffected. No global inverse collision machine is inferred.

### Determinant sign and magnitude

Deleting target row b and source column a from I−w e_b^T/w_b gives the true omitted-gap chart matrix. The stated adjugate is w e_b^T/w_b, so the chart determinant is (−1)^(a+b)w_a/w_b. Equivalently the flux form i_w(dg_1∧...∧dg_d) is preserved by adding multiples of w to its tangent arguments. Both manuscript proofs are valid. For a physical positive flight w_a>0 and w_b<0. Multiplication telescopes the face-coordinate sign to (−1)^(m+a_0+a_m), and a literal return gives (−1)^m. Literal outgoing closure makes the source-opening list a cyclic permutation of the event-output list. The exact positive factor is therefore the product of output/input pair-speed ratios. The caveats about different end charts and ambient label-permutation signs are correctly stated.

### Seven-event primitive

Every global affine-line formula, time, position and interval duration agrees by direct rational substitution. The speed table has eleven labels and five live occurrences; the two distinct X phase labels at speed −1/2 are legitimate. Every rule has distinct speeds on each side. Event 4 is marker-only: the messenger has exactly the same line and Q_middle phase on both sides. The table and analytic center diagram encode that same fact.

All noncontact gaps are strictly positive on 1/4<x/y<1 and D/y>1. Their normalized values are affine in x/y with nonnegative endpoint values and at least one positive endpoint; the distant gap is D/y−1>0. All seven flight times pass the same strict interval proof. Because gaps are affine in flight time, no unlisted contact occurs between successive sections, including the possible post-event-4 target/messenger catch. At every endpoint exactly one adjacent gap vanishes.

Under only 0<x<y<D, the first three events are valid. Thereafter the only next-contact candidates are X_fast/Y and messenger/L, with difference (4x−y)/2. Equality produces a remote simultaneous pair; negative difference produces the wrong next event. This proves necessity by the first actual failure, without continuing an invalid word. Thus y<4x is exact. The final marker position F=−2x/3+5y/6 lies strictly in (0,y). Event 6 restores X_0, event 7 restores Q_+, and all stationary section roles close. The speed-ratio product is 2/3 and seven-event sign gives −2/3. The centered J and its inverse are correct. Removing R removes one independent scale coordinate and yields only a one-dimensional normalized section.

### Singular obstruction and normalization scope

The homogeneous full-section matrix N is invertible. Under the fixed positive scale condition N=λ diag(1,A), det N=λ³ det A, so A must be invertible. The affine variant λ[[1,0],[b,A]] has the same determinant. For a general invertible homogeneous matrix [[a,β],[c,B]], the chart map (c+Bw)/(a+βw) has Jacobian determinant det N/(a+βw)³. The manuscript's block elimination proves this even if B is singular. A positive projective scale chart is therefore locally nonsingular; forgetting an independent coordinate or restricting to a proper slice changes the problem. All relevant exclusions are explicit and no stronger impossibility is asserted.

### Positive compiler and label composition

The frozen dependency establishes the same stationary-marker section, rational positive determinant compiler, exact center-containing guards, literal phase closure, and uniform duration bounds. Its elementary primitive and factorization claims were read as proofs, not executed. For det A<0, B=J⁻¹A has positive determinant; chronological composition gives J B=A. Since normalization cancels the positive scale, the exact composite chamber is P_B∩B⁻¹P_J. It is open, rational, bounded, convex and center-containing. Exactness follows by the first failed block.

The explicit interface is valid: the positive compiler uses event-private messenger labels, so its final input rule is unique. Replacing only its final P_0 output by private Q_+, and replacing only reversal event 7's output by P_0, causes no duplicate-input conflict. Intermediate reversal Q_+ outputs remain private. The marker-only event uses the fresh X_fast label and leaves the messenger alone. The completed machine is finite, deterministic, number-preserving, and has five live signals. The positive event count is even because T is even; appending seven yields the required odd count. The eleven-label bound is clearly confined to the standalone primitive.

### Infinite validity and rational clock

Literal closure gives exactly ⋂ A^(-n)P. The positive compiler supplies duration at least 2D; the appended J duration is less than (38/9) times its entrance scale. Thus the macro duration is bounded above and below by fixed positive multiples of λ^nD_0 on an infinitely valid run. The Zeno criterion is exactly λ<1. Every strand lies within a constant multiple of the shrinking scale in that case, so it approaches the fixed left anchor; no continuation beyond accumulation is claimed.

For rational initial z, its rational cyclic subspace span_Q{z,Nz,N²z} is invariant by Cayley–Hamilton. Bounded normalized shape and λ<1 imply N^nz→0, hence N^n→0 on this subspace. The restricted I−N is invertible over Q, and the total time is ℓ[(I−N)|_V]⁻¹z∈Q. Restricting before inversion is essential when N has an unused eigenvalue 1. The manuscript retains this distinction.

### Additional exact reversal kernel corollary

The final manuscript addition in Section 5.7, separate from the frozen proof, is also checked. With r=x/y, f(r)=5/6−2r/3, the one-word interval is (1/4,1). Intersecting with its one-step inverse gives I=(1/4,7/8); f(I)=(1/4,2/3)⊂I. This proves the exact infinite kernel. In positive integer gaps g_1=x, g_2=y−x, g_3=D−y, the two required strict inequalities are 3g_1−g_2>0 and 7g_2−g_1>0. The sum of their residual squares equals zero exactly for the unique positive integer pair u=3g_1−g_2, v=7g_2−g_1. The final corollary explicitly states the positive-integer input and witness domains. The far-spectator gap imposes no extra restriction beyond positivity. At r=1/4 the first word ties; at r=7/8 the first word is valid and its image begins the second word at that excluded tie.

The iterate is x_n=y/2+(−2/3)^n(x−y/2). Summing the exact word duration gives T_N=(53/18)yN+(23/15)(x−y/2)(1−(−2/3)^N). The baseline and geometric-sum coefficients are freshly checked, so the standalone λ=1 primitive is non-Zeno on the infinite kernel.

## Primary literature verification

The following primary source pages were opened directly on 4 October 2026. The citations and their limited role are accurate.

- Becker et al., https://arxiv.org/pdf/1804.09018, Definitions 1–2 on PDF pages 4–5: distinct speeds within collision sets and finite-support configurations; Example 5 on PDF page 6 explicitly has distinct labels at equal speed. The seven-author list and 21 March 2019 revision match https://arxiv.org/abs/1804.09018.
- Durand-Lose, https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2006_CiE.pdf, PDF pages 2–5: rational space/time convention, positive-energy conservation, equal-energy number preservation, injective rule-map reversibility, and the no-accumulation qualification. These are contextual distinctions, not a source for the present compiler.
- Alishah–Duarte–Peixe, https://arxiv.org/pdf/1411.6227, PDF pages 21–24: constant-direction section projection (5.2), its sector, reversed-flow inverse immediately after (5.3), and fixed-itinerary composition. Metadata at https://arxiv.org/abs/1411.6227 confirms Nonlinearity 33(1), 2020 and the 19 November 2018 v3. This is a real geometric precedent; the manuscript appropriately avoids claiming novelty of the underlying linear algebra or exhaustive prior-art coverage.

## Correction log

1. The initial source had a missing backslash before `quad` in the infinite-validity display. Reported to the writer and fixed.
2. The parent review identified that the generic n−3 scale-dimension sentence needs a nonzero quotient point, with n=2 treated separately. The writer added the exact qualification above; independently checked. The five-signal theorem is unchanged.
3. The first PDF had empty Title/Author/Subject metadata. The writer replaced the ineffective raw metadata setup with hyperref metadata.
4. Initial PDF page 9 placed its two related tables far apart on a float-only page, separating the surrounding prose. All 19 initial pages were inspected; no clipping, overlap, missing glyphs, mathematical rendering errors, or incorrect diagram endpoints were found. The second build resolves this spacing issue; all 19 final pages were inspected again and pass. Metadata was also directly verified with pdfinfo.


## Final source and PDF binding

- Standalone `Report61.tex`: SHA-256 `133122c9c7c2c894fdbe30a67d9f5274d9d5293d8bc638a212c9e883181af683`
- Modular manuscript pin file: SHA-256 `768309347285fb5c98be4a3a0c691755cb0228b373543beb486f04797ad8f277`
- Final `Report61.pdf`: SHA-256 `bb9f61e0620fd23186b351c1427521f83c6eacd90ce18717417235f2fc7d4893`; 19 pages, Letter size
- The standalone TeX is byte-for-byte the expansion of all six pinned modular files, replacing each complete input line, including its terminal newline, by the named module bytes. An initial token-only comparison differed solely by five doubled boundary newlines; the whole-line comparison is exact. Every module byte count and SHA-256 was independently verified. The complete per-file bindings are in `REVIEW_RECEIPT.json`.
- PDF Title, Author and Subject are populated correctly. Text extraction is available. The final log has no undefined references, missing glyphs, overfull boxes or build errors. Its expected disabled-shell-escape warning and two underfull bibliography lines are harmless and were visually checked.
- The independent tool reviewer produced the final locked build. This manuscript review does not replace the separate build/release/replay security reviews.
- Original frozen science hashes, byte sizes, permission modes and modification times match the before/after snapshots. No source science was changed.

## Final all-page visual inspection

The reviewer opened each native final 120-DPI page image, not merely extracted PDF text. The exact image hashes are recorded in `REVIEW_RECEIPT.json`. All pages pass:

1. Title, abstract, model and theorem assumptions: all readable and complete.
2. Theorems, determinant product, reversal matrix and GL2 criterion: equations and numbering clean.
3. Contents: section labels and page destinations agree; deliberate contents-page whitespace.
4. Transverse flight lemma and its two-sided inverse proof: all symbols and fractions clean.
5. Translation quotient and corrected n=2/nonzero-scale qualification; gap definition and determinant lemma clean.
6. Adjugate and flux-form proofs, sign telescoping and singular-obstruction opening clean.
7. Affine/projective normalization and start of reversal section: block matrices and Jacobian formula legible.
8. Speed table and seven-rule table complete; labels, signs and speed-ratio columns all legible.
9. Affine-line and event-position tables now adjacent, followed by durations and chamber discussion; former large float gap resolved.
10. Complete endpoint gap table and first-failure proof: rows, signs and prospective times correct and clear.
11. Centered guards and analytic spacetime diagram: exact center times, all seven contacts, stationary markers and unchanged event-4 messenger line verified.
12. Centered inverse, parity, infinite kernel and two-positive-integer-witness corollary/proof: complete and unclipped.
13. Finite-macro clock and positive-compiler theorem: equations and qualification text clean.
14. Positive event count, chronological matrix product, exact guard pullback and interface replacements readable.
15. Literal phase closure, infinite-validity identity and duration inequalities legible; quad typo absent.
16. Zeno scope and rational cyclic-subspace time proof complete; primary-literature discussion begins cleanly.
17. Literature scope, evidence layers and full cone certificate: no missing signs, clipping or misleading provenance.
18. Pinned SHA-256 strings fit; additional-corollary provenance and future-question list readable.
19. No-Zeno-continuation caveat and all four references complete; two logged underfull bibliography lines are visually harmless.
