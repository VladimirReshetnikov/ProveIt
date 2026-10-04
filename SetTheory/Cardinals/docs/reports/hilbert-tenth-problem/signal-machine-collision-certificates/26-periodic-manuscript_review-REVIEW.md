# Independent final manuscript review of Report56

4 October 2026. **PASS on the final source and 15-page PDF identified below.** No substantive mathematical correction, source-credit correction, or visual defect remains. This is a fresh conventional manuscript review, supported by separately authored exact checks. It is not proof-assistant verification or journal peer review.

## Reviewed identities and one clarification

Final article source: `article/Report56.tex`, SHA-256 `8c5f54158e5ca70cc7d92497ee6fb6d32fb1e49d9a03b8aed14e0498e88642b6`.

Final PDF: `article/Report56.pdf`, SHA-256 `4853f8c578f42b7273d693199ce768f8b68c95fa8ee64433f959b122751136ea`, 15 Letter pages.

The initial review pins were source `c737fd7bc362d3891af4c24100455d729f682691ecd6595ad4464f5e96fff3d0` and PDF `07161982de63e7fea1fc73fd6a6eccb20ed3cc7eb40b706375348931fee3ef48`. Both matched the actual release when reviewed. I suggested making the normalization explicit in Section 4.1: a full-period zero sum concerns the trigonometric factor after dividing by the positive factor rho^n. The writer changed “the values over a full period” to “the normalized values over a full period.” The theorem and mathematical reasoning did not change. The entire source delta is verified by removing that one word and recovering the original source hash. Only page 5 changed; I directly re-inspected it. The other fourteen final page PNGs are byte-identical to the inspected originals.

Frozen proof SHA-256: `df7cefb472a76e6f34ce7fff0b1e8548782a82f4863fac2ecd2d682c69941a77`. The final packaged proof is byte-identical to the supplied frozen proof. No frozen science or audit file was modified in this review.

## 1. The stated hypotheses support the theorem

Sections 1–3 and Appendix A explicitly require a fixed rational machine, number-preserving local rules, a prescribed nonempty finite word of complete batches, strictly positive intervals between batches, an outgoing collision section, and exact return of the ordered labels and outgoing co-location pattern. The input/output sets at a collision have pairwise distinct speeds. Equal speeds at distinct sites are allowed. Simultaneous remote sites and every input to a multiple collision are included. Zero-duration cascades are excluded rather than silently absorbed into the word.

Rational initial gap encoding x=p/q, q>0, is stated before the theorems; the rational translation can be supplied separately. The rational-limit theorem expressly requires rational initial positions. These requirements matter: a free irrational translation would invalidate rationality of absolute position limits, though it would not affect the validity signs or duration.

The machine data and macro coefficients are compilation constants. They are not additional polynomial variables. Arity can grow with the prescribed word, while repetition count is not a witness parameter. The article expressly denies a uniform fixed arity over all words. Witness uniqueness is per encoded input, not across equivalent numerator/denominator representations of the same rational geometry.

The dimension count d=N−1−|Z|≤N−2≤2 is sound because number preservation ensures a genuine collision leaves an outgoing co-located group. It is collision-anchored; the article correctly warns that a later observation phase would add a coordinate. Multiple collisions and simultaneous binary groups only decrease d. For d=0, a nonempty positive-flight macro is impossible by homogeneity.

The adjacent-pair chronology proof is complete. Speed-sorted outgoing zero blocks separate immediately. Every closing adjacent pair supplies a candidate time; equality forces inclusion in the next batch and strict comparison excludes omitted simultaneous sites. A nonadjacent crossing cannot occur before an intervening adjacent gap vanishes. Local number preservation preserves spatial slot counts across each replacement. The linear chamber and induction criterion EM^n x=0, GM^n x>0 therefore certify all finite prefixes, including their final section constraints. No global off-chamber invariance of M is assumed.

## 2. All order-two spectral cases are present and correct

For each equality observation, the first two values suffice by Cayley–Hamilton, including singular and defective matrices. Padding dimension one by a zero coordinate does not introduce a physical state variable.

The nonreal discriminant branch is handled before squaring. Dividing by rho^n reduces signs to a sinusoid. For a rational rotation, its full-period sum is zero; for an irrational rotation, dense phases reach a negative arc. A nonzero observation therefore cannot remain weakly nonnegative, and no observation is strictly positive forever. A nonempty legal macro has a strict positive-time guard, so this branch is empty. In particular, a pure-imaginary spectrum whose square is a negative scalar matrix cannot slip into the positive-root branch.

For real spectrum, both parities of M are reduced through B=M^2. The four cases exhaust alpha≥beta≥0:

- alpha>beta>0: strict positivity is A0>0 and A1−beta A0≥0. Zero dominant coefficient is permitted because the smaller root is strictly positive
- alpha>beta=0: both A0 and A1 must be strictly positive; the vanishing-tail boundary is correctly rejected
- alpha=beta=lambda>0: the Jordan formula gives A0>0 and nonnegative slope A1−lambda A0. The scalar case is included without a diagonalizability assumption
- alpha=beta=0: no infinite strictly positive sequence; the weak condition uses the first two nonnegative values

Weak variants are stated separately. Negative real roots, opposite roots of equal modulus, negative Jordan roots, and zero roots are all covered by testing both parities. The sign-separated radical elimination C≥0 OR (C<0 AND H≥0), with H=Delta A0^2−C^2 and A0≥0, is correct including A0=0. It does not square a sign-ambiguous comparison.

These are elementary order-two arguments, not a proposed finite spectral criterion for arbitrary-dimensional Positivity. No physical realization is claimed for a generic higher-dimensional recurrence counterexample. In fact, no such counterexample is presented in the final article. Its concrete nonsquare-spectrum diagnostic is two-dimensional and is explicitly described as a recurrence diagnostic, with no signal-macro realization asserted.

## 3. Quartic degree and canonical natural witnesses

The six residuals for each quadratic sign atom have total degree at most two. Boolean flags plus a one-hot sum select exactly one sign. The magnitude equation fixes z=|Q|−1 when Q is nonzero. The additional e0*z residual pins z=0 at Q=0, so the zero branch has no free natural slack.

The AND, OR, and NOT gate equations deterministically propagate Boolean values along an acyclic circuit. Their outputs need no extra Boolean constraints. Requiring the final output to be one and summing residual squares gives an ordinary integer polynomial of degree at most four with one natural zero on accepted inputs and none on rejected inputs. This proof is global; finite witness mutations are not used as a substitute for uniqueness. No quadratic guard is multiplied by a selector, which would risk a cubic residual.

The ledgers 4A+J witnesses and 6A+J+1 residuals are correct. Constant formulas and positive-witness shifts are handled without changing the core claim. The result makes no general finite-fold/single-fold MRDP claim.

My new checker independently reconstructed every sign residual and gate residual of each literal export, then expanded and compared the entire coefficient dictionary. Both exact identities pass, as do complete abstract sign truth tables, including sign combinations that may not come from a natural input:

- Four-signal certificate: 2 atoms, 2 gates, 10 witnesses, 15 residuals, degree exactly 4, 65 nonzero monomials; all 9 sign cases pass
- Quadratic recurrence diagnostic: 3 atoms, 5 gates, 17 witnesses, 24 residuals, degree exactly 4, 117 nonzero monomials; all 27 sign cases pass

The first atoms are d and 2y−d. The second atoms are x, C=x−2y, and H=4x²+4xy−4y². For A=[[2,−1],[−1,1]], the eigenvalues are (3±sqrt(5))/2, and H=5x²−(x−2y)². The displayed positivity meaning of this diagnostic is correct. The exact export hashes agree with the frozen artifact audit.

## 4. Observable clock, deadline degree, and rational limits

The physical clock is the strictly positive scalar observation ell*M^n*x. Its summability classification correctly treats both parity subsequences. A stable pair is summable; a dominant root at least one must have exactly zero visible coefficient when the smaller root is in (0,1); two roots at least one cannot supply a summable strictly positive sequence. The zero-small-root and repeated-root cases use their correct strict-tail and Jordan conditions. The nilpotent branch cannot support a valid infinite strict clock.

The cancellation condition C<0 AND H=0 is the correct degree-two equality test under A0>0, Delta>0. The article correctly allows an invisible neutral or unstable whole-matrix mode and does not confuse matrix spectral radius with observable summability.

The ordinary clock-sum formula follows from the parity generating function. Its denominator 1−t+h may be negative if an unstable mode cancels. The exceptional denominator-zero case requires a simple eigenvalue one plus a surviving root below one, giving (ae+ao)/(q(2−t)); a repeated unit root cannot support a strict summable clock. Fixed-sign denominator normalization is explicit.

Deadline equality and strict comparison use DqH−K*L(p), with q,K>0 and section time zero. This is degree at most two in the stated integer inputs. The article explicitly warns that a further variable-denominator initial-time offset would require fresh degree accounting. No uncounted rational offset is hidden in the theorem.

For any fixed finite population, the rational-limit proof is valid conditional on the prescribed macro's validity and finite accumulation. Rational generating functions and Abel limits make the time sum rational. Number preservation permits each spatially ordered signal coordinate to be followed continuously, with a common finite speed bound making it Lipschitz. The leftmost displacement series is absolutely bounded by the clock series; convergent gap sequences have rational Abel limits. A fixed macro-phase collision site lies within one shrinking macro duration of a boundary position. A finite rational prefix preserves rationality. This does not supply an arbitrary-dimensional validity-recognition algorithm and does not define a post-accumulation execution.

## 5. Example and diagram

The complete two-bounce chamber d>0, y>3d/8, return (d/4,y−3d/8), duration 3d/8, and displacement 3d/8 are consistent. The R–S candidate is the only possible competing adjacent collision not already in the shuttle macro. The first K complete cycles require y>(d/2)(1−4^−K). Their intersection is y≥d/2. A finite endpoint tie is excluded; a contact existing only at the accumulation time is correctly retained by finite-prefix semantics.

The example has four live signals and five available speed values. Its return spectrum is {1/4,1}, but the clock observes only the contracting component and totals d/2. The integer late-failure seed d=4^(K+1), y=d/2−1 passes K cycles and fails the next; K=0 is correctly described as an empty prefix followed by a competing first tie.

Figure 1 accurately draws xL=t, xR=1−t, xS=3/2−2t. My exact rational check verifies all eight displayed bounce vertices, alternating wall membership and shuttle slopes +3/−3, and the even-bounce time formula. The final short segment is explicitly a convergence indicator rather than another physical flight; the limit has an open circle and a no-batch label. The caption says the diagram is analytically derived and not a physical simulation.

## 6. Source credit and implementation boundary

I checked the primary sources directly:

- [Becker et al., Abstract Geometrical Computation 8](https://arxiv.org/html/1307.6468v1), Definition 1 and Section 3.1, Figure 7, Lemma 6, support the distinct-speed rule convention and classical shrinking-wall shuttle. The source measures speeds rather than the number of live signals; the article maintains that distinction
- [Ouaknine and Worrell, Positivity Problems for Low-Order Linear Recurrence Sequences](https://www.cs.ox.ac.uk/james.worrell/pos12.pdf), especially Section 6, supports the strict/non-strict distinction and confirms that low-order positivity is prior work. The article does not overstate the cited order-five strictness result

I also read the preserved repository README/review material relevant to the finite-schema comparison. The manuscript accurately separates complete finite collision chambers from accumulation semantics and states that a physical-time bound is not an event bound. It discloses that the full merged article exceeded the connector limit and was not obtained, treats saved-text hashes as such, and calls its exact-phrase overlap search bounded rather than exhaustive. I did not independently repeat that historical connector retrieval or repository search, and do not certify those historical events beyond the retained records.

The abstract, Section 10, Section 12, and Appendix A clearly state that the general machine-and-macro frontend is mathematically specified but not implemented. The generic implemented component begins at a quadratic sign formula. No optimal arity, maximum decidable population, arbitrary-run liveness, general Positivity solver, physical realization of the recurrence diagnostic, or novelty/priority claim is made. Classical ingredients are credited.

All historical numerical test counts displayed in Section 10 agree with the corresponding retained receipts. They are carefully described as finite regressions; the stronger exact coefficient-dictionary identity is identified separately. I did not rerun old author or audit programs. Release/replay security and build claims were read as packaging claims; their full adversarial behavior is outside this manuscript review and belongs to the separate release-tool audit.

## 7. Direct visual review and final evidence

I directly inspected every original final-page image at 115 dpi, then directly inspected the revised final page 5. I independently rendered both the initial and final pinned PDFs with Poppler. The initial renders exactly match the inspected render-d pages; the final renders match render-e, with only page 5 changed. Thus the entire visual review binds to the final PDF, rather than an unverified draft render.

Page-by-page findings:

1. Title, abstract, reading guide, and contents are legible and fit
2. Theorem hypotheses and scope are readable without clipping
3. Section dimension and chronological chamber display cleanly
4. Linear chamber and induction proof have intact equations and references
5. Revised nonreal proof and recurrence case list are clean; the final Jordan display remains within the page
6. Radical elimination and canonical sign gadget are legible
7. Gate equations and arithmetic ledger are clean; the clock case list continues normally
8. Continued clock case, cancellation, and rational-time formulas are intact
9. Deadline expressions and two-bounce example fit without overlap
10. Diagram, labels, open limit marker, caption, and displayed boundary formulas are clean
11. Late-failure example and all-population rationality proof remain readable
12. Export ledger table, diagnostic matrix, and evidence counts are legible
13. Proof hash and execution-boundary text fit without overflowing
14. Source comparison, limitations, and compiler checklist are clean
15. Checklist continuation, boundary table, references, and URLs are legible

No clipped text, overlapping elements, missing glyphs, unresolved references, misleading limit marker, or unreadable page was observed. The paper is appropriately dense for a mathematical report.

Machine-readable receipts are `arithmetic-receipt.json` and `visual-binding-receipt.json`. The corresponding checkers were newly authored and inspected in this review before execution. They use only exact integer/rational arithmetic, ordinary file/hash operations, JSON data parsing, installed PDF tooling, and pixel comparisons. No submitted emitter, upstream program, saved schedule, physical simulator, or Lean code was imported or executed. The `final-pdf-render` directory preserves the independently generated final page images.

**Recommendation: release the final pinned manuscript as scoped.**
