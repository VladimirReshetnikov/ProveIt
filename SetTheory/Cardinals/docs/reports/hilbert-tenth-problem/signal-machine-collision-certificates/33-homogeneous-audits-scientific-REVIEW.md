# Independent audit of compatible homogeneous five-signal realization

Date: 2026-10-04 UTC  
Verdict: **ACCEPTED within the stated model and dependencies. No mathematical correction required.**

## 1. Source binding and execution boundary

This review concerns the frozen packet `compatible-homogeneous-realization63-20261004`, especially `PROOF.md`, SHA-256:

`31f0db773daa015075e74dabb8955c110288e1c0f9ed2121c647df034773aa67`.

The complete main proof, README, author checker source, manifest, both native DAGs, all four JSON evidence files, and all four preserved dependency proof/review texts were inspected as text or inert data. The independent certificate reviewer did not consult the author's checker. The fixed-center review was treated as a source-bound prior assessment, not as a substitute for reconstructing the new physical translation and left/right normalization.

The fresh core checker passed **840 named assertions**. A separate independently written standard-library sparse-polynomial checker passed **737 assertions** for the native certificate and literal DAGs. These are assertion counts, including repeated finite fixtures, individual graph-node checks, and file authentication; they are not counts of independent theorems. The conventional all-parameter arguments below are essential. Neither checker is a proof assistant.

Only freshly authored, displayed, inspected audit mathematics was executed. No author/upstream scientific script, earlier constructor, physical simulator, saved physical collision schedule, or Lean program was executed or imported. The generic 26-rule declaration produced here is finite inert data; checks compare labels and speeds without advancing a physical state or selecting its next collision. Polynomial DAG evaluation concerns integer expressions, not signal trajectories.

The source manifest's 13 listed hashes and byte lengths match. All four original-source bindings match the preserved copies. Core evidence records the full 17-object source tree, including directories, before and after checking. Its object set, bytes, modes, and nanosecond modification/change timestamps are unchanged; the four historical original files likewise retain the recorded bytes and metadata. Access-time invariance is not claimed. The checkers write only outside the frozen source directory.

## 2. Exact mathematical statement and dependencies

The approved theorem is a **local complete-word realization criterion in the original full stationary-marker section**. For rational N, the exact necessary and sufficient conditions are

    det N != 0, and C intersect N^(-1) C is nonempty.

Here C consists of the three strict physical gap inequalities in z=(D,xi,eta); their sum is D, so D>0 is automatic. The model has five live outgoing strands, binary 2-to-2 events, distinct incoming and outgoing speeds, positive inter-event flights, no simultaneous remote events, and full positional section coordinates modulo common translation. The theorem is not about a projection that discards hidden continuous coordinates.

The inherited fixed-center interface is precisely: every rational matrix [[s,b],[0,A]], with s>0 and det A nonzero, has a nonempty positive-duration five-signal complete word, exact finite rational homogeneous guards strict at e0, and literal section/phase closure. Its source is `dependencies/fixed_center_PROOF.md` §§2–6, bound to SHA-256 `502e90e091eabc0a6c8eb6092e73f4407ae84f143d337be8a4a633a3f85a7c47`. The preserved positive-planar and invertibility proofs support that interface, including signed planar factors and the odd seven-event primitive. Their algebraic/chronology interfaces were inspected. This review does not re-certify the unrelated planar spectral-classification corollary cited by the positive-planar dependency.

For necessity, each flight is an oblique linear section map transverse to the departing and arriving collision faces. The explicit inverse in the invertibility dependency removes the ambient projection's apparent kernel. Collision positional identifications are invertible, and common translations are preserved. Thus the complete three-coordinate return is invertible. Agreement with N on a full-dimensional open set forces that very matrix to be invertible. An admissible input and its literal output both lie in C, proving the other necessary condition. No global reversibility assumption is used.

## 3. Ten-event translation: all flights and contacts

Source: main `PROOF.md` §3; positive-planar dependency §§2.1–2.4.

For e<1 put u=t/(1-e), t'=t+eD, h=e/(2-e). Under 0<t<s<D and 0<t'<s, the two margin identities

    1+h=2/(2-e),    1-h=2(1-e)/(2-e)

are positive. Hence the moving target speed lies strictly between -1 and 1. The independent checker compares every messenger and target displacement against its declared speed times its declared flight duration. Its complete flight list is

    t, t, u, u, u, s-u, D-s, D-s, s-t', t'.

The first four contacts are target launch, anchor bounce, target restoration, anchor bounce. The last six are target launch, spectator crossing, far-reflector bounce, spectator crossing, target restoration, anchor bounce. There are exactly two spectator contacts in the six-event homothety part. Both target restoration equations hold identically.

The internal endpoint u lies between t and t': u-t=e t/(1-e) and t'-u=e(D-t')/(1-e) have the same sign as e. Thus u is strictly between 0 and s without adding an independent guard. Every displayed flight is positive. In either moving stage the target remains in the open interval (0,s), so it cannot touch an anchor, spectator, or reflector. The messenger separates from the target on departure and has nonzero relative speed on return. Its outward and inward passages through s are explicitly listed. There is no second moving marker and no omitted spectator. These facts establish the whole chronology, not just endpoint algebra.

Necessity is a first-obstruction statement. Starting with a valid section, a failed required endpoint forces a target-neighbor contact, a simultaneous contact, or a collapsed/reordered prescribed interval by the proposed restoration. If the initial scale is already obstructed, the argument stops there; it never treats a formula beyond an earlier wrong collision as an actual trajectory. This validates the exact primitive guard, including strict boundary exclusion.

The duration is 2(t+u)+2D and lies strictly between 2D and 6D. At e=0 the moving labels have speed zero, but their actual partners have speeds ±1; all ten timed events remain valid. Reflecting the geometry negates physical velocities and leaves distance-coordinate times and inequalities unchanged.

## 4. Arbitrary physical shape translation and exact guards

Source: main `PROOF.md` §4.

For rational p,q inside the normalized triangle, let m be the least of their six endpoint gaps, M=max(|q1-p1|,|q2-p2|), n=max(1,ceil(2M/m)), and delta=(q-p)/n. Convexity gives all completed-step gaps at least m. Since |delta_j|<=m/2 and m<=1/3, each delta_j has magnitude at most 1/6. The X-first intermediate corner changes its three gaps by delta1,-delta1,0; all remain at least m/2>0.

Each step has these genuine timed blocks:

1. Translate X from L by delta1 D: 10 events
2. Cross X and Y and reflect at R: 3 events
3. Translate Y from R using distance parameter -delta2: 10 events
4. Cross Y and X and reflect at L: 3 events

The reflected sign is correct: D-y changes by -delta2 D, so y changes by +delta2 D. The temporary physical Y speed is delta2/(2+delta2). There are exactly 26 events, four temporary marker labels, and an outgoing-right return at L. The supplied 26-rule declaration has 26 distinct messenger input phases, the correct next-phase speed including wraparound, one launch/restoration pair for each temporary, and restored stationary roles. All rules are binary and both sides have distinct speeds.

The exact guard list consists of all three gap rows at every completed checkpoint k delta, k=0,...,n, and every X-first corner ((k+1)delta1,k delta2), k=0,...,n-1. This is 6n+3 supplied scalar rows. Applying the primitive's exact guard to the first failed checkpoint proves necessity; induction proves sufficiency. Initial/final order alone is insufficient in general, and the proof does not discard the corner rows. Redundancy is harmless.

The product is T_delta^n=T_(q-p). All rows are strict at (1,p), so the cone has nonempty full-dimensional interior. Counts 26n events, 4n temporaries, 26n messenger phases and 30n+4 total meta-signals are correct for this particular construction. They are not minima. The p=q convention n=1 gives a genuine 26-event identity.

The step duration is exactly

    6D + 2(1+1/(1-delta1))x
       + 2(1+1/(1+delta2))(D-y),

and 6D<T_step<14D. The first X move leaves the incoming Y distance unchanged. The 36 supplied endpoint/corner fixtures were recomputed independently, including each hidden scale endpoint and all counts. They support, rather than replace, the all-parameter convexity proof.

## 5. Left/right normalization, original coordinates, and literal phases

Sources: main `PROOF.md` §§5–5.1.

Nonempty C intersect N^(-1)C is open and rationally defined, so it contains a rational vector. Its first coordinate is positive; normalize to e_p=(1,p). Write Ne_p=s(1,q), with s>0 and p,q rational interior shapes. Then

    N0=T_(-q) N T_p=[[s,b],[0,B-qb]],
    det(B-qb)=det N/s.

The audit verifies this identity in all nine formal entries of N and both formal components of p. It also verifies the actual chronological product

    T_q N0 T_(-p)=N.

Consequently the physical prefix p-to-zero, inherited middle compiler, and physical suffix zero-to-q realize N itself. This is left/right normalization, not a conjugacy or merely a new encoding. No rational eigenray of N is required.

Every middle compiler guard is retained after pullback. The exact total list is G_minus, G0 T_(-p), and G_plus N0 T_(-p). At e_p the respective entrance vectors are e_p, e0 and s e0; homogeneity and positivity make every row strict. The first input ordering rows place the D=1 chamber inside the bounded triangle. It is therefore a nonempty bounded open rational polygon, and its exactness follows by the first failed block after a valid prefix. Equality to the entire endpoint compatibility region is neither proved nor claimed.

Fresh messenger phases isolate every messenger-involving rule. At the inherited orientation-reversing primitive's single marker-only contact the messenger phase remains unchanged; a fresh temporary marker label isolates that rule. Only the final outgoing phase is identified with the entire macro's initial phase. No zero-time phase reset occurs. Identity completion on other admissible collision sets is finite, deterministic and number-preserving. It does not make an extra collision part of this word, and it does not assert global rule injectivity.

The composite counts m=26(n_minus+n_plus)+m0, t=4(n_minus+n_plus)+t0, and g=(6n_minus+3)+g0+(6n_plus+3) are correct. With r marker-only events, m-r messenger labels and m-r+t+4 total labels are available. The two translations have determinant one and even length, so inherited collision parity sign(det N)=(-1)^m is consistent.

## 6. Exact rational decision algorithm

Source: main `PROOF.md` §6.

H and H inverse are mutually inverse and Hz=(x,y-x,D-y). Thus the endpoint condition is g>0 and Kg>0 for K=HNH inverse. Normalizing sum g_i=1 is legitimate by positive homogeneity. The LP in (g1,g2,g3,epsilon), with both g_i and (Kg)_i at least epsilon and 0<=epsilon<=1, has a positive optimum exactly in the strictly compatible case.

Any feasible point lies in the compact simplex times [0,1], so an optimum exists. A nonempty bounded polytope has a vertex even if its affine dimension is smaller than three. At a vertex, three independent active inequalities together with sum g_i=1 determine the four variables; hence enumerating all 56 triples is sufficient. Infeasible and zero-optimum cases are correctly distinguished. The audit uses independent Fraction Gauss-Jordan elimination, a reversed inequality convention, and exact rational comparisons; no numerical tolerance or floating optimization is involved.

All seven supplied LP fixtures, determinants, stored vertices and optima agree. Four additional zero, rank-deficient, negative and small-rational-scale fixtures pass. A positive vertex yields rational p,q,s by the displayed formulas. Fixed matrix dimension and a fixed number of constraints make bit complexity polynomial in rational input length. This is a decision bound; large reciprocal margins can make the explicitly selected physical word exponentially large in binary input length.

## 7. Worked example and escape obstruction

Sources: main `PROOF.md` §§7,9.

The positive gap matrix [[1,1,1],[1,2,1],[1,1,3]] has determinant two and characteristic polynomial t^3-6t^2+8t-2. All four possible rational roots ±1,±2 fail. A rational eigenray of a rational matrix would give a rational eigenvalue by taking a ratio at a nonzero coordinate, so no such ray exists. The displayed centered conjugate and normalized middle matrix are exact; its lower block determinant is 1/2.

Choosing p=0 gives s=4 and q=(-1/12,-1/12). The suffix needs n=1. At entrance D=4 it moves X from 4/3 to 1, then Y from 8/3 to 7/3, keeping strict order. Its final normalized gaps are 1/4,1/3,5/12. The optional initial identity can be omitted because the middle word is already nonempty. This genuinely covers the former rational-eigenray obstruction.

For K_escape=[[1,0,0],[0,1,0],[-1,0,1]], determinant is one and local compatibility holds when g3>g1>0 and g2>0. Since (K_escape-I)^2=0, its nth algebraic iterate has third gap g3-n g1. Every positive input eventually leaves the positive cone. Therefore no infinitely valid repetition of any exact full return with this matrix can exist. This is an endpoint obstruction, not an assertion of physical evolution after the first failed word.

## 8. Native positive-integer certificate and literal DAGs

Sources: main `PROOF.md` §§8–8.2; both complete certificate JSONs; separate `certificate_audit/REVIEW.md`.

There are exactly eight positive integer witnesses g1,g2,g3,h1,h2,h3,b,d and five residuals:

    (Kg)_i-h_i for i=1,2,3;
    det K-(2b-3)d;
    (b-1)(b-2).

The sum of their squares vanishes exactly when all five vanish. The gate forces b=1 or 2, and d>0 then enforces det K=-d or +d. The first three force Kg=h>0 with g>0. Conversely, strict real compatibility has a rational point by openness; clear denominators to obtain positive integer g,h, then choose b by determinant sign and d=|det K|. This proves the arithmetic equivalence for every integer K. A positive denominator q changes neither condition; q>0 is an external domain requirement, not an inequality enforced by the polynomial.

The **joint total degree in matrix inputs and witnesses** is exactly six. The determinant-squared monomial k11^2 k22^2 k33^2 has coefficient one, so cancellation cannot lower it. Specializing K first is a different degree question. The signed expanded polynomial has 71 nonzero monomials; its positive-difference substitution has 1,166. These expansion counts are independent supporting observations, not required resources.

Both literal graphs were schema/topology checked, and every node contributes to the output. Every residual and whole output was compared against a separately constructed permutation-determinant polynomial. The signed graph has nine signed external matrix leaves, eight positive witnesses, constants 1,2,3, and exactly 26 multiplications + 11 additions + 11 subtractions = **48 operations**. The positive graph has eighteen positive external matrix leaves and the same eight witnesses; nine actual entry differences precede a node-renamed copy of the same graph, giving 26 + 11 + 20 = **57 operations**. Intermediate gate values are unrestricted integers. The expression nodes are not extra Diophantine witnesses or physical events. Both degree-six claims hold identically.

All four supplied native fixtures pass both encodings, positive scaled fibers remain valid, and deliberate h, d and gate perturbations are rejected. Scaling g,h together gives infinitely many distinct witness tuples, so the representation is not finite-fold.

For centered numerator M, S=3H and B=3H inverse satisfy SB=BS=9I, det S=det B=27, and det(SMB)=729 det M. Thus K_tilde/(9q)=H(M/q)H inverse. The centered formula is the exact substitution K=SMB, with no hidden witnesses or aliases; it retains eight witnesses, five residuals, and joint degree six. Its leading example coefficient is 729^2. The native 48/57 counts explicitly exclude this conversion. No centered operation count or optimality claim is justified or made.

## 9. Repetition and conditional clock theorem

Source: main `PROOF.md` §9.

Literal phase closure yields infinite validity exactly when G N^n z>0 for every n>=0, for this actual constructed word and its full guard list. The local theorem does not ensure this set is nonempty or invariant under a larger chosen chamber.

Retaining the initial physical translation supplies duration greater than 6D. Every fixed-word event time and position is a rational homogeneous linear form in the incoming coordinates, since speed-dependent denominators are fixed constants. Finitely many such forms are bounded on the closed normalized input triangle. The macro duration therefore satisfies c1 D<=ell z<=c2 D with c1=6 available. Omitting the initial identity would require separately retaining a suitable lower-bound argument; the stated clock convention does retain it.

On an infinitely valid orbit, ordering bounds |xi_n| and |eta_n| by constants times D_n. Thus summable D_n implies N^n z tends to zero. Conversely, if N^n z tends to zero, every eigenvalue active in the cyclic space span(z,Nz,N^2z) has modulus below one; polynomial-times-geometric Jordan bounds make its norm summable. The duration comparison proves the stated Zeno equivalences. For rational z the cyclic space has a rational basis; I-N is invertible on that restricted space and the accumulated time is rational. An ambient inverse may fail because of unused unit modes. None of this gives a general infinite-validity decision procedure or continuation through accumulation.

## 10. Primary-source positioning

The three main primary references were retrieved and relevant passages checked directly. These are bounded precedent checks, not a novelty search.

- Becker et al., *Abstract Geometrical Computation 10*, §2, Definitions 1–2, manuscript pages 4–5: finite label-dependent speeds, distinct-speed incoming/outgoing collision sets, determinism, and the least positive meeting-time convention agree with the model. Equal speeds on different unrelated labels are allowed. [Primary manuscript](https://arxiv.org/pdf/1804.09018)
- Alishah, Duarte and Peixe, *Asymptotic Poincare Maps along the edges of Polytopes*, §5, equation (5.2), Proposition 5.4 and Definition 5.7: oblique constant-flow section maps, their strict itinerary sectors and compositions are present. This supports the geometric precedent, not this five-live-signal compiler. [Primary manuscript](https://arxiv.org/pdf/1411.6227)
- Durand-Lose, *Abstract geometrical computation and the linear Blum, Shub and Smale model*, §§3.1–3.2: scale-relative distance registers and arithmetic constructions are explicit. That encoding has additional registers/signals and does not prove the packet's full-section population-preserving criterion. [Author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2007_CiE.pdf)

## 11. Required limitations and publication advice

No theorem, chronology, guard, phase, normalization, decision, example, witness count, degree, or native-DAG correction is required. Preserve these qualifications:

- Local full-dimensional one-pass realization on the original section, not all-cone realization
- Exact guards of the selected word, not an arbitrary prescribed polygon
- Matrix-dependent finite machine, not one unchanged universal rule table
- Polynomial endpoint decision, not polynomial-size physical compilation
- Infinite validity required for the clock theorem; it may fail for every input
- Eight positive witnesses; signed versus positive external input leaves counted separately
- Joint total degree six; literal 48/57 counts only for native gap inputs
- No finite-fold, optimality, novelty, priority, Turing-completeness, global reversibility, or post-accumulation continuation claim

One optional wording improvement: §3's phrase about the “six listed crossings” should be read as the six homothety events, of which exactly two are spectator crossings. The displayed chronology and event counts are correct; this is editorial precision, not a mathematical defect.

## 12. Reproduction

The core checker requires Python and the installed SymPy 1.14.0. It imports no source-packet module. Run it against the source packet with a distinct new output directory:

    python independent_static_audit.py --source SOURCE_PACKET --output NEW_OUTPUT

This mode also authenticates the historical original files at paths declared in the source manifest. The audited run has 840 assertions. For a relocated evidence archive where only the frozen source packet is available:

    python independent_static_audit.py --source SOURCE_PACKET --output NEW_OUTPUT --archived-source

Archive mode still verifies all source-manifest hashes and dependency-copy bindings, and performs the same mathematical checks. It explicitly skips opening historical absolute paths; its 832 assertions passed. It does not falsely claim fresh metadata verification of absent originals. Both modes reject output inside or above the frozen source directory.

The certificate checker uses only the Python standard library and accepts its own source/output arguments; see `certificate_audit/REVIEW.md`. The initial core 836-assertion run is preserved in `initial-run/` with its matching checker. The final core adds four explicit dependency-copy authentication assertions and portable archive mode, without changing the mathematics.
