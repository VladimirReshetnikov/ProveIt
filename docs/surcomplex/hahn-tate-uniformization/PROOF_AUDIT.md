# Proof and novelty audit

This audit covers the merged report built from three manuscripts: source 01
(the original Hahn–Tate report, pin `a3124af`), source 02 (finite positive
generation and multiscale theta series, pin `a3124af`) and source 03 (Tate
uniformization over surcomplex numbers by formal charts, pin `0097304`).
Theorem numbers refer to the built `article.pdf`. Source 03's own proof-status
file is kept unchanged as `03-tate-uniformization-PROOF_STATUS.md`.

## Candidate-original package

**Part I.** The central result is the conjunction of an exact maximal literal
Hahn-series domain for the raw bilateral families with surjective elliptic
uniformization on that domain, at arbitrary valuation rank (Theorem 1.2). It
is proved twice. The first route proves the additional support and lifting
steps and uses the established complete rank-one Tate theorem as an explicitly
identified classical input. The second route (Section 8) uses no rank-one
completion and holds over any coefficient field of characteristic zero
(Theorem 8.13); its inputs are Tate's universal formal identities and Tate's
generic-pair lemma. The support-monoid equality and the exact valuation
identities of Section 9 are further candidates.

**What is not new.** The period-bounded quotient `U_q/q^Z` and its value
sequence (Theorem 10.3) have a precedent in the logarithmic Picard theory of
Molcho and Wise, *The logarithmic Picard group and its tropicalization*,
arXiv:1807.11364 v5: boundedness in Definition 2.1.3.1, bounded monodromy in
Definition 3.5.5, the tropical Jacobian in Definition 3.6.1, and the Tate
curve in Section 5.1 with (5.1.3)–(5.1.4). For an ordered value group and one
length their bounded subgroup is `H_α`. Neither bounded monodromy nor the
abstract shape of the quotient is claimed. Source 01 did not know this
precedent; source 03 found it. No functorial comparison with the logarithmic
Tate quotient is proved, and that comparison is the most important remaining
priority check. The extension obstruction (Theorem 10.5) is a consequence, not
an independent deep discovery.

**Part II.** Theorem 15.2 answers Question 11.14 of Amini and Nicolussi,
*Higher rank inner products, Voronoi tilings and metric degenerations of tori*,
Annales Henri Lebesgue 8 (2025), 1109–1188 (Section 11.5.3, page 1181),
affirmatively and constructively, in its published formulation. The question
belongs to higher-rank lattice geometry, not to surreal analysis. The further
candidates are the exact flag criterion (Theorem 16.3), the ordinal support law
(Theorem 17.2), the unit-robust theta domain (Theorem 18.1), the finite minimum
certificates (Theorems 19.1, 19.3) and zero lifting (Theorem 20.2).

"Not identified in a targeted search" is the novelty status of every candidate.
It is not a guarantee of absence from the literature, a peer-review certificate,
or, outside Question 11.14, a claimed solution of a previously named open
problem. The Question 11.14 claim is not a claim that nobody has answered it
since publication.

## Proof dependency map

**First route (source 01).**
1. **Classical Hahn–Neumann/Higman calculus.** Positive supports generate well-ordered monoids with finite decompositions. The article recalls a proof using Higman's lemma and cites the classical sources (Lemma 2.1).
2. **Exact domain.** The theta leading exponents are n(n−1)alpha/2 + n beta. The two Tate coordinate families have their own explicit leading-exponent obstructions. The support proofs are separate (Theorems 3.1, 4.1).
3. **Coarse formal evaluation.** Coefficient series in K_H may have arbitrarily negative fine valuations. Positive quotient values of the substituted variables give finite contributions in each quotient fiber. This is proved in Lemma 5.1.
4. **Rank-one reduction.** K_H is complete for the rank-one coarsening obtained by quotienting out values infinitesimal relative to alpha. A direct Cauchy-sequence proof is provided (Lemma 5.3).
5. **Classical Tate theorem.** Surjectivity and the group law over complete real-valued non-Archimedean fields are imported from Tate, not reproved or claimed as new (Theorem 6.1).
6. **Taylor/Hahn agreement.** Lemma 6.3 proves the joint-family interchange: quotient Neumann finiteness controls Taylor degree, and cofinality inside H controls the rational tail index. This is a particularly important independent-review target.
7. **All-rank group law.** Classical local identities are evaluated through the coarse formal homomorphism in regular projective charts. The argument does not apply a singular affine chord formula at a zero denominator.
8. **Surjectivity and kernel.** Good coarse reduction plus the invertible formal parameter z = -x/y gives every infinitesimal lift and makes the kernel exactly q^Z.
9. **Torsion arithmetic.** A binomial root removes the unit part of q. Finite exponent-coset decomposition gives the extension degree. A character-Galois stabilizer calculation proves that one specified torsion point generates it.
10. **Surcomplex transport.** Every instance lies in a set-sized normal-form workspace; strong functoriality makes the result independent of its enlargement.

Steps 3–8 remain load-bearing for the coarse reduction diagram (Corollary 7.2), the reduction compatibility and the coarse identity fibre (Proposition 7.1), which only the first route proves. For Theorem 1.2 itself they are bypassed by the second route.

**Second route (source 03), over any field k of characteristic 0.**
11. **Finite-variable specialization and the formal implicit function.** Lemma 2.1 holds over any k; Lemma 2.2 gives formal inverses, integrality, and uniqueness among actual infinitesimal inputs.
12. **Universal identities.** Tate's curve equation and cleared secant identities are universal formal identities, imported from Tate's proof (Section 8.2), not inferred from computation.
13. **Hahn specialization on the wide annulus.** Proposition 8.1 proves joint summability before regrouping on `−α < v(u) < α`, so the curve and secant identities specialize; normalizing one argument into `[0, α)` and the other into `(−α, 0]` keeps `u`, `u'`, `uu'` in the wide annulus. A review target.
14. **Node chart.** The integral chart T has unimodular linear part with `𝐋^{-1} = 𝐋`, an integral inverse, and `𝓕 = (Q − 𝒬)·unit` because `∂𝓕/∂Q = 1` at the origin (Theorem 8.3). Nodal points are inverted by Theorem 8.5.
15. **Other charts.** Smooth-residue points (Lemma 8.6, Proposition 8.7) and points at infinity (Lemma 8.8, obtained without dividing in Γ; Proposition 8.9). The three charts exhaust all points (Theorem 8.10). A review target.
16. **Group law and kernel.** Secant identities for distinct x-coordinates, Tate's generic-pair lemma (Lemma 8.11, proved), and infiniteness of the image (Theorem 8.12). Theorem 8.13 assembles the second route.
17. **Refinements.** Support monoids (Theorem 9.1) from support control applied to the chart and its inverse; the isometry lemma (Lemma 9.3) from formal difference factorization; the two-period comparison and its corollaries (9.5–9.7); the fine residue sequence and the obstruction (Proposition 10.4, Theorem 10.5); real and surcomplex transfer (Corollary 13.2).

**Part II (source 02).** Coefficients in C; Γ divisible where halves are used; monomial periods.
18. **Positive generation.** Acute rational cones in the positive-definite quotient (Lemma 15.3, the rank-one ingredient described by Amini–Nicolussi), bounded allocation (Lemma 15.4), a uniform shift dominating mixed terms, which is where the global radical condition enters (Lemma 15.5), and induction on active levels. Non-full lattices by restriction to the real span (Remark 15.6). A review target.
19. **Flag criterion.** One-level criterion (Lemma 16.2, using Lemma 16.1), then induction over lexicographic levels; testing every coset, not only the one through zero, forces the global radical condition (Theorem 16.3). A review target.
20. **Ordinal law.** Hessenberg interleaving bound (Lemma 17.1) and induction on active depth (Theorem 17.2).
21. **Theta domain.** Leading terms give necessity; the support monoid of the unit tails gives sufficiency (Theorem 18.1).
22. **Certificates.** The energy decomposition over a positively generating set (Theorem 19.1); the midpoint parity bound and orthogonal decomposition of zero-cost moves (Theorem 19.3).
23. **Zero lifting.** A formal implicit theorem with infinitely many monomial parameters, specialized by Neumann's lemma (Lemma 20.1), applied to the gap-graded theta series (Theorem 20.2).

## Classical material not claimed as new

Tate's original rank-one uniformization; Tate's universal curve and secant identities and his Lemma 1; the theta triple product; the Tate discriminant and modular invariant; the inverse j-series as a formal series; standard elliptic n-torsion and classification by j; algebraic closedness of a divisible Hahn field over C; the Kummer description of Tate torsion; formal models of the nodal Tate degeneration (Conrad); Neumann's lemma, Gonshor normal forms and Berarducci–Mantova's summability conventions; bounded monodromy and the logarithmic Tate curve (Molcho–Wise); higher-rank inner products, admissible lattices, Definition 11.10, Lemma 11.11 and the rank-one acute-cone argument (Amini–Nicolussi); rank-one non-Archimedean and tropical theta functions (Foster–Rabinoff–Shokrieh–Soto); convergent higher-rank Hahn subrings (Joswig–Smith); the midpoint/Delaunay parity argument; initial forms and the formal implicit theorem.

The torsion contribution is an exact arbitrary-exponent-group formulation within the support-controlled all-rank theory, not a new discovery that Tate torsion comes from roots of q. Source 03's torsion consistency check (C, divisible Γ) is subsumed by Theorem 12.2.

## Essential qualifications

From source 01:
- Maximality concerns the *specified bilateral families and strong Hahn summability*, not every imaginable extension or resummation.
- Nondivisible exponent groups are permitted for E_q, but arbitrary curves with the same j can be twists over such a field.
- The negative-j regime is covered. A uniformization of every elliptic curve in the good-reduction regime is not asserted.
- The value-circle exact sequence is algebraic and circularly ordered. No unrestricted real-metric Berkovich skeleton theorem is claimed at higher rank.
- Differentiation is with respect to an external variable. It is not the Berarducci–Mantova derivation on surreal scalars.
- Strong sums need not be limits of their partial sums in the full valuation topology.
- The computations are finite consistency checks, not machine-checked proofs of the paper.

From source 03:
- The kernel obstruction does not exclude every noncanonical extension; it excludes one that keeps both the canonical values on U_q and the kernel q^Z.
- The value quotient is not identified with a real circle without additional hypotheses.
- "Uniformization" is a group parametrization by Hahn sums and formal charts: no covering space, lifted contours, fine-topology convergence of partial sums, global surcomplex logarithm, or exponential at infinite imaginary arguments.
- No classification of all elliptic curves over No[i] (source 01 adds v(j) < 0 only).
- No algorithm on all surreals: `|γ| ≤ Nα` is only semidecidable without a convex-subgroup oracle; degree truncation need not reach a requested cutoff at higher rank.
- The Section 9 distances are model-dependent; calling them canonical would be an unsupported strengthening.
- The characteristic-0 generality is confined to Theorem 1.2 (Theorem 8.13), Sections 8–9 and 10.3, and Corollary 13.2. Torsion, j-recovery and classification are stated over C; Corollary 11.2 also needs divisibility.

From source 02:
- The Question 11.14 answer is pinned to the published formulation.
- The size bound for a positively generating set is an existence bound; there is no uniform bound on descent steps; the observed descent length 35 is experimental; no algorithm for arbitrary real constants is claimed.
- No Tate or abelian-variety uniformization in several variables, no global surcomplex exponential, no class-sized convergence, no fine-topological holomorphy.
- Singular initial zeros are not treated.
- Corollary 21.5 accords with, but does not reprove or strengthen, the collection's all-scale entire-function restrictions.
- Part II's hypotheses (monomial periods, divisible Γ, coefficients in C) are not merged with Part I's; Corollary 18.3 recovers Theorem 3.1 only for a monomial q and divisible Γ.

No proof has been independently refereed. No Lean formalization exists or is claimed.

## Open question status

"Higher-dimensional totally degenerate abelian varieties" (Section 23) remains open. Part II answers its theta-summability half for monomial periods and divisible Γ. Everything else in it (tails in the periods, nondivisible Γ, the coordinate maps, group structure, surjectivity onto abelian-variety points, singular zeros, theta line bundles) is open. "Functions outside the literal Hahn domain" is now partly answered by Theorem 10.5 and otherwise open.

## Recorded verification

Three independent finite suites, all rerun on copies on Python 3.14.4 when the report was assembled:

- `code/check_identities.py` (source 01; SymPy 1.14.0): PASS, reproduced `data/verification.json` exactly.
- `code/03-tate-uniformization-verify.py --degree 12` (source 03; standard library): 8 identities, 728 exact coefficient equalities, all pass; identical to `data/03-tate-uniformization-verification.json` apart from the informational runtime.
- `code/02-multiscale-theta-verify.py` (source 02; standard library): ALL CHECKS PASSED, identical to `data/02-multiscale-theta-verification.json` (5,555 allocations, 1,681 shear decompositions, 441 linear-term cases, 12 Pell witnesses, zero-row through degree 8).

`check_identities.py` and `02-multiscale-theta-verify.py` both write `data/verification.json`, and the node-chart program writes wherever `--output` points, so all three must be run on a copy (see `README.md`). No floating-point numerical test is used, and no Lean compilation or independent human peer review is claimed.
