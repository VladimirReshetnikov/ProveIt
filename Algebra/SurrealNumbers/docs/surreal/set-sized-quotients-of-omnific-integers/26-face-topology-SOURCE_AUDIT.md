# Source and novelty audit

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Commit: `7b256e0792df7718995b816ad12a77bf56731f8f`

GitHub API commit timestamp: `2026-09-24T00:21:12Z`.
The manuscript carries the local session date, 23 September 2026; its source identity is the SHA, not that date label.

The connector was used to read repository content. The root README was initially read from the moving main branch; the comparison material was subsequently read at the explicit snapshot. No local repository changes or pushes were made.

### Inspected material

- Root `README.md` and `docs/README.md`: scope, research catalog, and formalization boundary.
- `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`: prior-source reconciliation and reported scope.
- The corresponding `article.tex`, source lines 1–210: abstract and preliminary provenance.
- The same `article.tex`, source lines 3300–3520: coordinate-orthant resolution, Boolean Tor formula, exact augmentation flat dimensions, and related statements.
- `docs/surreal/omnific-preserving-automorphisms/README.md`, a selected later range: consulted while choosing the research direction, not used in the proofs.
- GitHub API commit metadata: exact pin and latest recorded formalization change.

This was a targeted comparison, not a full audit of all 61 reports and all companion manuscripts. Empty connector search results were not treated as proof that a topic is absent.

### Directly compared labels

- `osq:hd:thm:resolution`
- `osq:hd:cor:arithmeticTor`
- `osq:hd:prop:etale`
- `osq:hd:thm:boolean`
- `osq:hd:cor:fd`

The report abstract and guide also advertise the later exact projective dimension of the coordinate-orthant augmentation. That is credited, not imported as a lemma. The present article proves only the general interval max(2,h) <= pd <= h+1, except when h=1.

## Primary literature

1. Nathan Geist and Ezra Miller, *Global dimension of real-exponent polynomial rings*, Algebra & Number Theory 17 (2023), no. 10, 1779–1788. DOI: 10.2140/ant.2023.17.1779; arXiv:2109.04924. The primary text was inspected, including the dense-subgroup hypotheses in Section 4. These are orthant results; the broader all-module theorem is not reproved or claimed here.
2. Dave Bayer and Bernd Sturmfels, *Cellular resolutions of monomial modules*, J. Reine Angew. Math. 502 (1998), 123–140; arXiv:alg-geom/9711023. The author-hosted primary text and publication record were inspected. Cellular incidence resolutions are classical antecedents, not a novelty claim.
3. Vesselin Gasharov, Irena Peeva, and Volkmar Welker, *The lcm-lattice in monomial resolutions*, Math. Res. Lett. 6 (1999), 521–532. DOI: 10.4310/MRL.1999.v6.n5.a5. Publisher information and the primary indexed text were consulted. The interval-homology method is credited directly.
4. Ezra Miller, *Essential graded algebra over polynomial rings with real exponents*, Advances in Mathematics 485 (2026), article 110682. DOI: 10.1016/j.aim.2025.110682; arXiv:2008.03819v2. The primary PDF was inspected selectively, including its introduction, flatness references, and discussion of presentations and resolutions. This is related broader work on real polyhedral groups; the audit does not claim an exhaustive theorem-by-theorem comparison of the 85-page text.
5. The Stacks Project, Tags 00H9 and 00HK: flat modules and the finite equational criterion. Used for standard terminology and the nonflatness certificate.
6. Mathlib documentation, `Mathlib.RingTheory.Flat.EquationalCriterion`: consulted only as a concrete formalization target. No Lean verification was run for this article.
7. Conway and Gonshor: standard normal-form and omnific-ring foundations; publication metadata checked against primary or publisher records. The requested Wikipedia article was also consulted as orientation, not as a technical premise.

## Proposed contribution and comparison boundary

The principal candidate-original package is:

- ordinary flat dimension of radical coefficient-full monomial quotients of arbitrary rational polyhedral arithmetic cores;
- explicit cap modules isolating each face label and proving sharpness;
- the exact disjoint-face formula for face-prime quotients;
- the simpliciality criterion and arbitrarily large codimension-one examples;
- the finite relation obstruction to flatness of the natural total-order/omnific enlargement.

The article also supplies an arithmetic-module dichotomy over PID constant rings and a marked face-lattice reconstruction. Simple fraction-field and scalar-quotient observations are presented as comparisons rather than advertised as independent breakthroughs.

The mathematical arguments do not rely on an unrefereed repository theorem as a premise: the relevant algebra is reproved in the article. The foundational specifically surreal premise is standard Conway monomial algebra.

Priority is not certified. The search did not establish that no equivalent formulation exists in the wider literature. The manuscript does not claim to solve a named general open conjecture on all surreal numbers. Its “further research questions” are proposed next problems, not assertions that every question has a newly established global open status.

## Verification boundary

The Python program checks finite rational incidence complexes and geometric cap inequalities. It does not prove statements about all cones, filtered limits of infinite modules, proper classes, or publication novelty. The prose proof audit and finite program are not independent external refereeing.
