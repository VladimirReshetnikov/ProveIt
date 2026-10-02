# Independent audit of the all-matroid extension

Approved for the submitted scope: every finite matroid M on E∪{A,B} with E spanning its rank. Source ALL_MATROIDS_EXTENSION.md is pinned at SHA-256 2bdfc8c18e350df957e1fa381d80f00e5d07fc4dec55e9535cecfc4fc0309073. The previously approved low-rank derivative proof is unchanged.

## Primary sources checked directly

Bonin and Kung, [Semidirect sums of matroids](https://arxiv.org/pdf/1210.0626), Section2, gives the union independent-set definition and rank formula(2.1). Lemma2.4 gives the asserted loop-factor contraction rule. Section3 defines repeated principal extensions and Lemma3.1, formula(3.2), gives precisely the stated free-on-flat rank formula, for arbitrary matroids. The rank-zero-flat case is included. Edmonds and Fulkerson, [Transversals and Matroid Partition](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn3p147_A1b.pdf), Section4, Theorem1c, is correctly cited as the foundational independent-set partition theorem. No representability hypothesis occurs in these inputs.

## Principal-line seed

Applying the rank formula to old subsets of sizes q−1 and q−2 gives exactly the one-new-element Boolean union family and the two-new-element V family. Applying it to an old subset together with A or B gives the same V family for a mixed pair. The distinguished and new elements all lie in a flat of rank at most two, so no basis can contain three. This includes loops and parallel distinguished elements. The resulting basis polynomial has exactly the displayed coefficients; specializing m new variables to sU/m yields the half-factor in the quadratic term. Matroid-basis Lorentzianity and closedness therefore supply the required seed without a matrix representation.

## Support through matroid union

The two factors have ranks q and |Y|. An old basis together with all new dummies supplies an independent union set attaining their rank sum. Every union basis has a disjoint full-rank partition: its size equals that rank sum, so neither factor can lose rank or share an element. Old elements are forced into the first factor and dummies into the second; only A,B may switch factors.

Omitting r dummies therefore forces exactly r distinguished elements into the transversal factor. Its private dummy incidences force those distinguished elements to match the omitted heads. The cases r=0,1,2 are exactly the four listed endpoint allocations, and r>2 is impossible. Multiple admissible partitions of one union basis are not multiple bases. In particular a common one-head omission gives the Boolean union U, with no coefficient two on its intersection.

The weighted basis specialization consequently equals z^(|Y|−2)F_M. Positive population weights allow the dummy substitutions; zero weights follow in the explicit coefficient polynomial. The old-basis term remains nonzero. Support translation yields M-convexity only, with no Lorentzian monomial-division claim.

The old-element contraction argument is purely matroidal: subset restriction/deletion commutes with all five families, including Boolean union. The remaining old set spans the contracted rank. Thus every previously approved q0–q4 derivative case and the higher-rank induction apply unchanged. Representation is fully removed at the submitted spanning-old-set scope. Removing that remaining hypothesis is a separate prospective addendum, not part of this approval.

## Independent exact corroboration

check.py uses rank oracles, not a representation or producer code. It first verifies10,060 symmetric basis exchanges in seven input matroids, including Fano, a rank-four sparse-paving family, uniform matroids and a partition matroid with a loop. Across84 distinguished pairs with spanning old sets it verifies84 principal-extension basis identities,840 union rank-formula polynomial identities over82,331 proposed union bases, and365 old-nonloop contraction checks. Zero population weights are included. These tests corroborate the ordinary constructions; they are not a theorem premise.

The program is standard-library-only, supports portable source/output arguments and rejects optimized Python. No physical-role collision, joint Y-activity Lorentzianity, general rank-six graph theorem or new artifact release is inferred.
