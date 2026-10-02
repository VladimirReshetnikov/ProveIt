# Independent audit: the two-by-two role-cover criterion

Approved: let D be a finite loopless directed relation whose bipartite tail/head role graph has a vertex cover with at most two tail roles and at most two head roles. For arbitrary nonnegative independent role activities, its signed physical monomer polynomial is real stable; its gamma polynomial has only negative real roots and is ULC at its actual surviving degree. The physical sets represented by the two cover parts may overlap.

Final proof `../TWO_BY_TWO_ROLE_COVER_THEOREM.md` is pinned at SHA256 `808a922ac2826b5eb9dd32033ce9ad7de0ffa2077b93325d9783dc5a4f33bcf3`. The final revision changes only the status sentence.

## Checked reduction

1. Treat all tail and head roles as distinct vertices. Covered tail roles form P and covered head roles form Q, disjoint in this expanded graph even when they represent the same physical vertex. Every edge either belongs to P×Q, goes from P to an exterior head, or goes from an exterior tail to Q. The vertex-cover hypothesis excludes every exterior/exterior edge. Exterior vertices are therefore independent pure-role vertices in the approved arbitrary-cross-subset balanced family.
2. Smaller covers can be padded by isolated auxiliary core vertices. Their monomer variables factor from every support term. Removing these factors preserves nonvanishing throughout the upper half-plane and leaves the desired split polynomial. Empty graphs and empty cover parts require no separate exception.
3. Original role activities attach to their unique role-copy vertices. Unused opposite-role activities have no effect. The balanced theorem supplies stability of this weighted split polynomial, including zero activities by its already justified nonzero limit.
4. Every original ordered disjoint support has a unique split support with the same matching feasibility and weight. Conversely, a split support survives physical pair-merging exactly when it uses at most one role of each physical vertex. Distinct role assignments with the same unused monomial remain distinct supports and their coefficients are correctly added; no matching multiplicity is introduced.
5. Each merge uses the stable symbol z+r+s. This applies regardless of whether the paired copies are core/core, core/exterior, or exterior/exterior. Pairs are disjoint, so merges can be iterated. The empty-support leading monomial remains coefficient1 and rules out a zero polynomial at each stage.
6. The diagonal root transfer and actual-degree Newton normalization are unchanged from the approved balanced proof.

## Internal-core-arc corollary

For disjoint physical sides P,Q of size two, this permits arbitrary arcs within each side and arbitrary forward P→Q arcs, together with P→I→Q exterior attachments. Every such arc is covered by a P tail or a Q head. Reverse Q→P and exterior/exterior arcs are not generally covered and are not included. Mutual within-side arcs are harmless because the physical merges impose the original disjointness condition.

Dependencies are the separately pinned arbitrary-cross-subset theorem, its complete/star/missing-edge proofs, and the previously source-checked Borcea–Brändén finite-degree stable-symbol theorem. This is an ordinary combinatorial reduction; no finite-population extrapolation or additional numerical assertion is involved.
