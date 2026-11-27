# Source and proof dependency notes

## GitHub files inspected
Repository: `VladimirReshetnikov/ProveIt`, branch `main`, base path `Analysis/GeneralizedRiemannHypothesis/`, accessed 2026-11-27 through the GitHub connector. The following are Git blob identifiers returned with the reads, not claims about the current branch at a later date.

| Path relative to base | Blob SHA | Scope of reading |
|---|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | entire |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | entire |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | entire |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | entire |
| vendor/grh-lean/grh/src/New/Main.lean | fc0ae69627d2e66c3d1d57815d42f0aac5823432 | entire |
| vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean | 99e5240de112527b739068b692e5007720d310c1 | selected leading lemmas |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 | entire |
| Article/article.tex | 2d95d3db42756d4dcea77ecd304c92ded01ad7c6 | entire |
| Article/sections/intro.tex | b68b38b12772e23ffae3a25a1d449881435a4e5c | entire |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | heading inventory |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 | heading inventory; selected prime sums, bias, products, sign lemmas |
| Article/sections/ana.tex | f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce | heading inventory |
| Article/sections/li.tex | 87871b581808b4388135617b7d38cae1438bece5 | heading inventory |
| Article/sections/rec.tex | da56d6ad5a1a699e335dcfd327bcdc9492c64017 | heading inventory |
| Article/sections/zer.tex | 1f1e31367ea4fdd259786e3997d46ecd279d5cbc | heading inventory |
| Article/sections/spn.tex | 886e8716472aa82fd45ff68da03be946e9dbd3da | heading inventory |

Vendor README pins upstream `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`, Lean v4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The root project uses a different toolchain and does not build this vendor package. The article is a merge, not a verification. We did not inspect every source theorem or independently run Lean.

External checks: Andrew Sutherland's [original proof log](https://math.mit.edu/~drew/grh/) and [short proof log](https://klein.mit.edu/~drew/shortgrh/), which reports completion of the shorter-proof checks on 26 November 2026. These reports describe machine verification; they are not a human referee report. This packet relies on the exact statements, not a broader claim about general automorphic L-functions.

## Mathematical dependency graph / formalization plan (not implemented)

1. In the vendored package, `import Main`. The exported constants `riemannHypothesis`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, and `LFunction_eq_zero_re_of_isPrimitive` identify the required zero-location facts. The last is the primitive specialization. Check them using `#check` and `#print axioms` inside the vendored toolchain. For example, `lake env lean scripts/PrintAxioms.lean` after a successful build.
2. Analytic bridge: for a fixed smooth nonnegative bump supported inside (1,2), formalize the Mellin inversion and explicit formula for the primitive inducing character, the unit-interval zero count, and absolute summability of the decaying zero weights. Use the exported zero-location theorem and classical nonvanishing on the line Re(s)=1. Then strip prime powers and handle imprimitive factors. This is the principal formalization burden. Lemma 3.1 gives a conventional mathematical proof, not a claim that this exact lemma is already in Mathlib.
3. Define the finite family of primitive characters of order dividing a fixed prime, conductors <= Q. For a tuple use the character group of its common modulus (no need for a literal direct-limit type to prove rank witnesses; for each finite candidate set use its lcm). Show inflation injective on primitive representatives. Prove Fourier inversion on the finite vector space and the pointwise comparison in Lemma 3.2.
4. Work with a finite probability distribution on ordered distinct prime tuples, assigned the product of normalized remaining weights. Prove the one-step comparison by dividing by remaining total mass, and induct on coordinate positions to obtain the matrix estimate (4).
5. Count wildcard positions by divisibility of a product of distinct primes. Use elementary Hamming-ball volume bounds and a finite union bound over independent tuples, observation sets and received words. A failure probability less than one gives the witness list of primes. The converse is finite double counting and asymptotic Stirling, entirely independent of analytic number theory.

The rank comparison, coding argument, and converse are not certified Lean declarations in this packet. The finite Python check is independent of these analytic dependencies and is not a proof of the general result.
