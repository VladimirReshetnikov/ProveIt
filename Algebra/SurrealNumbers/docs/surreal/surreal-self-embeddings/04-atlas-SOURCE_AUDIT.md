# Source audit and proof-status boundary

Audit date: 3 October 2026.

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned snapshot: `a006a77a0a8bacdffe089b70d3b963b17228a089`.
The GitHub branch response identified this commit on `main`.
The repository root and surreal project READMEs were read while locating the
relevant material. Directory listings were also inspected. This was a
selective source inspection, not a clone, complete audit, or rebuild.

All paths below are relative to the repository root. The three Lean files
were fetched using the pinned commit. The manuscript and discovery READMEs
were fetched during the same session through the default branch; their
individual blob identities, where recorded, identify the actual text read.

### Actual Lean source inspected

1. `Algebra/SurrealNumbers/Surreal/Foundations/NormalFormExponentAutomorphisms.lean`
   - Full returned source inspected.
   - Blob: `a78aedc6ad3f95617e09cd74ec538e106a56c116`.
   - Defines exponent substitution on small normal forms and transports it
     to the actual sign-sequence field.
   - Its exponent input is an ordered additive **equivalence**. The proper
     embeddings in this article require generalization to injective ordered
     additive maps; the file is not cited as already proving that extension.
   - Concrete interfaces include `mapExponents`, `exponentRingEquiv`,
     `exponentAutomorphism`, `exponentAutomorphism_ofReal`, and
     `exponentAutomorphism_omegaPower`.

2. `Algebra/SurrealNumbers/Surreal/Foundations/ExponentAutomorphismStrongSums.lean`
   - Returned source through line 120 inspected, including its closing namespace.
   - Blob: `f1a81bf562a1695b467217b309bd457cea1828ef`.
   - Supplies strong summability, strong-sum, valuation, and order transport
     for the automorphisms above.
   - The strong-sum theorem explicitly uses a lower-universe smallness
     condition on its index type.
   - Concrete interfaces include `stronglySummable_exponentAutomorphism_iff`,
     `exponentAutomorphism_strongSum`, `valuation_exponentAutomorphism`, and
     `exponentOrderAutomorphism`.

3. `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceExpLog.lean`
   - Opening 95 lines inspected.
   - Blob: `07fe74404032c2783ae3d918006e825b28155345`.
   - The source explicitly states that its results concern exponentiation
     and logarithm at infinitesimals, **not a global surreal exponential**.
   - It defines `infExp` and `infLog` by power-series evaluation and proves
     local strong-sum and inverse identities.
   - Global exponential laws and exponential-field model theory in the
     article therefore rely on mathematical literature, not this local file.

### Repository research manuscript

`Algebra/SurrealNumbers/docs/surreal/exponential-automorphism-rigidity/article.tex`

- Opening 235 lines inspected.
- Blob: `ffb9a14697e79846c1e667bb971917c2f147b869`.
- Title: *Growth-Scale Rigidity for Surreal and Surcomplex Automorphisms*.
- Manuscript date: 21 September 2026.
- Source labels the report unrefereed and does not claim proof-assistant
  certification of its main rigidity arguments.
- Its stated growth-scale/displacement mechanism motivated the article's
  extension to nonsurjective embeddings. The article supplies the relevant
  embedding proofs rather than treating uninspected later manuscript text
  as a black-box verified theorem.

### Limits of the inspection

A request for `Algebra/SurrealNumbers/docs/FORMALIZATION.md` returned an empty
content field. No claim in this package is based on a successful reading of
that ledger. Other source files mentioned as possible integration points
may have been observed only as directory entries. No Lean build, kernel
check, transitive axiom audit, or independent verification of the repository's
entire foundation was performed. Repository-wide README assertions are not
substitutes for those checks.

## Principal external references

The article contains its own numbered bibliography. The following URLs
identify the main externally verified sources, not extra package dependencies.

- Bagayoko and van der Hoeven, *Surreal substructures*, Fund. Math. 266
  (2024), 25–96: https://arxiv.org/abs/2305.02001
- Kaplan, Krapp, and Serra, *Decomposing the automorphism group of the surreal
  numbers*, arXiv:2509.22374v3 (2026):
  https://arxiv.org/html/2509.22374v3
  The consulted version prints Questions 5.4, 5.6, and 5.7. Its open-question
  status is distinguished from the repository's later unrefereed proposals.
- van den Dries and Ehrlich, *Fields of surreal numbers and exponentiation*,
  Fund. Math. 167 (2001), 173–188:
  https://doi.org/10.4064/fm167-2-3
- Their erratum, Fund. Math. 168 (2001), 295–297:
  https://doi.org/10.4064/fm168-3-5
  The correction to Lemma 4.5 is noted; the original paper must not be used
  without accounting for its erratum.
- Wilkie, model completeness and the real exponential field, JAMS 9 (1996),
  1051–1094: https://doi.org/10.1090/S0894-0347-96-00216-0
- Berarducci and Mantova, *Surreal numbers, derivations and transseries*,
  JEMS 20 (2018), 339–390: https://arxiv.org/abs/1503.00315
- Berarducci and Mantova, *Transseries as germs of surreal functions*,
  Trans. AMS 371 (2019), 3549–3592:
  https://arxiv.org/abs/1703.01995
- Aschenbrenner, van den Dries, and van der Hoeven, *The surreal numbers as a
  universal H-field*, JEMS 21 (2019), 1179–1199:
  https://ems.press/journals/jems/articles/16016
- van den Dries, Ehrlich, and Mildenberger, *Homogeneous universal H-fields*,
  Proc. AMS 147 (2019), 2231–2234:
  https://doi.org/10.1090/proc/14424
  The earlier preprint at https://arxiv.org/abs/1807.08861 has two authors;
  the published bibliographic record has three. The theorem concerns the
  specified ordered valued differential language, not all extra operations.
- Gitman and Hamkins, *Open determinacy for class games*:
  https://arxiv.org/abs/1509.01099
- Gitman, Hamkins, Holy, Schlicht, and Williams, *The exact strength of the
  class forcing theorem*: https://arxiv.org/abs/1707.03700

Classical background is also attributed to Conway's *On Numbers and Games*,
Gonshor's *An Introduction to the Theory of Surreal Numbers*, and van den
Dries's *Tame Topology and O-minimal Structures*.

## Status of this article's results

- Conventional mathematical proofs are supplied for the statements labeled
  as proved in the article; they have not been formally checked in Lean.
- General class-model constructions use the explicitly stated GBC+ETR
  framework. Explicit support substitutions have a weaker, direct
  definable-class reading where stated.
- No assertion of being the first discovery of any theorem is made. The
  literature comparison is selective, not an exhaustive priority search.
- Differential universality and homogeneity are acknowledged as established
  positive results, not recast as new or generally unsolved problems.
- The research questions ask for additional classification or compatibility;
  they are not an assertion that every formulation is known to be globally open.
- The included 22,169 finite checks cannot validate arbitrary ordinals,
  infinite Hahn supports, class recursion, model-theoretic arguments, or
  Lean compilation. They only check finite exact instances.
