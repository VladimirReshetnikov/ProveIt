# Bounded primary-source audit: parallel conservative involutions

Audit frozen: 2026-10-03. Purpose: identify close precursors and safe attribution boundaries for the isolated, prospectively stable parallel-swap lemma and its two-block compiler application. This is a source audit, not an exhaustive novelty search.

## Bottom line

The architecture belongs to established marker-automorphism, conserved-landscape, reversible-block, and time-symmetric-CA traditions. A particularly close proof precedent is the recognition-set invariance argument in Maldonado–Moreira–Gajardo (2015), Proposition 2. The bounded search did not locate the exact generic combination of all-type raw-key isolation, prospective preservation of the entire raw-key set, and the radius estimate 3(b+r). That negative search result does not establish novelty. State the new lemma and compiler improvement as results proved in the present work; make no global priority or optimality claim.

## 1. Marker-delimited simultaneous permutations

**Mike Boyle, Douglas Lind, Daniel Rudolph.** “The automorphism group of a shift of finite type.” *Transactions of the American Mathematical Society* **306** (1988), 71–114. DOI: https://doi.org/10.1090/S0002-9947-1988-0927684-2

Primary author-hosted full text: https://sites.math.washington.edu/~lind/Papers/AutomorphismGroupSFT.pdf

**Checked locations:** §2, printed p.74 (physical PDF p.4); Lemma 2.2, p.75; Theorem 2.6 and proof, pp.76–77.

**Supported:** A marker M and equal-length data words D permit simultaneous replacements MDM → Mπ(D)M when occurrences overlap only in retained markers. This embeds finite permutation groups into the shift automorphism group. Theorem 2.6 explicitly constructs two marker involutions whose product has infinite order.

**Boundary:** These are designed nonoverlap/marker conditions, not a generic prospective check on arbitrary raw predicates. Particle conservation is not asserted for arbitrary data permutations. Restricting to equal-Hamming-weight data is an immediate conservative specialization, which should be identified as an observation rather than attributed as a separate theorem of this paper. The paper itself credits the marker method to earlier work including Hedlund.

## 2. Conserved landscapes and local conservative block permutations

**Tommaso Toffoli, Norman H. Margolus.** “Invertible cellular automata: a review.” *Physica D* **45** (1990), 229–253. DOI: https://doi.org/10.1016/0167-2789(90)90185-R

Author-hosted original: https://people.csail.mit.edu/nhm/ica.pdf

Author-uploaded corrected reprint inspected: https://www.researchgate.net/publication/223146745_Invertible_cellular_automata_A_review

**Checked locations:** §5.3, “Conserved-landscape permutations”; §5.5, partitioning discussion. Original PDF fetch timed out, but its indexed p.241 and the author-uploaded complete text were readable. The reprint advertises corrections/annotations through October 2001. Cite section numbers: original page ranges were not independently checked in the original PDF.

**Supported:** In the Patt example, a permitted flip neither creates nor destroys triggering landscape occurrences, so the same local operation reverses the update. The general discussion requires the inverse-time landscape to identify the forward permutation. Partitioning places both ends of a particle move in one local operation, making local conservation sufficient for global conservation.

**Boundary:** The binary flip example is not number-conserving. Their conserved-landscape principle precedes the present candidate-set invariant; the generic all-type prospective eligibility procedure and its radius constant were not identified here.

## 3. Closest recognition-set preservation proof

**Diego Maldonado, Andrés Moreira, Anahí Gajardo.** “Universal Time-Symmetric Number-Conserving Cellular Automaton.” *AUTOMATA 2015*, LNCS **9099**, 155–168. DOI: https://doi.org/10.1007/978-3-662-47221-7_12

Publisher record: https://link.springer.com/chapter/10.1007/978-3-662-47221-7_12

Primary institutional preprint: https://www.ci2ma.udec.cl/pdf/pre-publicaciones/2015/pp15-18.pdf

**Checked locations:** Theorem 1, physical PDF pp.4–5; Corollaries 1–2, p.6; Proposition 2, pp.6–8, especially the recognition argument on p.8. These are physical preprint page numbers, not verified journal-page pinpoints.

**Supported:** Proposition 2 converts an arbitrary reversible partitioned CA to an RNCA. Its radius-1 pair-update map Ā_f recognizes L/R pairs, fixes W cells, and preserves the complete L/R/W classification on arbitrary configurations. Recognized pairs retain constant total mass; preserved recognition allows inversion with f⁻¹. The whole map also includes a subcomponent-shift factor Ī. Theorem 1 preserves number conservation while time-symmetrizing an RNCA on an enlarged alphabet; Corollaries 1–2 establish universal examples.

**Boundary:** Only Ā_f fixes W and preserves L/R/W; do not say the whole Ā_f∘Ī fixes malformed configurations. The theorem's time-reverser exchanges base-s digits and is generally not number-conserving. Thus it does not directly supply two individually conservative involutions. It does not give the present binary compiler or generic prospective-key radius bound.

## 4. Two involutions are the standard CA time-symmetry criterion

**Anahí Gajardo, Jarkko Kari, Andrés Moreira.** “On time-symmetry in cellular automata.” *Journal of Computer and System Sciences* **78** (2012), 1115–1126. DOI: https://doi.org/10.1016/j.jcss.2012.01.006

Primary institutional preprint: https://www.ci2ma.udec.cl/pdf/pre-publicaciones2/2011/pp11-28.pdf

**Checked location:** Proposition 1, physical PDF pp.6–7 (the preprint includes a cover sheet).

**Supported:** A CA F is time-symmetric exactly when it is a composition of two CA involutions; equivalently F∘H is involutive for some involutive CA H.

**Boundary:** Not every reversible CA is thereby a product of two CA involutions. Nor does the criterion impose number conservation on either factor. For the present F=AB, A²=B²=id directly gives AFA=F⁻¹ and BFB=F⁻¹; if A and B preserve particle number, these reversors do too. This is an algebraic corollary, not a novelty claim.

## 5. Conservative recognizers already appear in Morita's RNCA simulator

**Kenichi Morita.** “Universality of One-Dimensional Reversible and Number-Conserving Cellular Automata.” *EPTCS* **90** (2012), 142–150. DOI: https://doi.org/10.4204/EPTCS.90.12

Primary full text: https://arxiv.org/pdf/1208.2760

**Checked locations:** Lemma 2, printed pp.145–149; recognition equivalences (5)–(6), p.146; conservation/injectivity argument, pp.147–149; Theorem 1, p.149.

**Supported:** Any s-state two-neighbor reversible partitioned CA has a four-neighbor 4s-state RNCA simulator. The construction recognizes balanced heavy/light pairs and exploits persistence/transport of those recognizable pairs to establish full-shift reversibility and conservation. Theorem 1 gives a 96-state universal example.

**Boundary:** Multistate numeric mass is not binary occupancy. The paper expressly notes that a direct reversible-Turing-machine simulation may use ultimately periodic infinite configurations even for a finite TM configuration. It therefore does not establish universality with the present five particles or two conservative binary factors.

## 6. Reversible block-representation theorems: relevant but different

**Jarkko Kari.** “Representation of reversible cellular automata with block permutations.” *Mathematical Systems Theory* **29** (1996), 47–61. DOI: https://doi.org/10.1007/BF01201813

Primary publisher record: https://link.springer.com/article/10.1007/BF01201813

**Checked:** Publisher abstract only. It establishes structural reversibility in dimensions one and two using block permutations and shift-like maps. Do not assign an unverified theorem number or infer two conservative involutive CA factors from this abstract.

**Jarkko Kari.** “On the Circuit Depth of Structurally Reversible Cellular Automata.” *Fundamenta Informaticae* **38** (1999), 93–107. DOI: https://doi.org/10.3233/FI-1999-381208

Primary publisher abstract: https://journals.sagepub.com/doi/abs/10.3233/FI-1999-381208

**Checked:** Abstract: arbitrary reversible CA embed into a two-layer Margolus scheme; d+2 consecutive block layers can be reduced to d+1. For d=1 this is two block-permutation layers.

**Boundary:** A fixed-partition layer need not commute with the unit shift, need not be involutive, and need not preserve occupancy. Embedding may change the state space. These results are not the statement that arbitrary ordered conservative gate lists equal two full-shift involutions on the original binary alphabet.

## 7. Commuting localized involutions on a doubled alphabet

**Pablo Arrighi, Vincent Nesme.** “A simple block representation of reversible cellular automata with time-symmetry.” arXiv:1201.5529 (2012).

Primary full text: https://arxiv.org/pdf/1201.5529

**Checked locations:** Definition 1, physical PDF p.3; Proposition 1, p.4; Corollary 1, p.5.

**Supported:** On a doubled alphabet, the conjugates K_i=(G⁻¹×id)S_i(G×id) of on-site swaps commute and are localized; the full product satisfies G×G⁻¹=S∏K_i. Their localization is controlled by the block neighborhood.

**Boundary:** The commuting K_i are involutions by conjugation, but they need not be disjoint writes. This doubles the state space and simulates forward and inverse dynamics simultaneously. It is not a binary occupancy-preserving compiler or the proposed conflict-selection rule. Useful only if a fuller discussion of reversible local implementations is wanted.

## 8. Binary conflict-free conservative swaps: SALT comparison

**Daniel B. Miller, Edward Fredkin.** “Two-state, Reversible, Universal Cellular Automata In Three Dimensions.” arXiv:nlin/0501022 (2005).

Primary full text: https://arxiv.org/pdf/nlin/0501022

**Checked locations:** “The Rule,” physical/printed pp.5–7; “Reversibility,” p.8.

**Supported:** A phase swaps selected same-parity neighboring bits, conditional on opposite-parity cells, and suppresses any swap with a conflicting possibility at either endpoint. Controls are unchanged during that phase, so repeating it undoes the phase. Bit swaps conserve the number of occupied cells.

**Boundary:** Three-dimensional, parity-partitioned, six-phase dynamics. This is a concrete precursor for conflict-free parallel conservative involutions, but not a one-dimensional, unit-shift-commuting two-factor construction. No generic prospective-key preservation test is supplied.

## 9. Modern formal landscape criterion (secondary for the criterion's origin)

**Luca Mariot, Stjepan Picek, Domagoj Jakobovic, Alberto Leporati.** “Evolutionary algorithms for designing reversible cellular automata.” *Genetic Programming and Evolvable Machines* **22** (2021), 429–461. DOI: https://doi.org/10.1007/s10710-021-09415-7

Full publisher text: https://link.springer.com/article/10.1007/s10710-021-09415-7

**Checked:** Lemma 1 and immediately following paragraph in §2.3. The incompatibility condition across all triggering landscapes yields conserved-landscape involutions. The paper explicitly attributes this criterion to Toffoli–Margolus, so it is a helpful formal restatement, not an original-source priority claim. Publication year is 2021, not 2022.

## Recommended attribution wording and limits

“The construction uses established marker and conserved-landscape ideas: recognize local regions, apply reversible local permutations, and preserve enough recognition data to identify the inverse update. The explicit recognition-set invariance proof in Maldonado, Moreira and Gajardo (2015, Proposition 2) is especially close. The result proved here is a particular quantitative parallelization rule, with all-type isolation and a finite prospective raw-key test, together with its exact preservation of the compiler's admissible trajectories.”

Add the following distinctions wherever relevant:

- The radius improvement is relative to the frozen compiler and its previous proven bound, not an optimum over all binary conservative CA or all simulators.
- The new map and old ordered map agree on the audited admissible doubled micrograph; no global equality on malformed configurations is claimed.
- Candidate-set preservation and eligibility-set preservation are distinct proof obligations. Classical conserved-landscape intuition does not replace the second obligation or the read-window separation argument.
- A two-block representation, a product of two CA involutions, and a product of two individually particle-conserving CA involutions are different assertions.
- No inspected source was found to state precisely the prospective test and radius constant in the current lemma. This is a bounded-search observation only.

## Audit coverage and access limits

The full relevant primary passages were read for BLR 1988, GKM 2012, MMG 2015, Morita 2012, Arrighi–Nesme 2012, and Miller–Fredkin 2005. The Toffoli–Margolus complete author-uploaded reprint and original indexed passages were read, but direct author-PDF opening timed out. Kari 1996/1999 were checked at publisher-abstract level only; no internal theorem number is asserted. The search additionally checked combinations of “binary,” “number-conserving,” “particle-conserving,” “marker,” “involution,” “isolated swap,” and “prospective,” without locating an exact prior statement. Broad universality, minimum-particle, and optimal-radius literature were outside this bounded audit.
