# Borel conjugacy intake and an effective-presentation boundary

The new archive supplies a coherent rank-one Borel classification and flow argument. I found no mathematical correction needed in the complete manuscript read. It supplies no paid ordinary-integer compiler, finite Diophantine certificate, gate ledger or operation-count improvement. Its explicit warning that Borelness is not computability is essential. A new review-side lemma below makes that boundary concrete: a fixed exponent group with decidable rational membership can have co-c.e.-complete conjugacy even on finite, rational Euler-field inputs.

This is an independent mathematical reading of an unrefereed text, not a proof-assistant certification or a historical-priority determination. The external bibliography, prior Library draft and delivered PDF were not independently verified or rendered.

## Immutable archive and exact coverage

Arrival commit: `62846e17a78ee588f0d3686c966c1cde9a0f1bb9`.
Archive: `docs/incoming/Borel_Conjugacy_Divisibility_Threshold.zip`.
Git blob: `36e9557e31a7380341ca7fbde29d7b620cb18924`.
Bytes:370,852. SHA256: `affb3707e92ac55290e204d2adc786ac126b0da9bb878d0c754f138084a26b8d`.

All six regular members were inventoried and hashed from immutable Git ZIP bytes; all five entries of the delivered checksum manifest match. The companion JSON records member sizes, CRCs, hashes, exact inclusive read spans and context blobs.

| Member under `borel_conjugacy/` | Bytes | Actual coverage |
|---|---:|---|
| `borel_conjugacy.tex` | 85,223 | All1,874 lines, including every mathematical proof, examples, questions, scope and references |
| `README.md` | 4,834 | All101 lines |
| `verify_jets.py` | 11,424 | All284 lines read as inert text; not executed/imported |
| `verification_report.json` | 3,052 | All127 lines, as saved evidence only |
| `MANIFEST.sha256` | 420 | All5 entries authenticated |
| `borel_conjugacy.pdf` | 339,135 | Bytes/hash only; no page-count or visual verification |

The manuscript reports143 exact rational jet checks at degree24; their count adds correctly in the supplied JSON. Their PASS status remains a delivery claim. No supplied suite, builder, archived program, frozen predecessor or copied helper was run. The fresh review helper performs only immutable metadata authentication and new finite height-model corroborations. It neither reconstructs nor replays the jet suite.

Applicable ancestor instructions were inspected. The incoming README's Section4.11 requires unproved and wrong claims to remain credited on record. Nothing is removed here: the manuscript's ten further questions remain questions; the new lemma below answers only a negative effectivity subcase and is explicitly attributed to this review. No source counterexample requiring a retained correction was found.

## Mathematical interface challenged

The field consists of real-coefficient series on a fixed additive subgroup Z<=Gamma<=Q whose support meets each left half-line in a finite set. This is narrower than arbitrary Hahn support. Borelness is with respect to countable real coefficient coding. The coordinate group comprises Borel **ordered-field** automorphisms; the order restriction follows automatically only in the stated2-divisible cases. No Borel structure or computation on the proper class of all surreals is asserted.

The following complete proof chain was checked from the printed arguments.

* Lines211–477 establish support calculus, coefficient slices, the derivations D_a=aE and the allowed coordinates h=A*t^r*(1+u), with r*Gamma=Gamma. The slice proof uses actual Polish products for a fixed left-finite support, not an unsupported Polish topology on the entire field. Its finite-coordinate conclusion and valuation comparison justify the extension from monomials. Tangent inversion has a uniform positive valuation gain.
* Lines478–768 derive residue covariance and tangent normalization in all three gain cases, then full conjugacy and Borel witness selection. The positive-gain contraction increases valuation by alpha>0; its support monoid remains left-finite even with unbounded denominators. The chosen primitive constant is a normalization choice, not an orbit transversal. The compositional order in the displayed witness agrees with the stated substitution convention.
* Lines769–925 prove the height characterization and unit group, then the exact smoothness threshold. Two infinitely divisible primes give a countable dense logarithmic subgroup, and the invariant-set Baire argument excludes smoothness. Zero or one such prime gives the displayed complete invariants. This is descriptive-set-theoretic smoothness, not a decidability or uniform finite-arithmetic theorem.
* Lines926–1327 prove the centralizers, flow criterion and automatic time regularity. Negative gain contradicts the constant coefficient of the image of a positive infinitesimal. The analytic support lemma uses a point outside countably many analytic zero sets. For merely Borel time coordinates, the exponent character is trivial by divisibility; linearization or the positive-gain logarithm places the action in a one-parameter centralizer. The single extracted scalar then satisfies the measurable Cauchy equation. Entire coefficient dependence is in the time parameter, not analytic convergence in t.
* Lines1328–1874 contain consistent worked examples, the set-sized surreal interpretation, the finite-jet interface and explicit limitations. The supplied code's unit-power recurrence and normalization residual match the printed equations on their finite rational grids. This inert source reading does not validate the saved143 runs or establish any infinite theorem by computation.

No blanket claim about external antecedents, all algebraic automorphisms, arbitrary higher-rank groups, formalization or historical novelty follows from this review. Those boundaries are expressly preserved by the manuscript.

## Existing repository questions

The earlier manuscript *Borel Regularity Forces Summability* already appears as source23, Part XVII of
`Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/`.
The archive's reference to an earlier user manuscript should be linked to that existing continuation at placement, rather than treated as an unrelated new research programme.

At immutable62846e17a, the host README lines18–60 identify its placement5e4d8eed8. The host article lines36434–36476 contain questions `pma:bsd:q:conjugacy` and `pma:bsd:q:flows`; the latter still says the non-Euler cases are otherwise open. The incoming manuscript supplies the rank-one, ordered-coordinate classification and precise analytic/Borel-time flow answers above. The broader unordered and higher-rank questions are not thereby closed. These exact context spans and hashes are in the receipt; the rest of the41,000-line host article was not reread in this intake.

## New review-side lemma: decidable exponents do not make conjugacy decidable

This lemma was suggested by root and independently checked here. It is not attributed to the archive, does not refute its effectivity question, and is not a claim of historical novelty. Its only series-theoretic input is the explicitly proved zero-gain coordinate classification just reviewed; its group construction is elementary.

Fix an effective enumeration p_0,p_1,... of the primes and an effective enumeration M_0,M_1,... of machines whose halting-index set on blank input is c.e.-complete. Insert a mandatory initial step, so a halting machine has a least halting time H_e>=1. Put

```
h_(p_e) = H_e−1  if M_e halts,
h_(p_e) = infinity otherwise.
```

Define Gamma to contain0 and every reduced rational m/n whose denominator satisfies

```
v_p(n) <= h_p for each prime p dividing n.
```

**Decidable subgroup.** Factor the finite positive denominator n. For every p_e^j dividing it, simulate M_e for j steps and reject exactly when it has halted by then. This terminates and decides membership; it never decides whether a machine will halt later. Integers belong automatically. Denominators of sums and differences divide the least common multiple of the original denominators, so each prime exponent stays within the corresponding bound. Thus Gamma is an additive subgroup of Q containing Z, with computable rational membership and computable inherited rational operations. Every advertised height is exact, since1/p^j passes precisely for j<=h_p.

**Undecidable scaling units.** If h_p is infinite, division by p preserves all denominator bounds, so p*Gamma=Gamma. If h_p=h is finite,1/p^h belongs to Gamma but1/p^(h+1) does not; multiplication by p is therefore not onto. Hence

```
p_e in U_Gamma  iff  M_e never halts.
```

The computable map e->p_e reduces nonhalting to membership in the positive rational scaling group. Conversely, failure of unit membership for a rational scalar can be enumerated by waiting for a halting event at one of its finitely many nonzero prime valuations. In particular the prime-index unit slice is co-c.e.-complete.

**Finite-input conjugacy consequence.** On this one fixed L_Gamma, the reviewed zero-gain theorem gives

```
D_1=E is conjugate to D_(p_e)=p_e*E
iff p_e in U_Gamma
iff M_e never halts.
```

The supplied derivations have finite rational symbolic descriptions; arbitrary real coefficients are not causing this obstruction. Directly, a conjugating coordinate must solve E(h)=p_e*h, hence h=A*t^(p_e); such a coordinate is an automorphism exactly when p_e*Gamma=Gamma. Thus the effective Euler-conjugacy index set is co-c.e.-complete, and its complement is c.e.-complete.

**No existential Diophantine graph for this orientation.** An ordinary existential polynomial relation over natural numbers is c.e.: enumerate all finite witness tuples and evaluate the integer polynomial. Consequently there is no fixed integer polynomial P(e,y_1,...,y_k) whose natural-number solutions characterize this conjugacy index set. The same obstruction applies to a putative existential integer graph on the coefficient p, because its computable preimage along e->p_e would be c.e. A finite nonconjugacy certificate is simply a halting computation of M_e; reversing to that c.e. orientation supplies no new paid compiler, witness bound or operation saving.

The one-step convention matters. A machine halting on step1 has height0, so1 is allowed but1/p is not. The fresh helper checks this boundary and subgroup closure on a finite toy height table. Those finite checks do not establish or decide nonhalting; the all-size argument above proves the obstruction.

## Concrete remaining computational bottleneck

The manuscript's effective-normalizer question at lines1658–1668 cannot be answered from a decidable rational membership test for Gamma alone. Additional effective information about its infinite-height primes or unit group is necessary even for the simple conjugacy slice above. Certified support and coefficient truncation procedures are also needed before its finite-cutoff normalization formulas become algorithms.

For a fixed finite localization with exact rational coefficient data and an explicit finite cutoff, the jet formulas offer a finite arithmetic task. The cutoff, input loading, rational denominators, support bounds and every scalar operation would still require a charged integer graph to compare with the current Diophantine constructions. The archive gives none. Its Borel witnesses, infinite-height tests, real powers and formal infinite supports must not be treated as free circuit primitives.

The review's fresh metadata/height helper and JSON were checked in normal and optimized Python before freeze. No repository file, Git reference, archive member or supplied evidence was modified.
