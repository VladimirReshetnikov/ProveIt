# Novelty decisions

These decisions assess overlap, not Lean elaboration or mathematical correctness.

## C1 — retain_narrow

Prove the actual Gamma coefficient is a unit using a single polynomial residue for each prime, or factor-wise nonvanishing via multiplicative order.

**Nearest prior:** E068 product-unit decomposition for integer Pell/norm factors; E091 explicit CRT congruence transport; E080 standard subtraction/casts.

**Remaining delta:** The new obligation is nonvanishing of the actual current-controller coefficient in each residue field, including q^2-1 and independent exponents; no earlier manuscript proposes its order-based factor test or one whole-polynomial residue certificate.

**Limits:** Do not claim generic product units, modular congruence composition, or factoring coprimality is new. Preserve Nat subtraction lower bounds and zero-exponent endpoints.

## C2 — retain_narrow

Use exponent-map fixed points to prove x^(p^n)=x from x^p=x, then evaluate controller polynomials through a finite residue action.

**Nearest prior:** E077 finite certificates and profiling; E091 congruence operation transport.

**Remaining delta:** The invariant is the iterated exponent map, not a scanner or geometric period; it removes distinct repeated induction/Frobenius residue reasoning for the new controller constants.

**Limits:** Existing finite residue calculations are assumptions/baseline, not new certificates to re-credit. A small helper must justify its aggregate code cost.

## C3 — retain_narrow

Replace the prime-power order proof split by the complete divisibility spectrum p^(k+1) | g^m-1 iff p^k | m.

**Nearest prior:** E099/E108 Pell power approximation budgets (different subject).

**Remaining delta:** No LTE, p-adic valuation spectrum, exact prime-power order or arbitrary-exponent spectrum proposal was found in the 28 packet manuscripts and targeted supporting-code searches.

**Limits:** Preserve m=0,k=0 and exact first-lift hypotheses; give the full mathematical proof and avoid circular dependence on the order theorem being shortened.

## C4 — retain_narrow

Remove sixteen_pow_bound induction by setting t=4^r, rewriting 16^r=t^2, and proving 4t+2<=t^2 for t>=16.

**Nearest prior:** E151 fixed-index-six Pell anchor; E143 geometric-sum induction reuse.

**Remaining delta:** This is a concrete exponential-to-polynomial reduction at NativePellPower.sixteen_pow_bound, absent from the prior claims; it does not re-propose Pell approximation or geometric-sum libraries.

**Limits:** Count the normal-form identities and proof of t>=16; do not infer compiler speed from source length.

## C5 — retain_only_with_endpoint_and_generalization

Strengthen normalized_low_digit to every low field including e=0 and arbitrary bounded marker maps by using the previous cell top reset.

**Nearest prior:** E031 exact scalar carry decomposition/reset; E032 derived carry recurrence; E033 cyclic field residues.

**Remaining delta:** The new information is the cyclic e=0 incoming-carry boundary and marker independence, derived from actual top_carry_digits. Generic local zero-carry cancellation is already assumed available.

**Limits:** A proposal only to rewrite carry equations or package projection facts would duplicate the corpus. Demonstrate eliminated marker-specific assumptions and unify real clients.

## C6 — retain_narrow

Use the actual periodic top-field reset to normalize each cell by an acyclic finite fold from zero and prove locality under edits.

**Nearest prior:** E031 scalar reset facts; E066 explicit least/greatest full-cycle carry formulas; E073 carry uniqueness with fixed raw and digits; E154 signed-prefix concatenation direction.

**Remaining delta:** A proved synchronization/reset boundary splits the cyclic normalizer into independent cells. This gives a constructive per-cell evaluation and edit-locality theorem, beyond closed formulas or uniqueness of a full cycle.

**Limits:** Do not replace the general arbitrary-predecessor fixedpoint theorem. Derive every cell reset from the actual raw budget and cover N=1/wraparound; raw convolution changes can affect neighboring cells, so locality must name the raw cells that stay equal.

## C7 — optional_interface_only

Use translation of an arbitrary size-a seed subset in ZMod T to realize any sum when gcd(a,T)=1.

**Nearest prior:** E102 translated support separation (different use).

**Remaining delta:** No exact translated fixed-cardinality subset-sum interface found. It removes the interval shape from the existence mechanism.

**Limits:** Current ControllerIntervalSums already has a short interval-sum formula and explicit startFor. No immediate net shortening is established if interval APIs and exact witnesses are retained.

## C8 — exclude_as_independent_new_mechanism

Shorten origin_reflected_zero by a direct modulo2011 support contradiction instead of reconstructing the previous cell.

**Nearest prior:** E033 shared ambient field residues and support-zero helper; E102 support separation through quotient homomorphism.

**Remaining delta:** The exact target is newly added, but the advertised residue/support-zero mechanism already covers this form of elimination.

**Limits:** Could be a small application of the assumed baseline API; do not advertise it as a separate new research idea under the user non-repetition constraint.

## C9 — exclude_without_sharper_new_contract

Replace finite radix prefix bounds by generic digit-length/range/library geometry.

**Nearest prior:** E040 copied-field bound interface; E053 finite-word/Fin-ZMod boundary; E134 exact geometric bound; E143 geometric-sum inductions.

**Remaining delta:** Generic word-bound reuse is already proposed. A new exact cell-reset theorem would need to carry the novelty instead.

**Limits:** No independent recommendation retained.
