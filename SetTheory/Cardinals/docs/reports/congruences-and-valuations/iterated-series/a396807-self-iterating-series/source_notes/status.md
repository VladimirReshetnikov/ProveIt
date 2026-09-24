# Source provenance and mathematical status

Checked September 19, 2026.

## Target: OEIS A396807

Source: <https://oeis.org/A396807>

Internal record: <https://oeis.org/A396807/internal>

The entry credits Paul D. Hanna, June 16, 2026. The retrieved internal
record identifier was `#9 Jun 18 2026 00:43:54`. This is distinct from the
site-wide modification timestamp in the page footer; that footer is not
evidence that the entry itself changed on the retrieval date.

The generating function is defined using **functional iterates**:
`A = x + A^[5] A^[6]`. Its two explicitly conjectural comments concern the
constant residue 1 modulo 10 and the residue `k^(n-1)` for coefficients
of every integer iterate. The report proves both.

The first 19 published coefficients were transcribed into the verification
script and compared exactly with an independently implemented triangular
construction. Although the entry links to a 400-term b-file, the delivered
verification does not claim to have compared all 400 terms against that
external file. The 400-term output in this archive was generated here.

## Related entries

A396797: <https://oeis.org/A396797>

The entry credits Paul D. Hanna, June 15, 2026, and uses iterate indices
3 and 4. Both modulo-6 conjectures follow from the same sharp-modulus
theorem proved in the report.

A396798: <https://oeis.org/A396798>

The entry credits Paul D. Hanna, June 16, 2026, and uses iterate indices
4 and 5. The displayed modulo-8 coefficient pattern needs a starting-index
correction: the word (1,1,5,5) begins at n=2, not n=1. The third coefficient
is 9, so a literal word beginning at n=1 is already false. The report proves
the corrected pattern and all the listed first-eight-iterate congruences,
as a single formula valid for every integer iterate.

## Distinguishing the kinds of claims

**Verified source status:** The cited records displayed the described
conjecture labels on the retrieval date.

**Mathematical claims of this report:** Self-contained proofs establish
uniqueness over arbitrary rings, the sharp weighted modulus, the cyclic
trace inverse, rationality modulo every selected prime power, exact
period 46860 modulo 100 for A396807, exact compositional orders, p-adic
iteration, related congruences, and factorial lower bounds.

**Computational evidence:** The included exact and symbolic programs were
executed. Their JSON files record the tested ranges. Finite checks alone
do not prove the infinite statements. In particular, the long period data
are consequences of proved formulas, not independent evidence for those
formulas beyond the separate 400-term direct check.

**Novelty limitation:** A limited search for A396807 and its congruences
did not locate a separate proof. A conjecture label in a database does not
guarantee that nobody has proved the statement elsewhere. No exhaustive
priority claim is made. The proofs have not been externally peer reviewed
or formalized in a proof assistant.

The article's bibliography contains the authoritative source links.
No edits, submissions, emails, or other external communications were made.
