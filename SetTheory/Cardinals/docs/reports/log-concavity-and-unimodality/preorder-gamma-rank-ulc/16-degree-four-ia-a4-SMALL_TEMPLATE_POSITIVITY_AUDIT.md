# Four-attachment positivity: complete approval of the 33 small legal-type templates

## Verdict and exact scope

APPROVED for all 33 canonical four-attachment templates whose complete legal exterior-type set has at most five members:

20, 29, 35, 39, 41, 42, 43, 44, 45, 47, 48, 49, 52, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75.

Every nonnegative integer population of each listed template satisfies actual-degree ULC. All 303 outstanding representative-face inequalities for these templates have independently verified rational certificates. Eight templates (52,62,65,66,69,71,73,75) needed no additional certificates because the previously audited face reductions already cover them completely.

The other 43 canonical four-attachment templates are NOT approved by this result. In particular this does not automatically cover a face of a higher-type template merely because at most five of its populations are positive. The scope is the exact listed complete templates, not an unrestricted number-of-occupied-types condition. No claim is made for fractional populations between zero and one.

## 1. Fresh reconstruction from support data

The independent checker `audit_small_faces.py` starts with the previously Hall-verified gamma arrays, not the producer's face expansion. It reconstructs G_k=24γ_k by multiplying the falling factors defining every binomial population term. Quota total at most four ensures that 24 clears every factorial denominator.

Direct ordinary-polynomial multiplication gives the two gaps in G, which are exactly 576 times the gaps in γ. For every required face, the checker sets inactive populations to zero and substitutes 1+y at active coordinates. It proves that all resulting coefficients are divisible by four, and multiplies them by 5/4. This independently yields exactly 720 times the original shifted gap.

The source records are checked against these complete polynomials. Their positive divisor is independently recomputed as the gcd of all coefficients, and their retained coordinates are checked to be exactly the original population coordinates actually used. Removing those unused coordinates and dividing by the gcd gives precisely the supplied source polynomial, term for term.

Thus the checked identity is

720 · original Newton gap on the face = source divisor · source polynomial.

The original global source-target ID is also verified against the complete sorted 39,367-task ledger; it is not confused with either the template ID or the subsequently normalized polynomial ID.

## 2. Normalization maps are verified independently

For all 303 source faces, the normalized alias has the correct source ID, gap, and face. Its coordinate list is injective and in range; every dropped coordinate is unused. The checker explicitly permutes the complete source polynomial and verifies

permuted source polynomial = positive alias scale · normalized target.

Every normalized target is referenced, every required source face has an alias, and no source task or alias is duplicated. Polynomial equality is checked using exact coefficient maps, not floating-point evaluations or digests.

The batch's selected template list is independently compared with the complete template file, selecting precisely those whose full legal-type count is at most five. Its source face set is exactly the previously approved outstanding-task set restricted to those templates.

## 3. Exact rational identities

The completed immutable certificate ledger supplies 303 identities: 297 binomial-square certificates and six general-square certificates. All of them were expanded with unbounded-integer rational arithmetic.

Across these identities the checker verifies:

- 2,326 positive-weight monomial-times-binomial-square terms
- 176 positive-weight monomial-times-general-square terms
- 22,127 positive monomial terms

Every exponent is a nonnegative integer. Every outside weight is a strictly positive rational number; the smallest is 1/33611792537690994. Each square is expanded and its terms summed before comparing the result with the entire normalized integer target. There are no tolerance-based acceptances or finite-population substitutions.

These identities prove the required targets nonnegative on their nonnegative shifted orthants. The first Newton inequality, lower-degree boundary cases, and structural/component reductions remain exactly those already justified in the complete kernel and face-orbit audits.

## 4. Template-level completeness

A successful individual identity is not enough to approve a template. The verifier maps every certificate back through both alias stages and requires all outstanding orbit tasks of that template to be covered. The complete orbit coverage and integer zero/positive partition were established by the separate face-orbit audit. This run accounts for all 303 outstanding faces, all 303 normalized targets, and every task of all 33 listed templates; its pending-template list is empty within this batch.

The checker also supports a partial immutable certificate snapshot: it reports a template as approved only when that template has no remaining source task. It never turns a partial target count into a whole-template theorem.

## 5. Reproduction

Run `python3 audit_small_faces.py` for the independent mapping-only verification. Run it with `--certificates` pointing to the immutable small-faces `certificates.jsonl` for the complete identity and template audit. The script uses only the Python standard library and imports no producer module.

`small_faces_incremental_audit.json` records the approved and pending template lists, every per-template task count, all authoritative input hashes, the verifier hash, exact term counts, and runtime. Input files are hashed before and after execution. `small_faces_mapping_audit.json` records the earlier mapping-only stage and the eight templates that already needed no new certificates.

This is an incremental result inside the four-attachment sector. The full actual-degree-four conjecture remains unproved until the remaining template families are settled.
