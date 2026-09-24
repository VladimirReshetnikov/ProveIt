# Status and claim boundary

Prepared 20 September 2026.

## Claimed mathematical result

A complete elementary proof of the eventual reverse-reply assertion of
Conjecture 2.9 in arXiv:2603.16004v1, for every k >= 3, with the explicit
sufficient bound R(k) = k + (k+1)^2(k-2)^2 + 1.

The principal independent statement is the eventual pattern-isolation theorem:
if F and Q are sets of nonmonotone length-k patterns and an F-avoider of length
at least R(k) contains a Q-member, then there is a one-block family avoiding F
and containing exactly one fixed Q-member. It supplies witnesses of every
length N >= 2k-1. The output Q-member need not be prescribed in advance.

The reverse-reply application uses reversal closure to orient that member.
A complement-reply corollary and a bounded-forbidden-length extension are also
proved. The exact-length step and the monotone endgame are explicit.

## Proof dependencies

- Classical permutation-subsequence containment and rank standardization.
- The elementary Erdős–Szekeres monotone-subsequence theorem, reproved.
- Finite inclusion-minimality of singleton supports.
- Elementary normal-play pairing and termination.

No classification, finite lookup table, numerical approximation, computer
search, or unproved conjecture is imported into the proof.

## What was checked computationally

All 192 marked signed templates with k=3 and all 1,200 with k=4 were checked
against direct subsequence enumeration at three block lengths. The suite checks
6,886 reverse-pair minimizations and 2,192 additional target-set minimizations.
It also checks 360 sampled larger templates, 100 constructed large replies,
unstructured extraction examples, monotone-subsequence boundary examples,
and the complete recorded length-330 certificate.

The optional original discovery exploration and its packaged rerun examined
8,640 templates for k=5 and 70,560 for k=6. It found no failed support. These
are finite consistency checks, not formal verification of the universal proof.

## Qualifications

- No independent referee has reviewed this draft.
- No Lean, Isabelle, Coq, or other proof-assistant verification was performed.
- The threshold R(k) is sufficient, not asserted minimal; it is intentionally
  worse than the already-known bounds for k=3 and k=4.
- No full Sprague–Grundy table, misère result, or mixed-move-length game result
  is claimed.
- The selected conjecture is explicitly open in the retrieved source version;
  searches did not identify a later solution. This does not certify the absence
  of all unpublished, unindexed, or independent work.
- The abstract isolation lemma's independent priority has not been established
  by a comprehensive literature review.
