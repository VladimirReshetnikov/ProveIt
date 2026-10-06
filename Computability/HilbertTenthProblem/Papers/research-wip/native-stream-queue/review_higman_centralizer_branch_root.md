# Independent audit of the literal Accepted centralizer branch

Status: PASS for the exact literal branch and the separately reviewed hand
membership-to-word-problem lemma. This is a research artifact, not a new
numerical universal Diophantine bound.

The [centralizer construction](positive7_higman_centralizer_branch_riemann.md)
retains the Accepted prefix of the
[complete literal presentation](positive7_higman_literal_presentation_riemann.md)
and adjoins one generator fixing the three Accepted subgroup generators.
The resulting presentation has 499 generators and 17,679 relator slots.
The separate [hand lemma](positive7_higman_membership_word_problem_aristotle.md)
proves, under the explicitly inherited Accepted-subgroup premises, that
`W_n = [alpha^(beta^n), t]` is trivial precisely when `n` belongs to the
fixed universal set `U`. Here right conjugation is `h^g = g^-1 h g` and
`[h,t] = h^-1 t^-1 h t`. No parameter value was instantiated by this audit.

## Exact independent record comparison

The original root checker is `review_higman_centralizer_static_root.py`.
Root fully preflighted its source; Riemann separately read the entire source
and passed its scope before the sole execution. Its locked source SHA256 is
`b435437c2e156d6203653b356c8314b988838fab102edcd0c630f4fad2f682cd`.
The first run passed and its source, first JSON receipt, and first log are
permanently frozen. Riemann subsequently read the complete frozen first
receipt and the checker source again, with no defect found and no replay.

The check compares every retained generator object (498) and every retained
relator object (17,676) against the exact parent slices. The parent's full
independent comparison is bound to Pascal's first receipt
`39f3d7a0eaeb5568da89b6188fac13f2cfbdbb462b4d8237359e7197a1b537eb`.
It independently spells the new generator and each of the three new
12-letter relators, checks all three query ports, reconstructs the complete
124-entry event catalog and its parent-event byte fingerprints, and checks
every top-level metadata field, name/ID sequence, boundary and census.
This is a complete record comparison, not a sampled tail inspection.

For each `j` in `467,468,469`, the Accepted word is
`ell_j = [-498,-497,j,497,498]`. The new generator is ID499 with name
`centralizer/t`. The corresponding fixing relator is exactly
`[-499,-498,-497,j,497,498,499,-498,-497,-j,497,498]`.
The fixed query ports are
`alpha = [-468 repeated 23 times,467,468 repeated 23 times]`,
`beta = [-469,468,469]`, and `t = [499]`; their literal lengths are 47,3,1.
These statements describe signed-generator strings, not their evaluation.

## Mathematical review and retained boundaries

Root and Riemann fully reviewed the hand centralizer lemma. Pascal's earlier
review was bounded at the lemma's freeze; Pascal subsequently supplied a
full hand challenge of its mathematical draft, also passing. This later
review is recorded here without modifying the earlier frozen chronology.
Britton's lemma gives `[h,t]=1` for base-group `h` exactly when `h` lies in
the associated subgroup. The independent free-family argument then
identifies the specified one-parameter membership set. The inherited
counter-machine universality and operation-specific subgroup lemmas remain
attributed premises, not claims of a new complete primary-source audit.

**Remark 1 (invalid full-ambient centralizer).** Fixing all ambient generators
would force every query to be trivial, including `W_0`, although `0` is not
in `U`. Only the three generators of the Accepted subgroup are fixed.

**Remark 2 (branch-local names).** ID499 in the old final `X_U` transducer
and ID499 in this branch denote different generators. The old two-relator
tail is omitted only in this separate branch. Its active caches, selected
list and transducer metadata cannot be reused as centralizer metadata.
The original parent output is preserved byte for byte.

**Resolved question 1 (root and Pascal).** The author companion froze while
this separate comparison was pending. Its complete-prefix/new-suffix audit
has now passed. That status is advanced here; frozen author statements are
historical provenance, not a request to rerun either original program.

**Open question 2 (root and Aristotle).** Supply the actual paid arithmetic
interface for this three-fixed-word query, including all input loading and
history costs. The separately reviewed finite two-generator theorem is a
mathematical bridge; its large substituted relator arrays and matrix
alphabet have not been materialized. Relator slots alone do not determine
the compiler cost. The established universal frontier remains
84 operations = 47 multiplications + 37 additions, 18 positive witnesses,
and exact degree 187.

No predecessor, supplied, or frozen scientific program was executed or
imported. No group-word reduction/evaluation, saved-array evaluation,
symbolic degree propagation, machine simulation, or TeX/Lean build occurred.
The only new execution audited here was the original record comparator
after full preflight, once. All other preparation was hand proof, inert
record reading, byte authentication and ordinary repository editing.
