# Six fixed membership replacements are too weak

For each fixed choice `U ∈ {R(A,B), R(B,A), R(A,C), R(C,A), R(B,C), R(C,B)}`
in the native rho8 schema, **ZFC proves consistency of the resulting numerical
calculus**. This retains every other native row and the full seed/support
bundle. Assuming ZFC is consistent, none of these six proposals can therefore
have its consistency provably equivalent to Con(ZFC) in ZFC.

The [R(A,B) invariant](../diagonal-invariant/README.md) is Lean-checked.
The remaining five extensions here are **ordinary mathematical proofs**, not
additional Lean builds. This result treats each fixed orientation separately;
it does not cover the union of multiple orientations, an added classical
basis, dominated `U≤A`, or every code-dependent membership builder.

## Why the remaining cases close

The same auxiliary-class argument handles R(B,A), since its code is strictly
larger than A. For R(A,C) and R(C,A), the only extra possible rho6 trigger
would force A=C=0 and also make C a positive quantifier code, a contradiction.
See the [earlier independent inversion analysis](evidence/invariant-peer.md).

R(B,C) and R(C,B) require a real extension: there are valid H-to-H modus
ponens steps. The [complete proof](evidence/rbc-invariant.md) adds two explicit
families J and D to the auxiliary class. H can produce J or D, but no class
member supplies the antecedent needed for either to fire. Constructor tags
and strict code growth exclude every last-generator case. Induction on the
major-premise witness then gives MP closure; Q stripping handles quantified
monotonicity. F is excluded because it is membership-headed. The proof covers
the exceptional zero alias and uses no theorem-substitution principle.

The [independent review](rbc-rcb-independent-review.md) rederives the allowed
H/H step and every exclusion; its [receipt](rbc-rcb-review.json) states the
ordinary scope. These finite syntactic arguments are formalizable in ZFC.
They do not establish any machine-runtime theorem or affect accepted K219,
whose rho8 remains unrestricted.

## Search evidence and provenance

The proof is unbounded and does not depend on a failed search. The preserved
[evidence directory](evidence) also contains the preceding bounded schema
experiments: actual scripts, complete proof records, execution summaries,
first failed author-side substitution attempt, and its narrow correction.
The corrected full gated-bundle run completed ten rounds and reached its
25-second cap in round eleven; it found no requested universal target.
This is a bounded discovery result only. Literal bundle side conditions
were propagated; substitution was simultaneous after the correction.

The [freeze record](evidence/freeze.json) identifies the original scratch
artifacts. Original absolute paths are execution provenance. The corrected
standalone search is `evidence/condensed_v2.py`; invoke `--help` for its fixed
families and explicit limits and write to a new scratch directory. No search
or Lean build was repeated solely to publish this record.

Authorship: opening_encoder developed the RBC/RCB extension of drop_contract's
RAB class; review_upstream_reflection independently reviewed it, and root
checked and published the evidence on 20 October 2026. These are follow-up
research deductions, separate from Sources141–143 and their delivered claims.
