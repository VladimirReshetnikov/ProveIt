# Independent review of the selected simplification

Reviewed against pinned ProveIt commit `b17dd5487f34adea473a0204c5320fb3eeb8910e`.
This is a same-session independent assistant review, not external peer review and not a proof-assistant verification of Python.

## 1. Direct-Q progression: approved mathematical equivalence

The replacement in `analysis/direct_closure_progress.md` is correct.

The new primitive rule is `Gamma,E(z) |- E(S z)` implies `Gamma |- Q_y E(y)`, restricted to literal equations. The old D-progress rule derives it using an unused witness coordinate, D-progress with witness zero, D-elimination, and the returned Q hypothesis. This construction is already in the pinned source as `NPrf.qIProg` in `NativeEq.lean`; the report should attribute that fact explicitly.

Conversely, an old D-progress premise `Gamma,E(t,z) |- E(t,S z)` yields `Q_y E(t,y)` by the new rule. Under `E(t,0)`, Q-elimination gives the successor instance, so D-case with witness `t` gives the old conclusion. The witness is fixed during the Q-progress application, and the inherited freshness condition ensures that it does not contain the progression eigenparameter. Renaming local eigenparameters before weakening makes the construction capture-free.

Both transformations preserve all final terms, formulas and retained contexts. No arithmetic, equality, domain or ordinary logical connective is reinterpreted.

## 2. Proof-tree bounds: approved with the stated metric

Counting every primitive inference, including Hyp, as one node:

* A Q-progress node becomes D-progress, D-elimination and Hyp: `N+2r <= 3N`.
* A D-progress node becomes Q-progress, Q-elimination, Hyp and D-case: `N+3r <= 4N`.

The old premise proof is inserted once. Weakening and renaming are admissible structural transformations and do not create counted primitive nodes. These are proof-tree node bounds, not certificate-byte, runtime, source-size or formula-size bounds. Optional compound Q-case rules would need their own overhead accounting if included in the formal primitive calculus.

## 3. Inheritance of iPRA equivalence: approved, subject to accurate verification claims

Identity-language consequence equivalence transfers the pinned baseline's native/ordinary bridge and its ordinary whole-domain iPRA bi-interpretation. In particular, the actual numerical equality and the numerical composite graph `x=y` remain unchanged. Translating the designated contradiction `0=S0` in both directions gives equiconsistency.

The pinned source contains `NPrf.iff_teq` in `NativeComposite.lean` and `biInterp`, `teq_iff_pra`, `pra_iff_teq`, and `teq_consistent_iff` in `BiInterpretation.lean`. This review inspected these declarations; it did not independently build their full dependency closure. A report may cite the existing formal development and identify any new Lean verification separately, but should not present the Python checker as formally verified because the source theory has a Lean development.

The direct rule is sound in the ordinary theory by contextual equation induction under a temporarily assumed base. It is essential to keep the literal-equation restriction. Compound induction would change the strength.

## 4. Structural simplicity: modest, defensible, not a global minimum

The new interface separates witness choice (D-case) from equation induction (Q-progress). Progress no longer carries a redundant existential witness, and D-introduction has only its case form. This is a defensible conceptual simplification.

The total count of primitive inference schemas is unchanged. The direct-Q rule was already a derived theorem. Therefore this is a choice of simpler primitive interface, not discovery of a new induction principle or a new arithmetic basis. No absolute minimality follows.

## 5. Wrapped-source checker: 528-byte candidate is NOT yet approved

The inspected `slice_bytes.py` has 528 normalized bytes, 269 significant tokens, 311 AST nodes, and 333 raw gzip-level-9 bytes in the available runtime. The 529-byte baseline has 266 tokens, 310 AST nodes and the same 333-byte gzip size. Those provisional counts cannot establish a complete-checker improvement until completeness is repaired.

The intended successor-side change is sound in isolation: for a nonempty source list `s`, `s[:1]` constructs `[s[0]]` and the recursive call uses `s[0]`. Extra tail entries are ignored annotations. A successful computation source must be a list, since scalars/dictionaries cannot be sliced and relevant string entries fail numerical opening.

The base-side change introduces a real canonical-completeness obligation. Empty `s` now gives the numerical zero spelling `[]` in the base computation equation, while the inherited Q/D logical zero instances are filled with `False`/scalar `0`. Python does not identify `[]` with `0` in raw proof matching. A semantic decoder interpreting both spellings as zero is a soundness statement, not a proof that every canonical native theorem has a certificate.

Changing the canonical zero to `[]` alone does not fix this: the common introduction continuation still supplies the scalar-zero instance. A derivation of the alias equation `0=[]`, or a complete encoding/normalization proof, is needed. No such derivation was established in this review. Do not deliver the 528-byte candidate as complete on finite tests alone.

The variant `s and s[:1]` preserves scalar `0` for canonical base packets and uses `[n]` for canonical successor packets. That costs 533 bytes in the reported source and avoids this specific gap, but does not beat the 529-byte baseline.

## 6. Scope and trust boundary for any finalized compact checker

The full measured program must include JSON loading, traversal/opening, scope management, arithmetic supply, every logical branch, and the acceptance output. Producers, measurement scripts and regression tests may remain untrusted, but a mandatory executable certificate translator may not be omitted from the measured trusted boundary if the checker depends on it for soundness.

The inherited soundness argument depends on sorted decoding of surplus arities, semantic opening, persistent contexts, old-floor validation before allocating a fresh parameter, and the zero-instance supply lemma. A generated computation assumption at a fresh parameter need only have a known simultaneous zero instance; it is not necessarily a uniformly true arithmetic equation. Fractional fresh aliases must all be zero-substituted, as the inherited proof explains.

Negative controls should exercise compound-induction rejection, future-witness capture, and context leakage. Finite tests are evidence that these branches are exercised; they do not replace universal soundness or completeness proofs.

Finally, `slice_bytes.py` implements witnessed D-progress, not direct Q-progress. Even if a repaired version becomes smaller, attribute its size gain to the separate certificate representation change. Do not claim the direct-Q primitive replacement caused that size reduction.

## Overall assessment

Approve the direct-Q progression presentation and its exact two-way derivation theorem as a modest structural simplification. Approve transfer of the inherited whole-domain bi-interpretation and equiconsistency with explicit provenance. Withhold approval of the 528-byte checker as complete pending the zero-alias obligation. Keep rule-interface and implementation-size results separate and report all size-coordinate tradeoffs.

## 7. Final strict checker audit: approved

The finalized proposal replaces the compact-alias experiment with standalone, explicitly sorted and scoped checkers `strict_old.py` and `strict_q.py`. I independently inspected both modules and `translate.py`.

Reviewed SHA-256 hashes:

* `strict_q.py`: `793cc66da356e2586b66ef21d8f2ac1928503b96cf8bd49a280049f6c8962851`
* `strict_old.py`: `4a3811374119363cadfc54d5b87e9332df55272d837f4dade0260b3ba196ebf0`
* `translate.py`: `e2066dbc76fa2406c8073f34966d00505aa65917fa1e827bedbf66ec9f1da2da`

No correctness issue was found. The public `check` entry point validates every context formula and the requested goal at the declared scope. Every inference validates its supplied terms/formulas with exact sorts and arities, checks major-premise roots where necessary, and checks the exact expected subproof conclusions. Variable and hypothesis indices use `type(index) is int`, excluding Python's Boolean/integer alias. Fresh variables are represented by adding a de Bruijn index, shifting every retained context formula, and validating final conclusions and witnesses in the original scope. Contexts are never mutated in place.

The substitution/lifting definitions correctly preserve variables below binders and shift substituted free variables. In particular, `witness_instance` removes the existential coordinate while retaining the induction coordinate, and DE places the opened Q formula over exactly one new free numerical variable. The old-to-new translator weakens the new Q proof into the D-case context using simultaneous numerical/context substitution. The reverse translator inserts an unused existential coordinate and discharges it by DE. These are executable versions of the written proof transformations.

The universal checker theorem follows by induction on successful proof evaluation, maintaining valid scoped formulas and derivability. Conversely, each finite derivation is serialized by its inference constructors. This is a written mathematical correctness argument for the abstract algorithm, not a claim of proof-assistant verification; physical Python recursion and memory limits can reject sufficiently large valid certificates.

Independent supplemental script `analysis/strict_audit.py` produced:

* 145 malformed-input and scoping rejections, including Boolean/float/negative/out-of-range indices, wrong term/formula roots, extra/missing constructor and rule arguments, future-witness references, and retained-variable capture.
* 36 successful translation/round-trip checks, with parameter-bearing proofs nested under up to eight case/DE layers. The DE branches actually use their opened closures. Exact node-growth formulas and unchanged goals were checked.
* Zero failures.

These are bounded regression results, not the universal proof. The comparison is appropriately controlled: the two standalone modules share their parser, syntax, substitution, context handling, common rules and driver, and differ only in their progression-rule implementation (plus a docstring label removed by normalization). Their measured differences are 83 fewer normalized bytes, 18 fewer significant tokens and 21 fewer AST nodes for direct Q. Normalized gzip grows by 19 bytes; raw gzip grows by 20 bytes. This supports a modest simplification in a matched straightforward implementation. It does not beat the repository's 529-byte compact checker, and no such frontier claim should be made.
