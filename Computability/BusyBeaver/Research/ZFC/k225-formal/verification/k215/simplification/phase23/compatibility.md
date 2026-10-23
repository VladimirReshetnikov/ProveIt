# Phase23 compatibility notes

**The selected compatibility and exact-profile checks pass.** The reviewed
boundary includes forty intentional declaration retirements and three stronger
theorem types; it is not a promise to preserve the removed APIs.

## Generic Core and facade imports

The retained generic declarations keep their namespaces and names in `FiniteSetsCore`,
`SingletonInfinityCore`, `InductiveAttemptsCore` and `WellFoundedPartCore`.
The existing `FiniteSets`, `SingletonInfinity`, `InductiveAttempts` and
`WellFoundedPart` modules remain as import-compatible quotient adapters. Generic
consumers may import a Core file without importing the CP/GIC quotient lane.
Compatibility consumers continue to import the facade. No blanket claim is made
that every historical helper declaration remains available.

Phase22's stronger tagged/quotient signatures and four underscore witness spellings
are preserved. In particular, the upstream `KQ1Basic` deletion is merged while
retaining `interpreted_pair`'s `_witness` binder. `KLowerQHyp` keeps the reviewed
premise omissions and current call arities.

## Intentional declaration retirements

The upstream cleanup removes these 29 ordinary theorems. Its maintained-source
and fifteen-client census found no caller; the deleted items carried no implicit
simp attribute. Unknown external clients naming one must migrate or retain the
historical source. These removals are not an API compatibility promise.

| Module | Retired theorem names |
|---|---|
| `ConstructibleAbs` | `bitEq_iff` |
| `DeepPositiveClosure` | `valid_pscForm_iff` |
| `FiniteSetsCore` | `succ_self` |
| `InternalOrd` | `sub_of_le` |
| `InternalRank` | `nsat_powF` |
| `KEind222` | `th_neg`, `th_ex`, `th_luk` |
| `KLowerRel` | `sh_ne` |
| `KLowerTag` | `tag_power` |
| `KQ1Basic` | `quotient_empty_form`, `quotient_singletonClosed_form` |
| `KTableCore` | `agree_of_agreeB` |
| `KTape` | `sepsL_app` |
| `KUpper222` | `rsat_powBody` |
| `KZip` | `zl_nil` |
| `NamedZF` | `nsat_congr` |
| `PositiveClosure` | `point_seed_reflexive`, `subset_seed_reflexive` |
| `ProfileAxioms` | `member_right_iff` |
| `ProfilePairs` | `classMember_left_congr`, `singleton_object_congr` |
| `RMEquiv` | `incPath_nil` |
| `SingletonInfinityCore` | `index_formula_induction` |
| `TarskiDerived` | `contra_rev`, `b_axiom` |
| `TupleOrder` | `tup_val`, `tup_dom` |
| `WellFoundedPartCore` | `wf_closure_of_equalityFree_gic` |

Native Replacement also removes six public raw helper names from `KQ1Replacement`:
`replacementChoiceForm`, `equalityFree_replacementChoiceForm`,
`sat_replacementChoiceForm`, `replacement_instance`, `interpreted_replacement`
and `quotient_relOf`. Their exact raw source is retained as historical data.
There are no references outside the obsolete helper chain in maintained sources
or any of the fifteen accepted clients, nor in selected reports or attributes.
The surviving `replacementRename`, `quotient_replacement` and `quotient_repl_form`
retain their original types. The original global `Functional` hypothesis on the
quotient endpoint remains; retiring the raw helper with its partial-functionality
premise introduces no new assumption into the surviving endpoint.

The direct attempt extension also retires five `InductiveAttempts` APIs:
`HasAttempt`, `attempts_exist_of_separator`, `hasAttemptForm`, `sat_hasAttemptForm`
and `existence_separator`. The now-unnecessary existence cut has no maintained
external or accepted-client caller, and no selected report names those helpers.
Their exact source remains historical data. No compatibility promise is made for
these removed names.

The forty retired declarations are proofs or formula helpers, not retired
modules or producers. All retained quotient facade consumers remain selected.

## Three stronger signatures

Both `Tarski.gam_list` and `gam_complete` drop the forced section arguments
`hC : Classical NF.imp NF.bot (Thm Ax)` and `hz : Cons Ax [neg f0]`. Their statements
and proof bodies do not use either premise. Explicit argument sequences change as
follows; implicit `Ax` remains unchanged.

| Theorem | Before | Candidate |
|---|---|---|
| `gam_list` | `hC f0 hz L hL` | `f0 L hL` |
| `gam_complete` | `hC f0 hz g` | `f0 g` |

The four maintained callers are `gam_consistent`, `gam_closed`, `gam_imp_iff`
and `gam_rich`. The recursive `gam_list L ...` reference is unchanged. The scoped
`omit` leaves the section's inclusion policy unchanged for all other theorems,
and those four callers still use their required `hC`/`hz` elsewhere. External
applications passing the removed arguments, including named `(hC := ...)` or
`(hz := ...)`, must be updated. No external maintained or typed-client reference
was found.

`InductiveAttempts.closure_of_instances` also drops only the `hEx` existence-cut
premise. Its conclusion and other premises remain exact. The sole maintained
caller, `closure_of_forms`, no longer supplies `existence_separator`; its public
type is unchanged, as are `successor_closure` and
`ordinary_infinity_of_container`. External positional or named `hEx` applications
must remove that argument. The source census found no external maintained or
accepted-client use. The one-Separation/one-image proof chooses a base attempt
and directly extends each recorded image witness, so it does not need an
attempt-existence set for every index.

The four anonymous `memD` lambda binders are internal parameters to
`Quotient.lift₂`, with no public named-argument change. KZip's sole additional edit
removes an unused simp argument; its old unused `zl_nil` theorem was already
removed by the attributed upstream cleanup.

## Accepted compatibility checks

All fifteen accepted client source hashes remain unchanged. Fourteen compile
fresh and one reuses its exact phase22 binding. All 93 client reports, five
WFTheory reports and ten endpoint-audit reports retain exact profiles. All 230
provider logs and both audits have zero warnings. The
[independent actual readback](lean/result-review.json) verifies these bindings.

The [source peer](integration/source-peer.json) preserves its source-review status
from before the full run completed. Its three stale mathematical-diagnostic
size fields are disclosed; the diagnostic is not a full-run basis, and the final
full plan matches the actual source bytes and lines. The accepted terminal and
capture receipts establish the current checkpoint without rewriting that history.

The four Core modules add no replacement axiom or alternative foundation. Native
Collection remains indexed by actual formulas, its global support-domain guard
is retained, and no totality premise is added. Machine data and halting/nonhalting
statements keep their existing scope. Internal PA and minimum-state claims remain
open. Phase22's eleven Lean leaf files remain immutable external evidence. The
[future control lead](leads/README.md) is uncompiled and outside these checks.
