# Paired historical-parent AQ26 extension: toy-tested, not yet run on the real parent

This workflow extends an independently matched, frozen AQ29 parent with the
30 additions used by the successful AQ26 author-only run. The additions policy
is pinned by SHA-256 inside both the planner and preparer. Its 30 ordered
source paths, hashes, and declared imports, and its exact lists of all 79 axiom
reports in 22 modules, were independently compared with
[the previously recorded author additions](../author-additions.json), including
explicit empty lists for the other eight modules. The policy includes all 30
modules as planner targets, including checks outside the final target's import
closure. Both builders and the comparator enforce the report lists and reject
axioms outside `propext`, `Classical.choice`, and `Quot.sound` in every addition.
Identical forged reports in the two sibling logs do not satisfy the policy.

The freezer requires a strict historical source plan, a successful matched
parent comparison, and a separately observed successful parent coordinator
exit. It retains the exact frozen parent source prefix; added sources and both
Git histories are authenticated separately. Preparation rechecks the parent
and makes separate copies of each sibling's own objects; each sibling compiles
all 30 additions in its own environment. The comparison checks source, object,
direct input and companion identities, report contents, and sibling isolation.
It does not join separately compiled addition objects. A successful run would
establish a result for the **historical parent snapshot plus the pinned added
sources**, not for an arbitrary current workspace state.

The [toy control receipt](control-receipt.json) records five successful test
programs and five optimized-mode rejection controls: source/Git adversarial cases, per-module and immutable-policy tests,
a Git-backed freezer fixture, a paired real-Lean fixture, and an end-to-end
observed parent/freezer/extension fixture. The fixture programs substitute a
toy policy's digest only in copied tool scripts, or in the in-memory freezer
fixture; production scripts retain the real fixed policy digest. Controls cover
self-consistent policy-and-manifest removal of a nonterminal module or report,
matching forged sibling diagnostics (including a module expected to be silent),
source drift, output companions, hardlinks, and unobserved parent exit. These
controls use synthetic sources and a synthetic Foundation provider: they do
not establish the real AQ26 or AQ29 results. A manifest-only historical survey
found 1,209 parent modules and 30 additions; it did not check parent source
bytes or drift, and it cannot authorize freezing.

The controls also reject preparation paths inside the Foundation provider or
Lean toolchain before creating any output. The receipt from before this guard
was added is retained as [historical evidence](control-receipt-before-overlap-fix.json).

No real extension has been prepared or run by this workflow. Do not start one
until the real AQ29 parent pair has completed successfully and its coordinator
exit and stdout have been observed and recorded. The parent and provider's
existing evidence retains its own limitations: the outer Foundation wrapper
exit was not observed, and package-transitive dependencies, dynamic loads, and
transient mutations are not fully authenticated by these direct-input guards.
A Lean build and these controls are evidence about the stated Lean artifacts;
they do not themselves prove the requested internal PRA proof exists.
