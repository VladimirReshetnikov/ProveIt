# Origin merge after phase seven

This merge preserves the complete checked phase-seven Lean checkpoint and the earlier verified Rocq production sources. The new batch-211 research placements and upstream compilation receipts remain preserved as provided; they do not extend the completed checkpoint.

The next Lean proposal is the representation-independent implication core from `e94206c09f`. Its two files total 22,278 bytes and 458 lines, versus 26,770 bytes and 454 lines for the checked pointwise proof. It reduces numbered helpers from 110 to 84 and proves the unrestricted row using only modus ponens, restricted rows and a reflexive relation closed under insertion into either implication operand. The private seed is a derived restricted instance. No truth, zero-collapse, decoding, injectivity or transitivity assumption is added. Source review found no mathematical blocker; the core and its adapter have not been kernel-checked here.

This is a substantive next checkpoint, with one extra project module. Adoption also needs a maintained source producer: the upstream canonical producer merely gains a superseded notice and still emits the old inline proof. The actual prototype is retained in [proof-core](../../proposals/proof-core/README.md). Its text-normalized input checks should become explicit byte-preserving provenance checks. The generic core can keep the shorter pointwise argument and omit the unused distribution derivation; it does not need the older 110-helper chain restored.

The [exact merge boundary](retained-production.json) keeps 21 existing production files and nine absences, including the unadopted generic module and coordinated Rocq changes. All new versions remain recoverable from the immutable upstream commit. The raw normalized-Rocq receipts describe that upstream source revision, while our maintained Rocq source/driver remains at the earlier checked boundary. No new Rocq compilation or delivered executable was run for this merge.

`merge.json` records source pins and unchanged upstream payload identities. `postmerge-saved-review.json` checks the maintained sources against the complete phase-seven primary evidence after resolution.

Some source paths named in the verbatim upstream Rocq receipts are intentionally absent from the retained production tree. Recover those files from the exact upstream commit recorded in `retained-production.json`; the receipts are not a rerun instruction for this retained revision.

A later [two-file seed-sharing proposal](seed-sharing-639e.json) from `639e34777e` is also merged as history with the checked production bytes retained. Its common bundle-semantics interface is queued for the next kernel check alongside the generic implication core.
