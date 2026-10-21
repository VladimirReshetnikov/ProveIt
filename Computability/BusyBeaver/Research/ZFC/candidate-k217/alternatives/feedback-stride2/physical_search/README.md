# Round-three physical search: qualified negative results

No calibrated 214-state machine or new215-state machine is claimed here.

## Source-only improvement

`source200/source.sites.json` improves the received observed200 source from maximum eight consecutive zeros to seven, retaining200 distinct source DAG nodes and4,775 primitive occurrences; maximum depth is46. `source200/verify.py` independently checks the complete primitive word and guarded ordinal control-flow graph against the prior calibrated transfer source. Source hash is d70f4004ab7d579e8ce06f545bbe18654201cc3a7f3df10adc3a9e2f500461b0.

The owned closed-factor best-first search expanded3,000 accepted frontier entries and observed509,849 distinct proposals. The reported seven-zero source is a successful bounded source improvement, not a physical state bound. The existing scanner requirement remains unsatisfied. Moreover, an independently written row-protected allocation on this source costs222 states. The exact provisional table and allocation receipt are included; they passed literal decoder prefixes only, and are not runtime-calibrated. The215-state-budget solver was infeasible within its particular fixed-old-subtree/protected-row model, not globally.

## Contextual alias screens

Each input `folds/*/fold.in` contains a complete native table, its designated start, finite-window contexts and common-branch ordered pairs. The context invariant begins with every possible finite window at the designated start, and is closed under both possible newly exposed boundary symbols. Thus it applies to every initial tape, not only blank tape. `verify_contexts.py` independently checks the supplied inductive certificates and exact common-branch pair lists.

`fold_both.cpp` considers every ordered pair whose deleted state is not the designated start. Each retained read-symbol action is synthesized independently from both writes, both directions and all surviving working targets. It requires an exact one-step expansion of the old action, with complete finite-patch restoration outside the old write, within64 transitions and without interior recurrence to the merged state. Failure for one branch short-circuits the other. Its counts are candidate branch actions, not pairs of both actions. A return to the target endpoint is allowed before the no-recurrence check. No bound on arbitrary TM minimization follows.

Completed two-branch screens:
- Prior zero-spare transfer, width11:45,796 ordered pairs;39,514,672 branch actions; zero survivors.
- New MP-first transfer, width9:45,796 ordered pairs;39,512,960 branch actions; zero survivors.
- New zero-spare201 command ordering, width9:45,796 ordered pairs;39,507,824 branch actions; zero survivors.
- New ZR34/q50 physical encoding, width9:45,796 ordered pairs;39,512,960 branch actions; zero survivors.
- Provisional global-bias216, width11:46,225 ordered pairs;40,063,100 branch actions; zero survivors.

`fold.cpp` is a different family: preserve the common branch, synthesize the other branch, allow interior merged-state recurrence, and require exact one-step expansion within128 transitions. For global-bias216 its508 common-branch ordered pairs give436,880 actions and zero survivors. The provisional global-bias source/table itself is not independently calibrated by this screen.

Replay a width11 directory by compiling each owned C++ source with `g++ -std=c++17 -O3 -DRAD=5`; use `-DRAD=4` for width9. Feed the selected `fold.in` to the executable. Do not use a radius that disagrees with `FOLD_INPUT.json`. No precompiled executable is supplied.

## Scratch-biased return repair

The received scratch-biased215 source's return at100111 is CC3, which targets selector ordinal23 rather than source root. CC4 would return root; CB2 is an alternative root return with an ordinary carry/head shift. Its leaf parent62 is shared with256 other decoder prefix roles. The last unique ancestor is311 at1001; row311/1 enters62.

Owned finite screens tried all860 write/move/existing-target choices for row311/1, first preserving CI6 at100110 and requiring either CC4 or CB2 at100111. No action passed. A separate screen allowed CI6 fused with immediate root return; again no action passed. Changing62/1 alone likewise gave no action passing the CC4 fixture while preserving adjacent CI6. These are concrete zero-register/unit-spare representative screens, not impossibility results for multirow repairs or source relocation. None is called an all-natural proof.
