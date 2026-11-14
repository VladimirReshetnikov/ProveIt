BOUNDED STATE-REDUCTION RESEARCH

Pinned source revision: VladimirReshetnikov/ProveIt@17f92105e2bc4317feae6c219cb2143437b482ff.

RESULT
No machine below 194 states was certified. The main package supplies PA194R, a 194-state reassociation with a new control graph of PA194F, recovered from one of the saved plateau grammars. Its builder and full machine certificates are outside this optional search directory. No negative search result here is a minimality theorem.

QUICK REPLAY
Python 3.10+ and a C++17 compiler suffice; no network is used. From any directory:
  python3 reproduce.py positive
This compiles the new quotient synthesizer, reruns the 201-control positive control, and confirms that all seven previously certified AX fold pairs are found (eight row-pair solutions because one fold has two implementations). This portable replay was executed successfully.

OTHER SUITES
  python3 reproduce.py quotients
  python3 reproduce.py parameters
  python3 reproduce.py anneal --seconds 360
  python3 reproduce.py layouts
Use --output DIR to choose a separate replay directory. Compilation and all new outputs go there. The published input tables are hash-checked before a run. The anneal command runs three budgets sequentially; the original three runs were concurrent, so wall-time-limited proposal counts will differ on another computer.

EXACT COVERAGE
coverage.json is the authoritative coverage receipt. logs/ retains complete recorded output.
* Sixteen bounded quotient screens are reported, including seven distinct native 194-state input tables, the new source compositions, two inherited universal symbolic context sets, two-sided convergence, and entry-bit/head-displacement encodings. All returned zero quotients.
* The encoded joint-convergence run on the CS entry-zero input completed 114,835 relations, 146,189,864 first-action trials, and 631,747 complete row-pair checks, with zero results (radius 4, 100 steps per side).
* Four final-zero endpoints, two AX frontier shapes each, and 46,656 independent six-head variable-role assignments per shape gave 373,248 parameter-screen cases. Every best count remained 194.
* All 9! = 362,880 physical register layouts were screened on one frozen AX grammar; the best count remained 194.
* Three final occurrence-aware anneals completed 360 seconds each. Final dec3: 5,634,864 proposal slots; dec4: 5,585,517; dec5: 5,683,487. Total 16,903,868. All best scores were 60 effective AX readers, hence 194 working states, and no sub-194 output was produced. The fixed input controller includes the separately verified entry-zero test on register 6.
* Earlier anneals were interrupted when effort moved to changed final-zero words. Their receipts report lower bounds from the last complete progress lines, never completed-budget counts. Mutation counts include duplicates and no-ops and do not count distinct machines.

WHAT THE NEW QUOTIENT CODE CHECKS
joint_return_merge.cpp synthesizes both rows of a retained control and identifies a removed control with it. Unlike the earlier independent-row screens, its candidate may revisit the changed retained control internally. One assigned row is filtered until a trace needs the still-unassigned row; the surviving two-row assignments are then checked together on every required context. The result must reproduce one parent transition.
joint_convergence.cpp allows the parent and candidate each to advance a positive bounded number of steps before joining. It also permits an action directly into halt.
joint_encoded_convergence.cpp additionally permits the two-cell head displacement and entry-bit toggle relations when all external arrivals to the removed control have one direction. Incoming actions and the endpoint encoding are changed consistently.
The initial finite abstract window is all zero at native start 74. Each shift admits both values of a newly exposed boundary bit, so the closure overapproximates every blank run. Supplied symbolic contexts are inherited research inputs; their generators and proof discussion are in the source archives identified by context_manifest.json. Their derivation is not re-certified here.

PROOF BOUNDARY
The sufficient finite positive-progress simulation lemma is stated in joint_quotient_lemma.tex. A numerical search hit would still need a standalone universal certificate, source binding, exact initialization, and the arithmetic calibration. No such hit occurred. Bounds exclude longer joins, larger windows, more changed controls, and other tape encodings. The input graphs include research compositions; accepted consistency-machine status is given by the main report, not inferred from a filename or a search score.

PROVENANCE
The three joint quotient synthesizers and the portable replay/receipt code were written in this research. screen.cpp and the annealing implementations are adapted from the attributed PA194 research packets, with their license files preserved in licenses/. Their original locations are documented by the pinned repository's PA/docs and incoming packet READMEs. prepare_seed.py regenerates syntax inputs from an explicit table and grammar; prepare_parameter_seeds.py regenerates the frozen per-head parameter inputs. The source tables, grammars, context sets, and resulting input hashes are included.
