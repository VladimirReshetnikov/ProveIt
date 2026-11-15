# Research index

These directories preserve the construction searches and unsuccessful attempts
to reduce the state count. **No accepted blank-start machine below 194 working
states was obtained.** The joint forest search did produce the 194-state
families from which the three independently verified delivered machines were
selected. None of the negative results is a 194-state lower bound.

| Directory | Contents | Start here |
|---|---|---|
| [lowlevel](lowlevel/) | Whole-source merges and bypasses; interval invariants; expanded Runtime193 initialization searches; finite-window quotients of ForestX; general two-row endpoint synthesis. | [README](lowlevel/README.md), [structured results](lowlevel/search_summary.json), [quick replay](lowlevel/quick_replay.json). |
| [source_math](source_math/) | Source-level AX transformations, including redundant axiom heads and truth-head padding; preservation arguments and grammar searches. | [README](source_math/README.md), [summary](source_math/summary.json), `padding_preservation.tex`. |
| [joint_forest](joint_forest/) | Joint associations of operand, MP, and loop routines with AX sharing; archived candidate tables and receipts; additional ORH reduction searches. | [README](joint_forest/README.md), `reference/global_associations/summary.json`. |

## Completed results

The joint forest enumeration covers 250 families. Seventy have a nominal
194-state budget, and 63 pass the construction checks. Of those, 62 are new
under the comparison used in the main report; the remaining graph recovers
the incoming ORH machine. This is a construction-search result, not 63 new
independently verified absolute consistency theorems. The three tables in
`../machines/` have the additional literal physical verification and written
proof described in the main report.

Truth-head padding reaches a best nominal count of 195 in its recorded search.
The corrected search on the original source reaches 194. The source-math
experiments do not produce a validated sub-194 result.

For the primary machine, the low-level whole-instruction searches test 57,460
inherited-row merges, 111,168 one-free-row merges, and 67,936 sole-ingress
bypasses, with no hit. The same domains are repeated using checked source
interval facts, again without a hit. On ForestX the corresponding counts are
57,460, 104,992, and 67,936. These symbolic source checks permit different
intermediate control traces while requiring the correct complete instruction
outcomes.

Expanded bootstrap searches on the primary and ForestX 193-state runtime
cores process 6,230,979 computations and 25,963,703,422 literal transitions.
They cover up to five edits from native start 74 and up to three edits from
every existing start control. No complete admissible source frame is found.
The recorded classifications distinguish finite halts, exact cycles, proven
outward rays, and unresolved cutoffs. These totals count computations, not
distinct machines; the search domains overlap.

Fresh ForestX quotient searches at radii four and six each test all 18,721
control pairs, finding no quotient. A broader instruction-endpoint discovery
screen on the primary machine tests 1,770 reader pairs and 45,184,860 joint
row choices, also without a hit. Its padding-zero and finite-window restrictions
are stated explicitly in the low-level README.

The joint-forest directory additionally retains the ORH screens: 680 local
merge attempts, 110,396 one-free-row trials, and 67,164 bypass trials, with
no accepted reduction. Consult each receipt for its exact domain and bounds.

## Verification scope

The low-level Runtime193 files implement their source from initialized frames;
they are **diagnostics, not blank-start consistency machines**. Symbolic search
certificates use their declared register interfaces. Finite samples, failed
symbolic closure, and time cutoffs are not promoted to universal impossibility
claims. The independent literal checks for the delivered 194-state machines
are maintained separately under `../verification/` and their machine folders.

Reproduction commands, frozen inputs, attribution, and hash manifests are in
each directory. Run the low-level quick replay with Python 3.10+ and assertions
enabled; the larger search replays are optional and may take several minutes.
