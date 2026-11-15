LOGICAL AND COMMAND-PROTOCOL RESEARCH; INDEPENDENT ORH AUDIT
=========================================================

This directory contains an independent audit of the delivered PA194ORH
machine, unsuccessful attempts to reduce the state count, and a checked
195-state experiment with a different successful modus-ponens protocol.
The 195-state experiment is auxiliary; it is not the principal result.

Reading order
-------------

research_notes.tex describes the explored logical transformations, the
successful-MP alternatives, precise negative-search scopes, and comparisons
with the repository's ZFC, DiophantineConsistency and ConciseIPRA projects.
ORH_audit.tex proves the new machine's history-selector trace identity and
explains the independently checked source control flow. Both are TeX
fragments intended for the main report.

ORH_audit.py and ORH_audit.json
  Independent checker/receipt. It imports no construction compiler or
  symbolic executor. It proves the two local history cases by literal TM
  traces, checks four closed-macro dispatch paths, verifies unchanged rows
  at all 23 register-box controls, and independently resolves all 3,671
  source instructions by lexicographic subtree intervals. It finds exact
  instruction-list equality and 134 changed source addresses.

mp_tail_words.py and mp_tail_words_receipt.json
  Free-term command calculations for DD, HD, DH and SP. Besides push/pop,
  erase and the zero aliases, it checks all ten axiom selectors, theorem-only
  generalization, the dominated-rho selector, and MP proof-compilation
  suffixes at conclusion 0, conclusion 1 and an arbitrary other conclusion.
  SP is the direct stack-result protocol used by the 195-state experiment. Its
  MP cleanup needs the reserved zero used by the proof compiler. These
  algebraic checks alone are not a literal-table simulation or a Lean proof.

build_stack195.py, stack_result195.native.tm, stack_result202.raw.tm,
and stack195_checked/
  Reconstruct the auxiliary SP table, apply the seven inherited local
  folds, check all 4,780 arbitrary-register symbolic source contracts and
  exact complete blank initialization, and produce a dense 195-state table.
  The completed replay reaches the frame in 58,154 physical steps.
  The symbolic maximum 497 and total 1,479,348 count symbolic executor
  transitions; they are not uniform physical-step bounds.

contraposition/
  Search over 416 new initial trees with negative presentations of ordinary
  heads 3, 4, 6. The first head is retained, so its finite explosion bootstrap
  is still available. A 300-second run made 4,294,014 proposals and found
  best optimistic reader score 65. Compatibility is checked only for an
  optimistic score at most 64; no physical 199-state table is claimed. New h1
  modal variants were not included in this run.

DD/, HD/, DH/
  Each directory has its adapted search source, frozen 49-seed input,
  attributes, author log, and ten selected final grammars. Each 180-second
  run reached compatible reader score 60, hence a prospective 195 states
  with 135 fixed controls. Each parameter screen then tries exactly 10
  selected shapes times 6^6 head-parameter permutations: 466,560 cases per
  family, with no score 59. The complete parameter input is frozen as
  parameter_seeds.txt; it embeds the fixed machine rows as well as all
  annotated grammar DAGs. The .best/.hits/.audit/.seeds files and logs are
  retained. Only the independently constructed SP 195 table is physically
  validated here; these search scores are not physical-table claims.

Reproduction
------------

Commands below assume the shell's current directory is this directory.
Python 3.12 and a C++17 compiler are sufficient. The Python calculations use
only the standard library. No network, Lean installation or repository
checkout is required for these local replays.

  python3 ORH_audit.py
  python3 mp_tail_words.py
  python3 build_stack195.py --output replay_stack195

The ORH checker defaults to ../../machines/PA194ORH and
../../reference/AX11H_machine. Paths can be replaced with --packet and
--parent, and its output receipt with --output. The 195-state build compares its
literal raw and folded bytes to the retained tables before writing results.
Its default output is replay_stack195, preserving stack195_checked/.

For an exact finite parameter screen, for example DD:

  g++ -O3 -std=c++17 DD/parameter_screen.cpp -o /tmp/pa194-DD-screen
  /tmp/pa194-DD-screen DD/parameter_seeds.txt /tmp/pa194-DD-replay 10 46656 compatible

Use HD or DH in place of DD for the other two screens. The final argument
enables simultaneous-compatibility checking. Outputs go to the supplied
prefix; use a new prefix to preserve the retained author records.

For a new stochastic grammar-search run:

  g++ -O3 -std=c++17 DD/search.cpp -o /tmp/pa194-DD-search
  /tmp/pa194-DD-search DD/seeds.txt DD/leaf_attrs.txt /tmp/pa194-DD-new 180 2026111419

For the contraposition search, substitute contraposition/search.cpp,
contraposition/seeds_newlogic.txt, contraposition/leaf_attrs.txt, a new output
prefix, 300 seconds and seed 20261114181. The family seeds are 2026111419
(DD),2026111420 (HD),2026111421 (DH). Search stopping is by elapsed time, so
the number of proposals can differ on another computer. An optional final
argument limits proposal count. Recorded counts are 4,294,014 for
contraposition; 1,150,813 for DD; 1,244,403 for HD; 1,067,950 for DH. The fixed
parameter screens do not depend on a time cutoff.

Scope and provenance
--------------------

All negative results concern exactly the stated seeds, transformations,
grammar shapes and fold mechanism. They imply no global minimality bound.
An executable finite audit does not constitute a new kernel-checked Lean
proof of the absolute iPRA equivalence.

research_sources.txt gives the pinned repository commit and exact source
paths. Imported files below reference/ retain their original contents and
upstream provenance/licenses. The 195-state builder uses the original AX11
primary compiler, symbolic executor and table utilities with explicit local
inputs; the default external-reference functions in that compiler are
overridden before use. The command calculation imports only free-term
operations from the retained ax11_commands.py. These inherited files are
not represented as independently authored implementations.

The search.cpp/screen.cpp/score_seeds.cpp files are adapted from the
AX11H packet's research/joint_grammar/joint_ax11 implementation. Changes
disable parameter mutations in the local rotation runs, install the
protocol-specific two-macro sharing rule, and set the target score.
The separate parameter_screen.cpp re-enables explicit enumerated parameter
choices through its frozen annotated inputs. No claim of novelty is made
for the inherited optimization algorithm itself.

ORH_audit.py, build_stack195.py and the protocol-specific command model
were written for this investigation. The ORH checker deliberately uses an
independent control-flow resolver. The top-level report and the machine's
complete inherited proof packet supply the larger correctness context.
