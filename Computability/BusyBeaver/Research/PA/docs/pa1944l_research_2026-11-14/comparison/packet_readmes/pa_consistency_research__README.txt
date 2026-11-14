PA CONSISTENCY MACHINES — RESEARCH AND VERIFICATION PACKET
13 November 2026

RESULT STATUS
No machine with fewer than 196 working states has been validated here.
The requested strict state reduction remains unresolved. The 195-state
table in data/rejected195.native.tm is a rejected candidate, not a result.
The report and supporting notes distinguish mathematical arguments,
executable symbolic certificates, finite checks, and kernel formalization.
No new Lean kernel proof is claimed.

WHAT IS NEW
* An exact 158-internal-node representation of PA196's 159-node source,
  retaining all 3,812 ordered instructions and every control-flow edge.
  data/source158.json has maximum depth 37 and maximum zero run 6.
* A different 158-node source, compiled into a validated new 196-state
  binary one-tape machine. Six contextual reader folds save one state;
  its eight-zero return scanner consumes that saving. The full table is
  data/variant196.tm (dense start 0, halt 196) and variant196.native.tm
  (native start 74, halt 254). It starts on the all-zero tape.
* All 4,959 symbolic instruction cases pass for arbitrary natural register
  values, every header gap at least 48, and all nonempty finite spare lists.
  All 392 transition rows are covered. Blank startup reaches the exact
  original clean frame after 59,164 transitions.
* A direct syntactic paper-level proof construction of the reverse PA
  consistency implication, supplementing the upstream one-way internal
  theorem. A transfer proof applies it to the new 196-state table.
* Counterinterpretations show neither membership-rewriting head is
  derivable from the other exact native rules and guarded gate.
* An exact symbolic check and proof-compiler argument for 5,760 variants
  obtained by reordering six heads and exchanging selected antecedents.
  These are logical/source variants, not 5,760 validated physical machines.

DOCUMENTS
report.tex / report.pdf: primary comparison and research outcome.
notes/internal_soundness.tex / .pdf: direct syntactic consistency direction.
notes/membership_independence.tex / .pdf: two exact counterinterpretations.
notes/regrouped196_validation.tex / .pdf: runtime certificate soundness,
  the repaired 196-state layout, and PA-formalizable halting transfer.
notes/axiom_head_permutation.tex / .pdf: permitted head permutations and
  antecedent exchanges, uniform stack selectors and refutation compiler.

REPRODUCTION
Run from this extracted directory using Python 3.10 or later. The core
checks require only the standard library. Keep assertions enabled: do not
use -O or set PYTHONOPTIMIZE. Each command below occupies one line.

python3 code/verify.py
python3 code/check_variant.py
python3 code/construct_variant.py
python3 code/reject_merge.py
python3 code/reject195.py
python3 code/check_membership_countermodels.py
python3 code/check_trace_bound.py --output certificates/variant196/trace_bound.json
python3 code/check_startup.py --machine data/variant196.native.tm --output certificates/variant196/startup.json
python3 code/check_runtime.py --machine data/variant196.native.tm --source data/variant196_source.json --gap 48 --states 196 --output certificates/variant196

The runtime replay takes about one to two minutes on the research host.
The startup/runtime checkers return a nonzero process status on failure.
construct_variant.py deterministically rebuilds the validated native table
from the literal source tree and six fold identities; no optimizer is
required. It writes rebuild/variant196.native.tm and verifies exact bytes.

For the separate emitter-variant packet, see search/head_variants/README.md and run its standalone verifier as documented.
Optimization replay is optional and may require scipy; verification of
the supplied witnesses and expressions uses only the standard library.
No bounded optimizer run establishes a state-count lower bound.

TABLE AND TAPE CONVENTIONS
Every transition row is: current_state read_bit write_bit L_or_R next_state.
The tape is two-way infinite, its alphabet is {0,1}, and it is initially all
0. Every working state has exactly two rows. The separate halt control has
no outgoing rows and is excluded from the working-state count. Native state
labels are sparse and their maximum is not the number of states.

IMPORTANT ARTIFACT DISTINCTIONS
* data/pa196.tm and pa209.tm are pinned upstream machines.
* data/u208_01.native.tm through u208_09.native.tm are the nine designated
  incoming outputs; they represent two rooted labelled-graph classes.
* data/source158.json is a geometry-safe source improvement. It is distinct
  from data/variant196_source.json, the compiled variant's zero-seven source.
* data/rejected195.native.tm fails the intended first-return instruction
  contract at source occurrence 1003. This does not by itself decide its
  eventual blank-input halting sentence. Exact counterexample tapes and
  replay code are included; it must not be cited as a verified PA195.
* certificates/variant196 contains actual replay results and affine timing
  certificates. The per-case JSON summarizes the derivations and affine durations; the
  verifier rederives the symbolic steps. A saved PASS flag is not a
  substitute for rerunning checks.

PROVENANCE AND LICENSES
Pinned commits, source hashes, archive identities and inherited notices are
under provenance/ and data/u208_inventory.json. Inherited notices retain
upstream relative paths and wording; provenance/README.txt explains this.
MANIFEST.sha256 fixes the exact distributed bytes. Newly prepared research
material asserts no additional licensing restrictions. Upstream licenses
remain attached to inherited material.

BUILDING PDFS
A normal LaTeX installation with pdflatex, lmodern, amsmath/amssymb/amsthm,
booktabs, geometry, xurl, hyperref, microtype, enumitem and fancyhdr is needed.
Run python3 build_pdfs.py. The PDFs are already included.
