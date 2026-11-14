U222: A BINARY BLANK-TAPE TURING MACHINE FOR Con(U)
28 October 2026

RESULT

The exact table machine/u.tm has 222 working states, 444 transition rows,
two tape symbols, one tape and one head, with no stay-put moves. It starts
in state 0 on an all-zero tape; its halt label is 222 and is not counted
as a working state. Initialization is included in the 222-state count.

The mathematical result proved in paper/report.pdf is

  PA |- not Halt(U222, blank) <-> Con(U).

Here U is exactly the equality-free, source-free unary power-covering
schema in the user's supplied pa_unary_power_cover.zip. The supplied
uniform interpretation theorem also yields PA |- ... <-> Con(PA).
This is 16 fewer working states than the specified 238-state benchmark.

The release supplies an ordinary mathematical proof, including uniform
finite proof translations formalizable in PA, and exact executable
verification. It does NOT supply a newly compiled Lean, Rocq, or MM0
kernel proof of this new literal-table endpoint. The old K215 theorem
does not automatically certify the changed machine. The runtime checker
is reviewed executable proof infrastructure, not a proof-assistant kernel.
The report identifies each inherited theorem and new obligation.

No absolute minimality is asserted. 222 is the smallest fully verified
construction obtained in this investigation. No unconditional assertion
of Con(U), Con(PA), or actual non-halting is assumed or proved here.

START HERE

  paper/report.pdf                 Mathematical construction and full table
  paper/report.tex                 Editable LaTeX source
  machine/u.tm                     Exact dense-labelled transition table
  machine/u.native.tm              Same machine with native compiler labels
  machine/state_map.json           Complete bijection between presentations
  machine/sites.json              Exact counter-program source
  machine/construction.json       Emitter and splice data
  machine/machine_summary.json    State count and exact SHA-256 identities
  evidence/reproduction_full.json Packaged full reproduction result
  evidence/runtime.json           Complete arbitrary-register check summary
  evidence/runtime_cases.json     All 5,060 individual case summaries
  evidence/startup.json           All 95,714 literal startup transitions
  evidence/bootstrap_independent.json  Independent replay of that startup
  evidence/source_audit.json      Independent formula/primitive/CFG binding
  references/theory_U/            Original supplied U report and artifacts
  references/logic/              Compact inherited proof excerpts and scope
  inputs/                        Frozen baselines and reconstruction recipes
  code/                          Standalone builders and verification tools
  NOTICE.txt and licenses/        Provenance and upstream license notices

TABLE FORMAT

The first line is '#! start 0'. Every following row is

  state read_symbol written_symbol direction next_state

Direction is L or R. No rows are defined for the halt state. The tape is
indexed by the integers and the initial head coordinate is 0. The native
presentation has the same 222 working states but uses halt label 254.
State labels are names; the largest native label is not the state count.

REPRODUCE

Python 3.10+ and its standard library suffice. No network, solver, external
repository checkout, or proof-assistant installation is needed.

  python3 reproduce.py

This validates the release hashes, reconstructs both machine tables and
the exact source, checks their bytes, independently binds the complete new
emitter to its primitive control flow, checks the state bijection, and
independently replays blank startup. Its finite macro test cases supplement
the uniform loop proofs; they do not replace them.

To repeat every arbitrary-register symbolic case:

  python3 reproduce.py --full

The full run takes several minutes. It treats all register values, the
extra gap, and the finite spare list symbolically. It checks all 5,060
cases, validates startup separately, and compares regenerated case results.
Its internal search limit bounds proof construction, not register values.
The reports are not a standalone proof trace of every symbolic event;
the checker, source and table reproduce those derivations.

The program writes temporary verification data outside the release tree.
An optional '--report /path/to/receipt.json' writes a chosen final receipt.
The original U diagnostics can independently be rerun from
references/theory_U using 'python3 -B reproduce.py'. They are finite checks,
not a proof of consistency or a substitute for the interpretation argument.

To rebuild the paper with a TeX installation:

  python3 code/build_document_data.py
  cd paper
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF bytes can depend on TeX versions and timestamps. The mathematical
content and machine appendix are generated from the exact delivered data.
Regenerating files changes the published SHA256SUMS; keep an untouched
release copy when auditing hashes.

KEY IDEA

Replace K215's large Theory K shell with a short unrestricted power-cover
shell, while retaining the original logical/proof-search interface. Use
the formula code itself as a fresh output-variable label, and fix source
and test roles to labels 0 and 1. Both exceptional codes 0 and 1 are proved
harmless. The selected source therefore needs no successor increment and
no runtime free-variable test. Uniform refutation translations connect
the machine-facing extension to U and PA.

The source has 3,891 primitive occurrences and 204 distinct subtrees.
The physical allocation is validated for every primitive case, including
context-sensitive arithmetic entries; decoder-prefix checking alone was
not sufficient for earlier rejected layouts.
