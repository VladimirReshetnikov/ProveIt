PA-CONSISTENCY TURING MACHINES: COMPARISON AND REDUCTION RESEARCH
13 November 2026

STATUS

The strict requested target has not been achieved. This archive contains no
accepted blank-start PA-consistency machine with fewer than 196 working states.
It contains three new complete 196-state diagonal-calculus layouts and reproducible research
that distinguishes those positive results from failed smaller candidates.

START HERE

  report/report.pdf
  report/report.tex and report/sections/*.tex

The report gives the pinned comparison, the new constructions, the written
PA-calibration argument, the exact status of the experiments, and the complete
dense diagonal196 transition table. The top-level SHA256SUMS binds every file. RESULTS.json records the status
and principal counts in machine-readable form. Check hashes before replaying
scripts: some scripts regenerate receipt files and elapsed times.

ACCEPTED NEW TABLES

  axioms/diagonal196/machine.tm
    196 working states; 392 rows; initial state 0; separate halt label 196.
    191 AX macro items; 3,700 source sites; 4,815 complete instruction cases.
    Exact blank startup: 58,154 steps.
    SHA256 59bbe3dbe040de4903b7f9b4fb64f70642757c54849e921a44af29145d625b0c

  axioms/separate196/machine.tm
    196 working states; 392 rows; initial state 0; separate halt label 196.
    190 AX macro items; 3,673 source sites; 4,780 complete instruction cases.
    Exact blank startup: 58,154 steps.
    SHA256 61ffdfea87d204cfb879ffb78fb1c9c47f425fdb53771995a40dbe0f0c9c3e28

  axioms/search/scanner_best196.tm
    196 working states; 392 rows; initial state 0; separate halt label 196.
    190 AX macro items; 3,673 source sites; 4,780 complete instruction cases.
    69 AX readers and 7 compatible folds above the 134-control base.
    Exact blank startup: 58,294 steps. Six internal short-scanner obstructions.
    SHA256 bccb07e7da72d96806ab325cb321a88f28cdf0c14bfa87f9efd5e1a7d418c10a

All use a binary, single, two-way infinite tape initially filled with zero.
Each row is: current-state read-symbol write-symbol direction next-state.
Directions are L/R and each move is one cell. No transition is defined at halt.
Native-labelled versions and bijective dense maps are included.

The diagonal-vacuity calculus was already present in the supplied incoming
research with a 199-state implementation. The new physical layouts reduce it
to 196. Separating its diagonal clause as an extra head shortens the emitter
by one further macro item, with the same physical state count.

QUICK REPRODUCTION (Python 3, assertions enabled)

  python3 axioms/verify.py
  python3 catalogue.py
  python3 comparison/comparison/compare_designs.py --output comparison_replayed.json
  python3 comparison/scanner196/verify.py comparison/scanner196 --startup 150000
  python3 allocation/verify_hall.py
  python3 engine/reproduce.py
  python3 engine/reproduce_trit.py
  python3 engine/check_scanner195.py

For the third diagonal-calculus layout:

  cd axioms/search
  python3 export_scanner.py scanner_6 scanner_best196
  cd ../..

The axiom verifier uses only Python's standard library. It regenerates the
literal tables, independently checks complete macro control-flow bindings and
free-algebra emission, verifies every symbolic instruction contract, and checks
the full finite startup tape. The default engine command compiles C++ positive
controls; its --full option reruns the completed synthesis screens.

DIRECTORY GUIDE

  axioms/      Three accepted new 196-state layouts and their verification.
  comparison/ Pinned supplied designs, comparison, scanner layout, hybrid work.
  engine/      Local and head-offset folds, invariants, contexts, run receipts.
  allocation/ Fixed-reader allocation model and three finite Hall obstructions.
  report/      Complete LaTeX report and compiled PDF.
  catalogue.json and catalogue.py
               All 37 supplied table entries and their 30 graph classes.

REJECTED EXPERIMENTS

The 196-state U208/PA196 hybrid passes all 4,957 arbitrary-value source-frame
contracts, but every choice of existing blank initial control reaches an outward
blank loop. It is not a valid blank-start consistency machine. Its 197-state
prefix repair passes a finite startup check but fails a full runtime contract.
Other raw grammars or optimistic 195-state counts are not accepted machines.
Read each local README and receipt before using an experimental transition file.

The literal 195-state short-scanner edit has 96 failed unrestricted branch
obligations and also fails the stronger invariant-conditioned certificate.
From the intended exact clean seed its first root return, after 118 steps,
differs in 43 tape cells from the required successor. This disproves the stated
clean-frame implementation contract; it does not by itself decide the edited
machine's actual blank-tape property. Failed arbitrary-frame or abstract-domain
contracts generally reject a proof method, not necessarily a candidate's
blank-start behavior. The outward-loop hybrid traces above are concrete blank
computations and have the stronger status stated there.

The corrected all-helper grammar search completed 256,000 attempted rotation
proposals, with best effective reader cost 62 (196 total states). A further
30,000-proposal scanner portfolio reached six internal obstructions. Saved
grammars and logs are included; these heuristic budgets are not exhaustive
enumerations of all programs or machines.

FORMAL SCOPE

The published PA196 Lean development explicitly exports PA-proves(nonhalting
implies Con(PA)). Its inspected endpoints do not export the internal converse.
The report details the additional syntactic proof translation, canonical stack
annotation, and positive-length tape/source reflection for the written internal
biconditional. No new completed Lean-kernel endpoint is claimed. Symbolic runtime
certificates are executable mathematical checks, not a claim that a bounded
simulation proves nonhalting. Negative synthesis results are limited to their
stated templates and do not prove a general lower bound of 196.

PROVENANCE

BusyBeaver PA196: 407cdc356f6b586635e71ac92be394255f4bfea4
BusyBeaver PA209: 69d98241a721ead20b4f0b17df9062950b40fbfe
ProveIt:         dc523e7b06ffb414093c90aa035500ca283e5f75

Exact source/archive-member bindings and inherited licenses are preserved in
the relevant directories. No claim of upstream authorship or endorsement of
the new experiments is made. The pinned source files are not modified.
