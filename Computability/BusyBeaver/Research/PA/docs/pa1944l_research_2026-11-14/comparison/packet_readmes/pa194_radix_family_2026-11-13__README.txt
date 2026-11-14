NEW 194-STATE TURING MACHINES CALIBRATED TO Con(PA)
=================================================
Prepared 13 November 2026, Pacific time.
Repository snapshot: 17f92105e2bc4317feae6c219cb2143437b482ff

RESULT
------
No verified machine below 194 working states was found. This archive fulfills
the alternative request with two materially different 194-state constructions:
M5 and M6, using formula-constructor coefficients 5 and 6. M4R is an additional
194-state machine with the new decoder arrangement and exactly the original
resolved coefficient-4 source graph.

For each main machine, the report proves in ordinary mathematical terms:

  PA proves [the machine does not halt on blank tape <=> Con(PA)].

The proof combines inherited PA-calibration interfaces, a new proof translation,
the generic constructor lemma, exact source binding, and universal literal-tape
simulation. There is no newly compiled end-to-end Lean or Rocq endpoint here.
No reduction to 193, global state-count lower bound, or speed improvement is
claimed. Novelty is relative to the pinned corpus, not all published literature.

START READING
-------------
report/pa194_radix_family.pdf         Main report, comparison and complete table
report/pa194_radix_family.tex         Editable main source
calibration/radix_calibration_standalone.pdf
                                      Detailed arithmetic/logical calibration
construction/generic_cons_proof.pdf  Detailed constructor-macro proof
comparison/archive_ledger.csv        All 41 delivered packet families
RESULTS.json                         Compact machine-readable results
PROVENANCE.json                      Sources, scope and provenance

The corresponding .tex files, generated report tables and all reproduction
inputs are included. SHA256SUMS and MANIFEST.json bind the release files.

MACHINE CONVENTIONS
-------------------
Main tables: machines/{4R,5,6}/machine.tm
Five columns: current_state read_bit write_bit direction next_state
Direction is exactly L or R. The tape alphabet is {0,1}; the initial tape is
all zero and extends infinitely in both directions. Working states are 0..193,
start is 0, and terminal halt is 194. Halt has no outgoing transitions.
Each table has 388 rows. The count 194 excludes halt.

The companion machine.native.tm files use sparse native labels, start 74 and
halt 254. labels.json maps dense labels to native labels, including halt.
unfolded202.native.tm is the 202-control parent before the eight folds.

Dense-table SHA-256:
4R  a3c1d556d61b37d60639801accacfa595df4b2c9d2b2a0a46978425b10c459a8
5   180a0fd1f046d4cbd687b43979f0605619ad5f53054d32b9f62f33e7a3bccab8
6   725ce8474d7b83473488fc9466548ed2de3744d9a80183467894f9d719103ab2

REPRODUCE THE MAIN MACHINES
--------------------------
Use Python 3.10+ with its standard library, with assertions enabled. No network,
repository checkout, external Python package or proof assistant is required.
Tested on Linux; use a POSIX environment or WSL for byte-identical LF output.
Run the following commands from this archive's top-level directory:

  python3 -B construction/build.py --output generated
  python3 -B verification/check.py generated/4R generated/5 generated/6

To build only one family, append --family 5 (or --family 6 or --family 4R).
The builder asserts the three exact dense-table hashes above. It also checks
all 61 constructor substitutions, all 3,429 outside primitive sites and their
successors, the complete AX emitter, 32 simultaneous fold cases, universal
source contracts, and the complete blank startup at physical step 58,320.

The independent checker takes one or more machine directories as arguments.
It imports neither the builder nor its arithmetic-box oracle. It derives four
list-sweep contracts from the literal rows and resolves the source graph in two
independent ways. Its scope includes nine arbitrary natural registers, both
decrement outcomes, an arbitrary finite nonempty spare list and an affine gap.
It checks the entire finite-support startup tape, not a sampled window.

To recheck the delivered copies directly (this overwrites their independent
receipt and contract files, so use generated/ above to preserve the manifest):

  python3 -B verification/check.py machines/4R machines/5 machines/6

Completed evidence is at machines/{4R,5,6}/independent/. Construction receipts
are at machines/{4R,5,6}/receipt.json. Symbolic step counts are checker operations,
not actual running times of the machines. Startup counts are literal TM steps.

The 4R independent receipt was produced by the earlier standalone checker and
uses slightly different field names. Its tape evidence is valid. The separate
comparison/rotation-i-novelty.json is the authoritative 4R corpus comparison;
obsolete isolated-checker novelty claims were removed from that receipt.

REPLAY THE COMPARISON
---------------------
These commands use the included census and do not require the original repo:

  python3 -B comparison/compare_candidate.py machines/4R/machine.tm
  python3 -B comparison/compare_candidate.py machines/5/machine.tm
  python3 -B comparison/compare_candidate.py machines/6/machine.tm

All three have no match in the pinned census. This is graph comparison under
arbitrary working-state renaming, any spanning root, global tape reflection,
and global read/write-bit complementation. It is not a semantic proof.

The census records 4,421 table occurrences / 621 distinct byte forms, including
historical and rejected experiments. At 194 states there are 15 prior byte
forms in eight graph classes. One of these is a rejected scanner quotient.
All 41 packet families are compared in archive_ledger.csv/json and the report.

The literal recognizer reads complete numeric five-column .tm/.txt/.tsv/.csv
tables, including nested archives. Arbitrary code/JSON/prose representations
are outside its scope; packet narratives were reviewed separately. Repeating
the full repository census requires the pinned checkout and its archive files;
run comparison/census.py --help for its command-line options.

BUILD THE PDFS
--------------
A standard TeX Live installation with pdfLaTeX, Latin Modern, microtype, AMS
packages, TikZ, xurl, hyperref, geometry and the listed standard table packages
is sufficient. Run:

  bash build_pdf.sh

This regenerates report includes from the machine receipts and builds the
main report and both new proof supplements. PDFLATEX can select another
pdfLaTeX executable; PDFLATEX_FMT can optionally select a prebuilt format.
Inherited calibration .tex files are preserved as source references; the
script does not build those historical standalone documents.

LAYOUT
------
construction/   Standalone builder; frozen inputs; generic Cons proof; licenses
machines/       Accepted main tables, source maps, fold traces and all receipts
verification/   Independent literal-tape checker and its separate runtime
comparison/    Complete census, 41-packet ledger, old 194-state representatives,
               novelty receipts and mathematical audit
calibration/   New full radix proof, retained older calibration text and pinned
               Lean interfaces with their own provenance hashes
search/        Bounded search code, inputs and logs; auxiliary CSZ basis;
               clearly marked rejected examples
report/        Main TeX/PDF, complete native transition table and packet ledger

The search material is research evidence, not additional claims of a smaller
machine. Search templates, observed counts, limitations and reproduction
commands are in search/README.txt and search/machine_searches/README.txt.
In particular, a rejected source-equivalent change halts during initialization
after 1,361 steps. It is never presented as a PA-consistency machine.

PROOF STATUS AND REUSE
----------------------
The new logical argument explicitly handles variable-label recoding, the fact
that recoding is not order-preserving, unused residues, the zero-code alias,
ten-entry stack identities, dirty incoming stores, and positive durations.
The exact generic rho8All Lean interface is retained, but no claim is made
that the new complete PA theorem has been kernel-checked. The executable
certificates check the finite program obligations described in the report.

Inherited James Chang and ProveIt notices are retained in construction/ and
the auxiliary research package. Consult PROVENANCE.json for source attribution.
