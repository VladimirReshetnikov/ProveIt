PA194DHS -- a materially different 194-state PA consistency machine
Research report dated 13 November 2026, Pacific time

RESULT

No machine below 194 working states was verified. This package supplies
the requested fallback: a new 194-state binary one-tape machine and an
ordinary mathematical proof of

    PA |- (not Halt(PA194DHS, blank) <-> Con(PA)).

The logical proof uses the explicitly retained ordinary separate-head PA
calibration. The new command compiler, source specialization, physical
contracts and complete startup are verified here. This is not a newly
compiled end-to-end Lean/Rocq theorem or a completed iPRA endpoint.

START HERE

    report/report.pdf     Integrated report, proofs, comparison and table
    report/report.tex     Main LaTeX source (supporting fragments alongside)
    machine/machine.tm   Definitive five-column binary transition table
    verify_all.py        Complete construction and certificate replay

MACHINE CONVENTIONS

Working controls: dense 0 through 193. Initial control: dense 0.
Terminal halt label: dense 194; excluded from the working-state count.
Native labels: start 74, dispatcher 84, halt 254.
The initial head is at cell zero on a two-way tape containing only zeros.
Every transition writes 0 or 1 and moves exactly L or R.
There are 388 transitions, two per working control. labels.json records
the dense/native bijection. All 194 controls are control-graph reachable.

Allocation: 135 fixed controls + 69 AX readers - 10 contextual folds = 194.
Exact dense-table SHA-256:
2c5385ddcb928af834c1b959058d5fdc9e01b1d2be3ee9cf7c50557e45bfb48e

The machine combines the Gamma(D) emitter with no-push MP and a symmetric
cache-only Shift test. Successful MP retains the consequent in top and
offset, so a following zero-parameter AX emits its diagonal-vacuity
instance. This command behavior differs from both parents. The complete
graph differs from every one of the 34 supplied 194-state graph classes
under control renaming, spanning-start choice, reflection and symbol swap.
The individual ingredients and inherited engines are credited in the report.

REPRODUCTION

Python 3.10 or later, standard library only, no network:

    python3 -B verify_all.py

Run without -O or PYTHONOPTIMIZE; assertions are certificate checks and
optimized mode is explicitly rejected. The full independent literal check
takes about 80 seconds on the original host; speed varies by machine.
The wrapper checks pinned dependency hashes, rebuilds the candidate, checks
the command identities and independent physical contracts, compares all
frontier representatives, and verifies every append-zero start.

Individual stages:

    python3 -B build.py
    python3 -B proof/check_commands.py --output evidence/commands.json
    python3 -B verification/check.py

The supplementary 186 compilation profiles can be replayed independently:

    python3 -B supplement/semantic_screens.py

Optional local contractions, the 15,120-case head-order screen and timed
grammar searches require a C++17 compiler. See the self-contained bundle:

    search/local_and_grammar/README.md

Timed proposal counts are performance-dependent and do not count distinct
machines. Neither failed searches nor optimistic state scores are proofs
of minimality or correctness.

To rebuild the PDF with a standard LaTeX installation:

    cd report
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

VERIFIED EVIDENCE

- 40 simultaneous two-cell fold cases.
- 3,650 source sites and 4,752 universal primitive source outcomes.
- Arbitrary natural register values, arbitrary natural extra header gap,
  and any nonempty finite spare list; no bounded-value sampling argument.
- Four finite-list sweep lemmas rederived from literal transition rows.
- 1,096,025 symbolic operations, maximum 385 per outcome, minimum positive
  duration constant 3; the independent engine imports no construction
  compiler or arithmetic-block oracle.
- Fresh 263,236-pair source invariant for the two zero-test returns.
- Exact whole-tape initialization after 58,014 transitions, independently
  checked by sparse and bytearray simulations.
- All-variable command identities, including Gamma(D) selection, all
  halt branches and the numerical zero-stack aliases.

COMPARISON AND ADDITIONAL RESULTS

The pinned corpus contains 47 filed deliveries and four current incoming
archives. Its fresh numeric-table scan finds 1,811 table occurrences, 683
byte forms, 487 graph classes admitting a spanning start and 34 distinct
194-state graph classes. Among those 34, 21 are reported constructions,
nine are auxiliary research tables and four are explicitly rejected.
Historical proofs have not all been freshly revalidated. HS and NS are
byte-identical; N6 is repeated in two current submissions. The 51-delivery
ledger, all 34 frontier representatives and a full-tuple novelty checker
are included. Regenerating the entire census requires the pinned checkout;
verifying the new machine does not.

For the exact primary-PA194 append-zero transplant, all 194 working-state
blank starts are classified: four halt, and 190 reach inductively provable
blank rays within 77 steps. The statement concerns that exact one-row
mutation and does not exclude more substantial zero-spare redesigns.

The supplement proves that negative-only diagonal vacuity suffices for the
inherited PA refutation calibration. This is an ordinary proof-template
argument, not a new Lean endpoint or a claimed translation of every old
diagonal axiom. Direct negative-only profiles cost at least 200 states;
positive-offset profiles cost at least 198; controller/radix crosses have
minimum 194. These are optimistic compilation screens, not accepted TMs.

ARTIFACT MAP

report/                   Integrated TeX/PDF and generated tables
machine/                  Dense/native tables, source instructions, folds
construction/, inputs/    Pinned offline construction dependencies
proof/                    Free-term and command-interface checks
verification/             Independent literal-tape/source checker
evidence/                 Completed verification receipts
comparison/               Full ledger/census, 34 tables, novelty and reviews
search/append_zero/       Exact rejected mutation and all-start certificates
search/local_and_grammar/ Portable optional finite and heuristic searches
supplement/               Restricted-schema proof and semantic-cost replay
references/               Inherited ordinary PA calibration and parent proofs
PROVENANCE.json           Origins, pinned dependency hashes and result scope
SHA256SUMS                All delivered files except this checksum file

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 3cc7fbf75ba111a0da696ef2f6001dd528891bd5
The user's repository was not modified. Original licenses and attributions
to Vladimir Reshetnikov, James Chang and the inherited register-engine
authors are preserved. See the report and per-bundle provenance files.
