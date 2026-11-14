PA194: a 194-state binary Turing machine for Con(PA)
=================================================

The definitive machine is pa194/pa194.tm. The accompanying article gives an
ordinary mathematical proof of

    PA proves: not Halt(PA194, blank) if and only if Con(PA).

The machine has 194 working states, numbered 0 through 193, and a separate
halting label 194. The start state is 0. Its single two-way infinite tape is
binary, initially all zero, with the head at coordinate 0. Each working state
has exactly two outgoing rows, and every move is L or R. The halt label is not
included in the working-state count.

Each of the 388 rows has five columns:

    state  read_symbol  write_symbol  direction  next_state

Literal table SHA-256:
9087d70fc0e1878c38ceff928e6e7e0999c86b6efed00a5ec353821c00641c87

Read first
----------
report/pa194_conpa.pdf      Main article, including the complete transition table.
report/pa194_conpa.tex      Main LaTeX source; uses the neighboring TeX fragments.
pa194/pa194.tm             Definitive machine-readable transition table.
pa194/README.txt           Detailed construction and artifact guide.

What changed
------------
The supplied PA195 design has 134 fixed controls, 68 raw axiom-reader controls,
and 7 compatible folds: 134 + 68 - 7 = 195. The prior separate196 design uses a
190-token emitter and 6 folds. PA194 uses that same separate190 emitter with a
new binary association exposing 8 simultaneously valid folds:

    134 + 68 - 8 = 194.

The prior logical emitter is credited to the supplied research. The new result
is its 194-state physical implementation, including an exact source binding,
complete universal symbolic contracts, and a simultaneous local quotient proof.

Compared with PA195, the emitter deletes the cons token at zero-based index
184, leaving the diagonal-vacuity formula Gamma(A) = A -> forall A A as an
additional saved stack entry. The ten-entry command compiler is proved for
the original Shift condition t+h=1. Its selectors are adjusted explicitly.

Reproduce the accepted construction
----------------------------------
From this directory, with Python 3 and its standard library:

    python3 -B pa194/build_verify.py
    python3 -B verification/independent_verify.py
    python3 -B mathematics/check_emitter_and_words.py

Do not use Python -O: the verifiers deliberately use assertions. The scripts
locate their inputs relative to themselves and also work from other current
directories. No network, solver, proof-assistant installation, or heuristic
search is needed for these checks.

The first two commands reconstruct and verify all literal table, source graph,
local quotient, startup, and symbolic runtime facts. The third checks the exact
emitter and ten-entry command words in a symbolic term algebra with explicit
arithmetic constructor facts. The inherited symbolic register engine and its
boxed loop lemmas are shared dependencies, not two independent proof kernels.

The --quick option of the first two scripts omits their full symbolic runtime
passes. Use the commands above for the complete verification. The saved receipts
record complete runs; they are not substitutes for executing the checks.

Checked values
--------------
Working states / binary rows                 194 / 388
Raw states / simultaneous folds              202 / 8
Graph-reachable working states               194
Source primitive sites                       3,673
Symbolic branch contracts in each table      4,780
Incoming rows establishing history bits      23
Exhaustive two-cell local quotient cases      32
Local simulation lengths                     1, 3, 5, or 7
Exact blank-start initialization              58,154 literal transitions
Startup endpoint                             dense state 75, head -2
Complete startup tape                        66 one-cells; all others zero
Longest source path / header gap             38 / 48

The symbolic path lengths in the receipts measure finite symbolic proofs, not
uniform literal running-time bounds for arbitrary unary register contents.
Graph reachability does not assert that all states occur in the actual blank run.

Proof and limitations
---------------------
The report proves both directions internally in PA. It preserves the supplied
PA195 syntactic consistency calibration, translates between the bundled and
separate diagonal calculi, proves the changed command words, binds the source
program to the prior separate196 implementation, and proves positive physical
simulation and halting preservation under all eight simultaneous folds.

This is an ordinary mathematical proof with executable supporting certificates.
No newly elaborated end-to-end Lean or Rocq kernel theorem is claimed. The
reference sources and exact dependency boundary are included for further
formalization. The theorem does not assume PA is consistent; actual blank-tape
nonhalting follows if PA is consistent. No minimality claim for 194 is made.

Comparison and provenance
------------------------
The input repository is VladimirReshetnikov/ProveIt, pinned at
5be8b9236df6a6d308195e62a906a173dc70d00a.

The fresh comparison inventories all 31 incoming ZIPs and direct PA tables.
Recursive scanning recognizes complete numeric five-column binary .tm/.txt
tables: 2,719 occurrences, 576 distinct byte strings, and 566 labeled transition
functions. These are inventory counts and include duplicates and unsuccessful
designs. The report separates supported constructions from rejected or
uncertified candidates. The census is not a lower bound or a recognizer for
every machine encoded in arbitrary program source.

reference/pa195_conpa/ is the supplied PA195 packet with its original sources,
calibration proof, comparison, licenses, and attribution preserved. Additional
archived separate196 and original-command excerpts are under reference/.
The entire 233 MB incoming corpus is not duplicated here; its pinned identities,
member locators, and hashes are in comparison/corpus/. The construction and all
three verification commands above are self-contained.

Directory guide
---------------
pa194/          Literal tables, grammar, folds, source, certificates, and builder.
mathematics/    Consistency calibration and independent symbolic command checker.
verification/  Independent reconstruction and all complete-run receipts.
comparison/    Fresh corpus census, archive comparisons, and source identities.
reference/     Preserved prior construction and licensed source dependencies.
search/        Optional discovery code, exact winning witness, and bounded logs.
report/        Complete LaTeX article, fragments, and compiled PDF.

Search replay is optional. search/reconstruct_grammar.py checks the frozen
winning witness against the delivered grammar without rerunning the search.
Search scores and unsuccessful bounded searches are never treated as proofs.

Build the article
-----------------
With a standard LaTeX installation, from report/:

    latexmk -pdf -interaction=nonstopmode -halt-on-error pa194_conpa.tex

Alternatively run pdflatex with those flags twice. The article requires only
standard LaTeX packages; no external bibliography or downloaded figure is used.

Integrity
---------
SHA256SUMS binds every delivered file other than itself. To verify it on systems
providing sha256sum, run from the package directory:

    sha256sum -c SHA256SUMS

The reference directories retain their original license notices. New explanatory
and verification material is provided with attribution to the referenced source
designs; the package does not claim authorship of the inherited PA196/PA195
calculus, compiler, or register engine.
