PA194J and PA194D: two new 194-state PA consistency machines
==========================================================
13 November 2026, Pacific time

RESULT
------
No verified machine with fewer than 194 working states was obtained.
This packet supplies two materially different 194-state constructions:

  PA194J: ten source jumps replaced by decrements of registers proved
          zero by a finite inductive invariant; three native rows change.
  PA194D: the separately emitted diagonal head changes from Gamma(A) to
          Gamma(D), with a changed proof selector and a new 69-reader,
          nine-fold physical allocation.

For each exact delivered table M, the report gives an ordinary
mathematical proof, formalizable in PA, of

  PA proves: [not Halt(M, blank) if and only if Con(PA)].

The proof uses the supplied ordinary PA calibration and adds new source,
logical-interface, and literal-physical preservation arguments. It is not
a new end-to-end Lean/Rocq kernel theorem. No unconditional nonhalting,
iPRA equivalence theorem, or state lower bound is asserted.

START HERE
----------
report/pa194j_conpa.pdf        Complete report, both full tables, proofs,
                             comparison of all 41 packets, search limits.
report/pa194j_conpa.tex        Main LaTeX source; other report/*.tex are inputs.
construction/machine/pa194j.tm Authoritative dense PA194J table.
logical_emitter/machine/pa194d.tm
                             Authoritative dense PA194D table.
comparison/archive_ledger.csv Archive-by-archive corpus comparison.
RESULTS.json                 Machine-readable results and proof scope.
SHA256SUMS                   Hash manifest for the delivered files.

MACHINE CONVENTION
------------------
Both machines have working states 0,...,193, initial state 0, and terminal
halt label 194. The terminal label has no rows and is excluded from the
working-state count. The alphabet is {0,1}; the tape is two-way infinite,
initially all zero; the head starts at cell 0. Every move is exactly one
cell L or R. Each of the 194 working states has both read-symbol rows.

Each .tm line is:

  state read_bit write_bit L_or_R next_state

Native-label presentations start at 74 and halt at 254. Each machine's
labels.json gives the exact dense-to-native conjugacy, including halt.

PA194J dense SHA-256:
7c498ced0eb0dffed77ae2f68f4d80c98edfd8f7763ec1be68aa8cd7ea80eacd
PA194D dense SHA-256:
4226b7702de554df4b52d10239b2bd7ad79ca90bd8faf2bd256552fe0c7fe81b

REPRODUCE
---------
Python 3.10 or later, standard library only. From this directory:

  python3 -B verify.py

The full command checks file integrity, rebuilds both machines in a
temporary directory, recomputes their finite source invariants, checks
exact whole-tape blank initialization, proves every source contract using
the independent literal-tape engine, and checks novelty against all eight
old 194-state graphs. It also runs a second PA194J finite-invariant checker.
Allow several minutes. Assertions must be enabled: do not use Python -O.
No network, external repository checkout, or proof assistant is required.

For an explicitly limited, faster check:

  python3 -B verify.py --quick

This checks integrity, reconstruction, finite invariants, whole blank
startup, and novelty; it does NOT replay the universal physical contracts.
The original independently completed PASS receipts are retained in each
machine's evidence directory. Temporary execution leaves the frozen
packet unchanged, allowing repeated hash verification.

The machine folders can also be used separately:

  python3 -B construction/rebuild.py
  python3 -B construction/independent_verify.py
  python3 -B logical_emitter/rebuild.py
  python3 -B logical_emitter/independent_verify.py

These direct commands rewrite their evidence files, including timing in
the physical receipts; use the top-level temporary-copy runner when you
want to preserve the exact packet hashes.

Rebuild the PDF with a normal LaTeX installation:

  bash build_report.sh

The script runs pdflatex twice. The supplied PDF is already compiled.

VERIFIED RESULTS
----------------
                                PA194J             PA194D
Working states                     194                194
Transition rows                    388                388
Primitive source sites           3,646              3,649
Source outcomes checked          4,755              4,751
Positivity invariant pairs     263,180            263,244
Independent symbolic steps   1,103,582          1,091,154
Maximum steps per case             403                385
Exact blank startup             60,062             58,168

The source contracts cover arbitrary natural register values, arbitrary
extra header gap, and every nonempty finite spare list, with complete
tape frames and zero exterior. Both branches of all decrements are checked,
including branches excluded from the actual source run by the invariant.
Four generic list lemmas are derived from each literal table. The checker
imports no allocator or arithmetic-box oracle. This remains executable
mathematical evidence, with its soundness rules exposed as source, rather
than a proof-assistant kernel export.

Both machines reach source site 25, logical registers (2,0,...,0), native
control 84, head -2, header distance 48, and 26 spare blocks of value one.
Their complete startup tapes contain 66 one-cells and were checked exactly.

WHAT THE COMPARISON COVERS
--------------------------
The repository snapshot is VladimirReshetnikov/ProveIt at
17f92105e2bc4317feae6c219cb2143437b482ff.

The census covers all 36 filed PA/docs packets and five newer incoming
archives: 41 packets total. It recognizes 2,685 complete numeric-table
occurrences, 620 byte forms, and 446 action-graph classes. The old 194-state
frontier contains 95 occurrences, 15 byte forms, and eight graph classes;
one graph is a rejected short-scanner experiment. Multiple deliveries of
the same principal PA194C table are not counted as distinct designs.

The recognizer's scope is numeric binary tables in .tm/.txt/.tsv/.csv,
including nested archives. It does not extract arbitrary transition
systems encoded only in program source or JSON. Corpus counts include
rejected or diagnostic candidates and do not certify their semantics.

Both new principal graphs differ from every old frontier graph and from
each other, even allowing state renaming, a different graph root, L/R
reflection, and global tape-symbol exchange. PA194D's entire logical
emitter is also not a global A/D/H parameter permutation of the old emitter.

OTHER CONTENTS AND LIMITS
-------------------------
references/logical_calibration/ retains the inherited PA, diagonal,
separate-head, cached-command, and symmetric-Shift proof texts. These are
logical dependencies, not newly produced kernel certificates.

research/logical_variants/ contains five new emitter proposals and three
prior-art controls, with independent free-term checks and source graphs.
Only the separate-Gamma(D) proposal is delivered as an independently
verified 194-state machine. The other proposals are research inputs.

research/sibling_tables/ and research/gamma_d_csza/ contain additional
194-state siblings with primary-checker and initialization evidence. The
complete independent physical replay was performed for PA194J and PA194D,
not for every sibling. See the report before assigning a stronger scope.

research/search/ preserves search source, frozen inputs, seeds, logs and
receipts. Its numeric scores are candidate filters, not proofs of a state
count or a consistency equivalence. No failure to find a smaller table
is a lower bound. Optional C++ search runs are unnecessary for verification.

ATTRIBUTION
------------
See NOTICE.txt and the preserved license files. Source trees, runtime
proof engines, old machine tables, and logical proof texts are attributed
to the supplied ProveIt research packets, James Chang's upstream work,
and the other authors identified in their original notices.
