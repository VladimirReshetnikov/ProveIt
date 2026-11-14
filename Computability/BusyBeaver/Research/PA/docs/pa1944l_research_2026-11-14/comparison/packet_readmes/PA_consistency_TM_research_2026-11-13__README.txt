PA CONSISTENCY MACHINES: COMPARISON AND NEW SOURCE REDUCTIONS
13 November 2026

RESULT

No verified two-symbol Turing machine below 196 working states is claimed.
The requested construction remains unresolved by this investigation. This
packet contains new source constructions, proofs, comparisons and bounded
searches. It does not contain a successful 195-state transition table.

Read report.pdf, or build report.tex. The report and this README distinguish
an exact source-graph identity, a physical TM refinement, and the internal
PA consistency biconditional. In particular, the imported PA196 theorem
inventory exports PA |- Nonhalt(PA196) -> Con(PA); its formally bound internal
converse remains a separate obligation. This does not assert that the
converse is false or unprovable.

The convention throughout is a single two-way infinite tape, alphabet
{0,1}, blank input, and a separate halt control excluded from the count.

CONTENTS

report.tex, residual_command_proof.tex, screen_results.tex, report.pdf
  Complete report, ordinary mathematical arguments and compiled PDF.

combined157/
  New 157-internal-node representation of the 3,573-site combined
  negation/MP source. Ordered primitive instructions and every ordinal
  successor agree with the supplied combined 197-state construction.
  Two independent CFG resolvers check the claim. The experimental allocation
  subdirectory is explicitly rejected; it is not a smaller TM certificate.

source_zero5/
  New 159-internal-node representation of the original 3,812-site PA196
  source with maximum zero run five. It preserves the entire ordered word
  and ordinal CFG. The old source has maximum zero run six. Source159.lean
  contains generated definitions, not a compiled formal proof. The optional
  160-node file is an earlier discovery witness, not the main result.

residual_mp/
  Parameter-free MP adapted from the ZFC opposite-comparison-residual idea.
  An exact 3,799-site source, an ordinary proof compiler, a three-case loop
  proof, and portable checks are included. The local comparator has the
  same register-machine execution time as its predecessor for every natural
  input. The modified source has 164 distinct internal nodes and has not
  been allocated as a smaller physical TM. The 54,509 command checks use
  three safe abstract AX models and premise-compiler interface assumptions;
  they do not evaluate the full native AX emitter or prove a PA theorem.

comparison208/
  Offline comparison of 27 designated final U208 presentations, giving
  20 rooted action-preserving graph classes. Includes original comparator,
  18 helper checks, pinned inputs, provenance and fresh replay receipts.

selected196_tables/, verify_selected196.py, build_196_census.py
  Fourteen total, graph-reachable, pairwise nonisomorphic 196-state tables,
  with exact original member names, hashes, labels and validation scopes.
  Two are experimental MP variants. The census does not certify their
  consistency endpoints. build_196_census.py is the original discovery
  utility and expects the repository/archive layout; the portable
  verify_selected196.py uses only the supplied selected tables.

local_search/
  C++17 two-arbitrary-row synthesis with a targeted third-row extension,
  a portable runner, exact inputs, positive controls, and complete receipts.
  Refined-baseline run: 2,219 contexts; 1,097,600 third-row actions; zero
  survivors. Fourteen-table run: 535,080 ordered state pairs; 1,657,293,680
  first-row actions; 5,874,311,296 second-row actions; 9,618,896 third-row
  actions; zero survivors. Context invariants for the fourteen-table run
  are separately computed radius-six blank-start window closures.
  These results concern the specified five-cell, at-most-sixteen-step
  simulation template. The third stage is NOT all three-row repairs.
  The inherited_contexts/ subtree supplies the original all-natural
  symbolic context collector and its provenance, not newly authored code.

rejected_prefix/
  Independently checkable wrong-child example for a naive root rewire,
  and all 788 one-row actions (including halt targets) at native row 69/0
  under the stated prefix
  endpoint test. Symbolic instruction-checker rejection receipts are kept
  with their actual scope. A checker exception alone is not proof that a
  candidate halts on blank input or cannot be justified another way.

archive_inventory.json
  Exact names, hashes, member counts and contributions of all twenty
  incoming archives at the pinned revision. The full large original
  archives are not duplicated in this packet.

audit_notes.txt
  Detailed raw research notes. Some paths refer to the original work area;
  report.tex and this README give the portable packet paths and final scope.

verify_all.py, verification_receipt.json, SHA256SUMS.json
  Quick reproducibility entry point, actual replay results, and final
  byte-integrity manifest. A digest verifies byte identity, not a theorem.

QUICK REPRODUCTION

Requirements: Python 3.10 or later, standard library only. Run from this
directory with assertions enabled (do not use -O or -OO).

  python3 verify_all.py --output /tmp/pa_tm_checks.json

The runner verifies the final manifest if present; runs the two source
identity checks, the residual source construction and command regressions,
the 208 comparison, the 196 census, the independent synthetic-control
replay, and the rejected-prefix check. Intermediate outputs use a temporary
directory. This is not a Lean build, a rerun of every original machine's
symbolic runtime, or a replay of billions of synthesis actions.

The source_zero5 checker deterministically rewrites its identical receipt.
All other newly generated outputs of the quick runner are temporary or
written to the --output destination. No network access is required.

EXTENDED SEARCH REPRODUCTION

Requires g++ with C++17. Use a NEW output directory for each command.

  python3 local_search/run_search.py --control --output /tmp/pa_fold_control
  python3 local_search/run_search.py --refined-baseline --workers 1 --output /tmp/pa_fold_refined
  python3 local_search/run_search.py --workers 3 --output /tmp/pa_fold_variants

The last command reproduces the fourteen-table search. It is substantially
slower than the quick checks. Stored counts and exact contexts are under
local_search/variant_screen/. Timings depend on hardware and concurrency.

To regenerate the inherited source-conditioned invariant, consult
local_search/inherited_contexts/README.txt and run its source_contexts.py
and validate_contexts.py from that directory. These are additional checks
of an inherited symbolic model, with the scope described in the report.

PDF REPRODUCTION

With a standard TeX Live installation containing the packages named at the
top of report.tex:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

For an installed Debian TeX Live tree whose generated indexes/formats are
missing, the optional recovery helper builds using a private temporary cache
without changing system files:

  python3 tools/build_pdf_fallback.py

SOURCE PINS AND ATTRIBUTION

ProveIt revision:
  38b84bce90b7d1c24c3319c0ff58d8ef92d96b21
Imported James Chang PA196 revision:
  407cdc356f6b586635e71ac92be394255f4bfea4
Imported James Chang PA209 revision:
  69d98241a721ead20b4f0b17df9062950b40fbfe

Primary paths and URLs are in the report bibliography. Original source
licenses and notices are preserved in each relevant subtree. The existing
TMs, theories, symbolic runtime tools and source representations are credited
to their authors; upstream authors did not review this investigation.

No fresh full Lean build or physical refinement certificate for a new TM
was produced. No negative bounded search in this packet is a lower bound
on the number of states required for the consistency problem.
