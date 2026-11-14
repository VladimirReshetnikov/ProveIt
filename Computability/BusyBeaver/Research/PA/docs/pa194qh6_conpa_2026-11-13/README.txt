PA194QH6 — a new 194-state composition for Con(PA)
Prepared for Vladimir Reshetnikov, 13 November 2026 (Pacific date)

RESULT

No machine below 194 working states was obtained. This package supplies the
requested fallback: a materially different 194-state binary single-tape TM,
starting on the all-zero two-way infinite tape.

The new verified composition combines the premise-exchanged universal
quantifier-distribution emitter (Q), coefficient-six formula coding, no-push
modus ponens, and a Shift that tests only the cached formula for contradiction.
The component ideas come from the supplied packets; their composition and
exact literal/source binding are new in the pinned comparison corpus.

The ordinary mathematical theorem is:

  PA proves: Halt(PA194QH6, blank) iff there exists a PA proof of 0=1.
  Consequently PA proves: Nonhalting(PA194QH6, blank) iff Con(PA).

This is an ordinary mathematical proof using the explicitly identified
inherited PA-calibration lemmas, together with new finite and universal
symbolic certificates. It is not a newly compiled end-to-end Lean or Rocq
proof, does not claim an iPRA endpoint, and does not prove a state lower bound.
Actual nonhalting additionally follows if PA is consistent.

START HERE

report/main.pdf             Article, proof, comparison, all transition rows,
                            complete 55-delivery ledger and 40-class frontier.
report/main.tex             LaTeX source; all input files are alongside it.
machine/machine.tm          Literal dense TM: start 0, working states 0..193,
                            terminal label 194; 388 transition rows.
machine/machine.native.tm   Native-label presentation: start 74, halt 254.
machine/labels.json         Dense-to-native transition conjugacy, halt included.
verify.py                  Full deterministic acceptance checks.
comparison/AUDIT.txt        Scope, counts, duplicates, rejected designs, novelty.
comparison/QH6_REVIEW.txt   Independent mathematical review and limitations.
proof/qh6_preservation.tex  Expanded construction and preservation argument.

MACHINE IDENTITY

Dense table SHA-256:
a48c4729cb35c298c364ba5a7c1d5e489ea3c111f482a93e57338d4c9847d1e9

Native table SHA-256:
6ee047dc2d01faf550e83f40c85b5ac50a74c1699f15211e329047e51d979a4b

Each row is: current_state read_bit write_bit direction next_state.
Direction is L or R, and the halt control has no rows. No nonblank input,
extra tape, larger alphabet, stationary move, or hidden initialization is used.

REPRODUCE

Python 3.10+ and the standard library suffice. From this directory:

  python3 -B verify.py --receipt fresh-verification.json

This rebuilds in a temporary directory, checks exact byte equality, all
4,876 construction contracts, command algebra, source graph relocation,
the finite exchange proof, graph novelty, and the independent literal-tape
simulation. Do not use -O or PYTHONOPTIMIZE, since assertions are checks.

The optional --quick flag omits only the independent literal-tape replay;
the output explicitly records that omission. The delivered release receipt
was produced by the full default command.

To rebuild only the literal table:

  python3 -B construction/build_qh6.py --output rebuilt-machine

To rebuild the PDF, enter report/ and run twice:

  pdflatex -interaction=nonstopmode -halt-on-error main.tex

No network, source checkout, solver, or proof assistant is needed for the
machine/certificate replay. A TeX installation is needed only for PDF rebuild.

COMPARISON

Pinned repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 2e00058366845a6e2e0368004fd9ed2050a06a9a

Scope: all 51 placed PA research deliveries plus four current incoming ZIPs;
recursive literal-table inventory includes nested reference ZIPs.
Current census: 1,445 recognized table occurrences, 725 byte forms, 499 full
one-halt graph classes with a spanning root, 40 of them at 194 states.
Of those 40, 27 have supplied ordinary PA-equivalence manuscripts, nine are
auxiliary/search classes, and four are explicitly rejected. These statuses
are not a claim that every older proof was independently reproved here.

The new table differs from all 40 under arbitrary state renaming, any spanning
root, global tape reflection, and global binary-symbol exchange. Exact
canonical tuples are included, so novelty can be replayed offline.

The repository's 4,984-table count refers to original pre-dedup deliveries.
Its 490 graph classes include three diagnostic fixtures excluded by this
full-table census; current incoming archives add 12 classes, giving 499.
See comparison/AUDIT.txt for complete reconciliation and recognition limits.

Two different packets use the name PA194NS for different machines. The audit
identifies them by packet and hash, not by the short name.

VERIFICATION OBSERVED

194 working states; 388 rows; 135 fixed + 67 reader - 8 folded controls.
3,775 resolved source sites; 4,876 arbitrary-register outcome contracts.
Construction checker: 1,601,532 symbolic operations, maximum case 499.
Independent literal checker: 1,169,239 symbolic operations, maximum case 403.
Four literal-row generic list lemmas; positive duration constant at least 3.
Exact blank startup: 58,088 literal transitions to the complete clean frame.
83 resolved instructions differ from H6; 3,692 are unchanged.
61-line finite K/S/MP proof of exchange.

Symbolic operations are not bounds on total physical runtime. The affine
header domain and complete tape/register/spare-list invariants are specified
in the report. Startup checks the entire finite-support tape, not a window.

LAYOUT AND ATTRIBUTION

construction/   Deterministic builder, frozen source inputs, symbolic engine.
machine/        Tables, source, fold witnesses, receipts and independent audit.
proof/          Emitter, command and source-binding checks; finite proof data.
verification/   Separately implemented literal-tape symbolic checker and replay.
comparison/     Full census, graph representations, ledger, frontier and review.
research/       Bounded unsuccessful reduction experiments and exact receipts.
references/     Necessary inherited mathematical and Lean source dependencies.
licenses/       Supplied ProveIt and James Chang license notices.
report/         Main article and every LaTeX input, compiled PDF.

The archive does not duplicate the entire historical input corpus. Recreating
the full census requires the pinned repository; checking the delivered table
against the frozen census does not. No repository changes were published.

ARCHIVE INTEGRITY

SHA256SUMS covers every other delivered file. From this directory, a system
with sha256sum can check the extracted contents with:

  sha256sum -c SHA256SUMS
