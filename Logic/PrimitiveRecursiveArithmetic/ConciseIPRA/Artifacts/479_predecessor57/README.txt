A SMALLER CHECKED PRESENTATION OF iPRA
A 479-byte kernel and a 57-node scalar predecessor
Prepared for Vladimir Reshetnikov, 12 November 2026
================================================

START HERE

ipra_479_predecessor57.pdf
    Complete compiled report. It states the native axioms and rules, proves
    the new predecessor and checker refinements, explains both interpretation
    composites, and reproduces attributed inherited foundations.

ipra_479_predecessor57.tex
    Flattened, standalone LaTeX source. It does not require external input
    or listing files. The editable modular sources are also included.

MAIN RESULTS AND LIMITS

The direct compact checker improves from 487 to 479 normalized bytes.
The new complete module has 272 significant tokens and 304 AST nodes.
The current corpus-wide token and AST records, 248 and 270, are NOT beaten.
The new coordinatewise envelope is (248,270,479), achieved by different
programs. Neither this tuple nor the earlier records are proved global
complexity lower bounds. Compressed-source illustrations use a different
accounting category and are expressly discussed in the report.

The arithmetic improvement is separate: a shorter three-state clock and
ramp, followed by reversed comparator saturation, reduce the fully expanded
scalar predecessor from 75 to 57 constructor nodes (24%). The internal
proof uses only the inherited equation-induction basis. It does not assume
predecessor, pairing, arbitrary equality reflection, or successor injectivity.

The ordinary realization remains bi-interpretable and equiconsistent with
full first-order intuitionistic primitive recursive arithmetic. Numerical
domains are whole, equality is actual, and both numerical comparison graphs
are x=y. No primitive arithmetic or logical axiom is deleted, and no globally
simplest axiomatization or new Lean/Rocq verification is claimed.

PROOF CHECKERS

Recommended arbitrary-input interface:

    python3 checker/code/strict637.py < checker/fixtures/strict_proofs/computation_zero_local.json

A valid proof prints exactly ACCEPT and one newline and exits successfully.
All other outcomes reject. Python -O does not disable any acceptance gate.

Program                        Tokens   AST nodes   Normalized bytes
checker/code/compact479.py       272       304             479
checker/code/native607.py        337       383             607
checker/code/strict637.py        344       392             637

Their matched controls have 487, 629, and 646 normalized bytes respectively.
The six exact modules and their individual metrics are supplied under
checker/. All counts include the complete module, JSON input, and ACCEPT
output. No support file in this archive is imported by a measured checker.

The compact interface assumes a canonical closed GUARDED Eq/D goal and
finite integer/list certificate trees; it does not separately validate the
public grammar. The native interface validates the full closed native Eq/D
goal but retains the consumed-certificate alphabet promise. The strict
interface validates both the public goal and all input types, including
unused JSON prefixes. Do not combine these contracts in one size claim.

The compact 487-to-479 and strict 646-to-637 changes preserve finite raw
acceptance behavior exactly. The native 607-byte companion has eager source
opening, so its full native theorem set is unchanged but identical success
on every noncanonical stream is not claimed. The report and
checker/PROOF_NOTES.txt give the precise universal arguments.

MATHEMATICS AND EVIDENCE

mathematics/predecessor57.py
    Builds the fully expanded scalar terms, counts them, and evaluates the
    new predecessor literally at 0 through 4. Additional arithmetic checks
    are explicitly marked finite evidence, not proofs of the universal result.

mathematics/predecessor57_detailed.tex
    Detailed internal derivation, including a purely equational treatment
    of the Boolean cases. The main report contains the full native proof.

mathematics/block_macros.py and block_macros.tex
    One-binder finite blocks, the specified selector-padding optimum, and
    actual AST checks for the universal-prefix saving 85n+4 -> 67n+4.
    The block formulas trade raw size for smaller binder depth; they are
    not advertised as smaller in every measure.

checker/verification.json
    632 control/candidate process executions, normal and optimized Python,
    with zero unexpected outcomes. Includes the exact 17-packet scope
    counterexample and the valid native atomic-case theorem D(x,y)(y=1).

evidence/
    Source-corpus measurement ledgers, incoming archive identities,
    independent written review notes, and final PDF quality checks.

reference/
    Attributed exact inherited foundations and the pinned repository README.
    Historical first-person or novelty language in these files belongs to
    their original reports. It is not a new-contribution claim here.

REPRODUCE

    python3 reproduce.py

This reruns the proof-checker suite, term and formula utilities, and creates
the flattened TeX. The reference metric runtime is CPython 3.12.14.

    python3 reproduce.py --pdf

This also rebuilds the PDF with installed pdfLaTeX. The build helper can
construct a private format and font map from installed TeX assets when a
minimal installation lacks generated caches. It downloads nothing and
does not alter global TeX files. A conventional full TeX installation can
instead compile the standalone TeX directly.

    python3 verify_manifest.py

This verifies all packaged files against MANIFEST.sha256. Reproduction
regenerates evidence and may change environment-specific metadata, so run
the manifest check before rebuilding if exact delivered-byte identity matters.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: ecae4653f69184a25ade2b1aeaa346f7a7817b78
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The audit includes all 1,314 distinct current artifact Python blobs and
all nine then-current incoming archives, plus the unified article when
checking mathematical novelty. The 57-node construction is new relative
to that inspected corpus; no literature-wide priority claim is made.
The inherited MIT No Attribution license is retained in checker/.
No repository commit, pull request, or external publication was created.
