U209: JOINT DECODER REDUCTION FOR CON(PA)
Prepared for Vladimir Reshetnikov, 29 October 2026

RESULT
======
machine/u209.tm is a complete deterministic two-symbol, one-tape candidate
with 209 working states (0 through 208), separate halt label 209, initial
state 0, head coordinate 0, and an all-zero two-way infinite tape. Every one
of its 418 transitions moves L or R. Blank initialization is included.

Read report.pdf for the comparison, new construction, complete local proofs,
runtime proof rules, retained logical dependencies, and full transition table.
The editable source is report.tex plus tables/*.tex.

The new construction combines all three incoming U211 deletions by a new
18-selector association of a closed 3,096-primitive region. It deletes native
states 180, 181 and 218, replacing them by 163, 220 and 157 respectively.
The native labels are names: native 211 is a working helper, native 254 halt.
The delivered dense table has halt 209 and exactly 209 working states.

PROOF STATUS
============
The new ordinary mathematical argument establishes PA-formalizable blank
halting equivalence with the common U212 parent. Composing it with the
explicitly retained numerical-calculus and U/PA translations gives the
intended endpoint:

  PA |- not Halt(U209,blank) <-> Con(U) <-> Con(PA).

The release contains executable symbolic-induction evidence and mathematical
proofs. It does not contain a new Lean, Rocq, MM0, or exported PA endpoint
certificate. It does not assert consistency, unconditional nonhalting,
global minimality, or an independently ratified record.

CHECKED
=======
* All 3,909 source primitives and 5,083 ordinal control edges preserved.
* All 3,908 internal source-prefix interfaces independently checked.
* Ten exhaustive arbitrary-exterior fold cases and two engine-repair cases.
* All 414 ordinary prefold rows commute with the state quotient.
* Thirteen deliberately corrupted local constructions rejected, including
  the missing engine-entry repair; the local checker also passes with -O.
* 5,084 fresh arbitrary-natural runtime contracts, four list-induction laws,
  1,250,049 symbolic inferences, and all 418 literal rows covered.
* Exact common 48,140-step blank startup: full tape and full trace equal.
* Independent C++ regression: 15,252 primitive cases, 6,773,382 literal steps.
* All three incoming U211 full replays and the unary packet diagnostics pass.

The final fold-stage simulation expands one old step into one to five new
steps. That time bound does not cover the preceding address reassociation.
Finite regression and blank-prefix checks do not establish nonhalting.

REPRODUCE OFFLINE
================
Python 3.10+ and its standard library, with assertions enabled:

  python3 -B reproduce.py

The command verifies the release manifest, reconstructs exact machine/source
bytes in a temporary directory, binds the retained U212 archive and unchanged
induction engine, checks local paths/source/startup/comparison, and freshly
rederives all 5,084 universal contracts. The complete release is unchanged.
The preparation environment took about 80 seconds for the runtime phase.

  python3 -B reproduce.py --quick

The quick command explicitly skips the fresh unbounded runtime derivation.
It is not a replacement for the default full verification.

Optional independent finite executor (requires a C++17 compiler):

  g++ -std=c++17 -O3 code/check_finite_runtime.cpp -o /tmp/check_u209
  /tmp/check_u209 machine/u209.native.tm machine/sites.tsv

Rebuild the PDF in a working copy to avoid changing the sealed manifest:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF bytes may vary with TeX versions and metadata. The literal machine
and source bytes are deterministic.

ARCHIVE MAP
===========
report.tex, report.pdf, tables/  Mathematical report and complete dense table.
machine/                       Literal tables, source, state map, fixed recipe.
code/, reproduce.py            Standalone rebuild and verification programs.
baseline/                      Frozen U212 inputs and complete nested lineage.
comparison/                    Three U211 snapshots, source identities, census.
evidence/                      Fresh receipts and all symbolic case records.
research/                      Limited unsuccessful additional fold searches.
licenses/, NOTICE.txt          Retained attribution and terms.
SHA256SUMS                     Hashes of every other sealed release payload.

baseline/selected_U212.zip retains U213/U214/U218/U222 and the original
numerical-calibration paper and 23 logical reference files. Those references
have unbundled imports and are not a runnable new Rocq proof project.
The exact user-specified unary-theory archive is retained separately.

SOURCE SNAPSHOT
===============
VladimirReshetnikov/ProveIt, commit
da4ab9dd68ccfc47ac852118601eaf1fdae53795, docs/incoming.
The new candidate's dense SHA-256 is
5ded628d692ff442e4346c61eb3db3c77b0ac2c80c1ecced45cbfc483be40e08.
