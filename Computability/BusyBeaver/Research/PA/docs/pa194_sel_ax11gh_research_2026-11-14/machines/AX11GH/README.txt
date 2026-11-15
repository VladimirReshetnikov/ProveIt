PA194AX11GH: explicit-binder four-field AX with cache-only Shift
================================================================

This directory is an offline, reproducible construction of a new binary
single-tape 194-state machine relative to the numerical-calculus interface
of the supplied PA194 research family. It is not a sub-194 result and
does not complete the repository's absolute iPRA calibration to Con(PA).

Literal machine
---------------
machine/machine.tm has 194 working states, 388 rows, start state 0 and
halt label 194 (not counted). The head starts at position zero on an
entirely blank, two-way infinite tape; blank and tape alphabet are 0
and {0,1}, respectively. Rows are state/read/write/direction/target.

SHA-256:
513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1

The native machine has start 74 and halt label 254. The complete native
table and dense/native label correspondence are also included.

What changes
------------
The immediate parent is the incoming PA194AX11G. Its AX emitter, explicit
generalization binder, additional fourth operand, and no-push MP are
unchanged. Five physical rows replace Shift's sum test t+h=1 by h=1.
The new command behavior requires a partial Pop and an early-halting MP
compiler; the old AX11G compiler cannot simply be reused. The proof and
31 symbolic identities treat those cases, including all zero aliases.

Reproduce (Python 3.10+, standard library only, assertions enabled)
----------------------------------------------------------------
python3 build.py
python3 check_source.py
python3 check_emitter.py
python3 check_words.py --output machine/words.json
python3 audit_shift.py
python3 independent/check.py machine --output verification
python3 exchange/check_native_exchange.py
python3 exchange/check_exchange_independent.py exchange/native_exchange.json

build.py reconstructs the table from frozen parent inputs, checks all
simultaneous folds, replays 4778 symbolic source outcomes and verifies
the complete 57922-step blank initialization. It writes the generated
machine files in machine/. check_source.py independently binds the one
deleted source increment and all remaining CFG edges to the five rows.

The independent/check.py command derives list-sweep lemmas from the actual candidate
rows and independently replays every source outcome without arithmetic
box oracles. These are symbolic universal checks, not only tests of
small input values. They are executable mathematical evidence, not
proof-assistant kernel theorems. The full construction/theory distinction
is stated in ax11gh_proof.tex.

source_shift_audit.tex proves the changed Shift directly from primitive
source loops, including exact polynomial instruction counts. Its independent
4096-case replay checks indices and counts without standing in for the
all-natural induction. The exchange/ directory retains the fixed 18897-line
native-calculus certificate for exchanging the two universal-distribution
premises, with two independent replayers. It uses only restricted-rho and MP.

Attribution
-----------
The arithmetic runtime, numerical calculus, compiler and original source
are inherited from James Chang's PA196 work and the supplied ProveIt
research packets, with Wade/Gulchenko and K-family runtime ancestry.
Original licenses are in licenses/ and independent/reference/.
The exact source snapshot is ProveIt commit
603c58ca3bd6bf3222fcfc4e308e6b079f65d573.
Immediate parent: docs/incoming/pa194_ax11g_research_2026-11-14.zip.
The cache-only mechanism is from pa194_ax11h_research_2026-11-14 and
pa194gh_research_2026-11-14. This packet's new work is their combined
table/source, all-store compiler, explicit weak-induction justification,
and fresh replay against that table. It claims corpus-relative novelty,
not a new general principle of consistency encoding.

inherited_ax11g_commands.py is an attributed reference module. Its old
sum-Shift check_words() routine is deliberately not used; check_emitter.py
uses only its unchanged free-term emitter and four-field codec checks.
