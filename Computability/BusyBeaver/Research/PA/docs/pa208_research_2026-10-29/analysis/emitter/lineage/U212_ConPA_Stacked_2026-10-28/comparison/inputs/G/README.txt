U213 ConU reduction — 28 October 2026

RESULT
213 working states, two symbols, blank bi-infinite tape, start state0.
Native terminal254 has no transitions. Dense table has working states0..212
and terminal213. There are426 transitions. No smaller/global-minimality claim.

The new construction preserves the incoming U214 proof-search semantics.
Combining the new ordinary simulation proof with the explicitly inherited
U214/U218/U222 numerical-calculus and theory calibration yields the intended
PA-provable equivalence: U213 does not halt iff Con(U), equivalently Con(PA).
No newly compiled proof-assistant certificate or explicit PA derivation is
claimed. The final report details these trust boundaries.

NEW STEP
Eight closed source reassociations (exact ordered CFG unchanged) expose
native115 and214 as a left-tagged pair. Existing helper155 distinguishes the
left tag; deleting115 saves one state. The final source has199 distinct
subtrees (one MORE than U214), showing that source DAG size alone is not a
physical-state objective. An earlier16-rotation candidate is rejected because
it destroys blank startup, even though its generic runtime checks pass.

CONTENTS
paper/report.tex and report.pdf: report and ordinary mathematical proofs.
machine/: exact native and dense transition tables, renaming and source sites.
inputs/: unchanged U214.zip, pinned predecessor table/source/startup, recipe.
code/: deterministic builder, independent CFG/rotation/fold/startup checkers,
      inherited symbolic induction engine adapted to native labels.
evidence/: recorded checks; research/: comparisons and rejected candidate.
MANIFEST.json: SHA256 of every packaged file except itself.

REPLAY (Python3 standard library only; no network)
  python3 reproduce.py
  python3 reproduce.py --full
The full option repeats all5109 arbitrary-register symbolic cases and checks
all outputs exactly. The finite independent checks also run under -O.
The assertion-dependent universal engine intentionally refuses -O; this
refusal is itself tested. Replay uses a temporary directory and verifies the
sealed inputs remain unchanged. PDF compilation is separate (pdflatex twice).

IDENTITIES
Native SHA256 9bd9145a7e0aebb04ed5376da96f7ab48271c50954b688909f7d172cab1c5ee2
Dense SHA256 6536fe056f1eb006842c46d12b38a9228a09c94db1d90e6a6a9feaba15cae3fe
Source SHA256 d2ac2ea66ba792394c68f65212de2c9d680088a7c40112eab774ccedfce757e2

Opening ProveIt pin54c7e9e5176d22d6d6793ec1eb83780dfce278e9.
Closing inspection5c7a4716a51764f0f388360455c9c515401b9581:
six intervening commits touched DiophantineConsistency, not these machines.
