PA194AX11G: eleven-entry AX with an explicit generalization binder
================================================================

WHAT WAS CONSTRUCTED

A new literal 194-working-state, binary, single-tape, blank-start machine.
The machine stores the gate in its axiom stack, reads four AX fields, and
uses the explicit AX operand as the saved generalization binder. Its
uniform proof compiler generalizes without an offset-setting command.

The count is 134 fixed controls + 67 AX readers - 7 compatible folds = 194.
Dense working labels: 0..193; start: 0; halt: 194, uncounted. Native start: 74;
halt: 254. All 194 controls are reachable in the transition graph. Every
transition writes one bit and moves exactly one square L or R.

Dense SHA-256:
7e1c6442816e5df05e961f2057719252a1976c9a195a786978bf1e2d3c8e466d
Native SHA-256:
08e4627b7a9beb1be6c9e82b03b9ff5f570ececde60f58fa7e0c1a4996efe378

PROOF STATUS

This package proves the combined command algebra and supplies the exact
literal implementation and universal symbolic physical certificates.
It preserves the parent numerical calculus's refutability condition.
The inherited research contains an ordinary mathematical PA calibration.
No new completed iPRA calibration, Lean/Rocq endpoint, or machine below 194
is claimed. The current repository expressly leaves machine-specific iPRA
obligations open. A finite run or Python PASS cannot replace them.

The separate report identifies the exact conditional iPRA transport and
remaining model-uniform obligations. Read proof.tex and command_proof.tex
for the new relative argument. References under references/ are attributed
historical arguments, retaining their original claims and terminology.

EXACT CHANGE FROM PA194G

Native row (2066,1): old 0 L 302; new 1 R 19. All other native rows agree.
The source replaces the final AX breakTo1 leaf by the existing 19-site push
macro. It then falls into the full MP reader, consuming a fourth operand z.
PA194G already uses no-push successful MP, so no additional MP edit is made.

If D=d+x,H=h+y, the exact new AX command effect is

  A(c,x,y,z)(t,w,d,h)=(0,[g,q1,...,q9,t;w],z,0),

where q9=U(c,h), using the incoming cache h, NOT H=h+y. The remaining nine
formulas are the gate, diagonal, six ordinary heads (Q orientation for
quantifier distribution), and dominated implication head. They have residue 0
mod 4. The saved U(c,h) has residue 2 and is at least 2.

Push=A(0,0,0,0);Shift^10;MP(0).
Pop=A(0,0,0,0);Shift^12, total even at visible top 1.
Generalize_i=Push;Shift;A(i,0,0,0);Shift^11.
The final refutation test is Shift; Pop is deliberately NOT a false test.
The MP proof compiler reserves a zero under its two premises.

The four fields are encoded in order c+2,y,x,z through nested Cantor pairs.
The old three-field AX encoding must not be reused.

REPLAY

Python 3.10+ and standard library, with assertions enabled:

  python3 -B verify.py

This rebuilds in a fresh temporary directory, compares all core artifacts,
checks complete source relocation and all-store command words, repeats both
universal physical checkers and whole blank startup. Frozen evidence is
not overwritten. A shortened smoke check:

  python3 -B verify.py --quick

The quick check skips both long physical symbolic replays. The complete
component checks HAVE been run for this delivery, with results below.

  python3 -B build.py --output /absolute/fresh/directory
  python3 -B check_commands.py --output /absolute/fresh/receipt.json
  python3 -B verification/check_physical.py machine --output /absolute/fresh/results

OBSERVED VERIFICATION

3,672 source sites; 4,779 branch-sensitive outcomes.
Construction checker: 1,483,363 symbolic operations; maximum 470 per outcome.
Independent literal checker: 1,083,079 symbolic operations; maximum 379.
Four register-list induction lemmas were rederived from actual table rows;
no arithmetic-box oracle was used in the independent pass. Its minimum
positive-duration constant is 3. Two independent source resolvers agree.
All 28 local fold cases pass against the simultaneous final table.

Blank startup: 58,154 literal transitions to native 84, head -2, logical
registers (2,0,0,0,0,0,0,0,0), 26 unit-valued spare blocks. The entire finite
support and blank exterior are checked, not a bounded tape window.

The source splice replaces old ordinal 3553 by new 3553..3571, followed by
MP reader entry 3572. All 3,653 exterior source sites agree after relocation;
no exterior edge enters the splice interior. The inserted push matches
an existing source block at ordinal 50, including its internal successors.

FILES

machine/           Authoritative tables, labels, source, grammar, receipts.
construction/      Attributed inherited compiler and symbolic engine.
verification/      Independent literal checker, reference engine, full logs.
inputs/            Frozen parent PA194G artifacts, sufficient for rebuilding.
references/        Attributed calibration texts and Q exchange certificate.
command_proof.tex  Independent new audit of exact command words.
proof.tex          Literal/source preservation and exact proof boundary.
PROVENANCE.json    Pinned repository paths and hashes for inherited material.

Source snapshot: 32d0d8b7d93a63ad4106c18cdb29b37927acdad2.
Parent packet: Computability/BusyBeaver/Research/PA/docs/
PA194B_PA194G_research_2026-11-14/generalizer/.
The full delivery's comparison directory supplies the current all-corpus
identity check. A graph distinction is not a claim of semantic inequivalence
or a lower bound on achievable state count.
