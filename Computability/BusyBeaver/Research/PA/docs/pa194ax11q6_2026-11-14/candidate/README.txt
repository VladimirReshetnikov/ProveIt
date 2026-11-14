PA194AX11Q6
===========

This is an explicit 194-working-state binary, one-tape, blank-start machine.
It is a new composition of the supplied AX11 fallthrough protocol, Q's
premise-exchanged sixth head, radix-six constructor arithmetic, and no-push
modus ponens. It does not establish a state count below 194.

The written argument, using the explicitly retained inherited calibration,
establishes in ordinary mathematics:

  PA proves: not Halt(PA194AX11Q6, blank) if and only if Con(PA).

It is not a newly compiled end-to-end Lean/Rocq theorem or iPRA equivalence.
Python success is evidence for the exact finite and universal-symbolic
contracts stated in the proof; finite simulation is not used to infer
infinite nonhalting.

MACHINE
-------
machine/machine.tm is authoritative. Each row is

  current_state read_bit write_bit L_or_R next_state

Working states are 0..193, initial state 0, terminal halt label 194.
The tape is two-way infinite, initially all zero, with head at coordinate 0.
There are 388 rows and every transition moves exactly one cell.

Dense SHA-256:
9933fe380b5242981255a0b75da6b305fc88df7031e753411a51efaf7dbe0dab

Native SHA-256:
3b0a6a7af5bc9ef9b96fab2e810b06f2b219d2c6a703d9bc4862764688372546

The native table starts at 74, halts at 254, and is related to the dense
table by machine/labels.json. Native labels are identifiers, not a state count.

VERIFICATION
------------
Python 3.10+ standard library suffices. Run without -O:

  python3 -B reproduce.py

The runner makes a fresh temporary copy, rebuilds exact table bytes, checks
all construction contracts, the new source splice, symbolic command words,
the finite K/S/MP premise-exchange certificate, the exact blank startup,
and the independent literal-table contracts. Replays can take several
minutes. Logs and receipts remain in the printed temporary directory.

Optional fast structural check, omitting both long universal tape replays:

  python3 -B reproduce.py --quick

Use --work NEW_DIRECTORY to retain the fresh copy at a selected path and
--receipt FILE.json to retain a top-level receipt. The original release is
not overwritten by the replay runner.

Individual commands:

  python3 -B build_ax11q6.py --output NEW_DIRECTORY
  python3 -B proof/source_splice.py --machine NEW_DIRECTORY
  python3 -B proof/commands.py --machine NEW_DIRECTORY --output commands.json
  python3 -B verification/check.py NEW_DIRECTORY

WHAT CHANGES
------------
AX now pushes eleven entries (the saved old top plus all ten generated
heads), then consumes an extra field z through the full MP operand reader.
The exact final visible state is top=0, cache=0, offset=z. Its proof-word
compiler deliberately uses z=0, while soundness covers every z.

Formula constructors are I(A,B)=6*Cantor(A,B), M(a,b)=I(a,b)+1,
U(a,B)=I(B,a)+2, E(a,b)=I(a,b)+3. The sixth axiom head is
U(d,I(a,h)) -> (U(d,a) -> U(d,h)). These are recurring source semantics,
not changes confined to labels or the halt transition.

The machine has 135 fixed controls + 67 AX readers - 8 folds = 194.
The complete source has 3,794 sites and 4,901 primitive outcomes. All eight
folds have their exact incoming-context and local-tape identities checked.
The source-splice certificate replaces the QN6 exit at site 3673 by the
19-site Push, with fallthrough to MP's register-8 reader at site 3692;
all other 3,775 source instructions and successors relocate exactly.

FRESH RESULTS
-------------
Construction: all 4,901 outcomes pass; 1,571,333 symbolic operations,
maximum 490 per outcome. Exact complete blank initialization takes 58,320
transitions and reaches source site 25, native state 84, head -2, gap 48,
logical registers (2,0,0,0,0,0,0,0,0), and 26 unit spare registers.

The independent literal replay also passes all 4,901 outcomes, using
1,149,402 symbolic operations, maximum 397 and minimum positive duration
constant 3. It rederives four generic register-list lemmas from literal rows,
uses no arithmetic-box oracle, and checks source successor agreement by two
independent implementations. Its receipt is machine/independent/receipt.json.
machine/commands.json checks all
stack selectors, zero aliases, protected tails, early halts, and the
four-field scheduler encoding. Graph novelty is checked separately against
the pinned 72-delivery census in the complete report.

PROOF AND ATTRIBUTION
--------------------
proof/composition.tex is a complete new proof specialization. Its inherited
logical calibration and premise-exchange dependencies are retained under
proof/references/. PROVENANCE.json pins the input files to ProveIt commit
4be5c6e3a10292a7466f5d3687e3b39615ff049b. Attribution and licenses of
James Chang, Wade, and ProveIt contributors are retained in licenses/.
vendor/ and verification/reference/ contain the attributed proof engines.

The substantive new contribution is the exact composition and its checked
source/physical binding. It does not claim to invent its individual
ingredients, prove a lower bound, or settle the repository's stronger
unfinished iPRA formalization goal.
