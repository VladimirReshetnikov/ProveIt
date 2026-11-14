TAG196N: a 196-state machine with exchanged constructor residues
================================================================

This secondary research construction changes the universal-quantifier residue
from 2 to 3 and the equality residue from 3 to 2, preserving implication 0,
membership 1, truth 0, contradiction 1, and coefficient four. It uses the
no-push MP controller with the original t+h=1 Shift test.

Its mathematical proof is supplied in proof/calculus_transports.tex and
proof/command_compiler.tex, with the inherited numerical-calculus/PA
calibration identified explicitly. The main research report supplies those
references. The result is an ordinary mathematical PA-provable equivalence,
not a newly compiled Lean or Rocq theorem. It does not improve the 194-state
bound. Only the residue-permutation part of the general calculus-transport
fragment is needed for this machine; its head-exchange part is separate work.

Machine convention
------------------

One binary two-way tape, blank symbol 0, initial head position 0, dense start
state 0, working states 0 through 195, separate terminal halt label 196.
Every row writes a bit and moves L or R. There are 392 transition rows.
The native presentation has start 74 and halt 254.

Count: 135 fixed controls + 71 AX readers - 10 simultaneous folds = 196.
Source: 3,666 primitive sites and 4,767 universal physical outcomes.
Fresh physical verification: 1,535,770 symbolic iterations, maximum 517.
The entire blank tape reaches its clean source frame after 58,320 steps.
Arithmetic boxes are unchanged inherited dependencies of the symbolic check.

Relative to the frozen original TAG196 table, the only native-row change is
(164,1): 1 R 98 becomes 1 R 114. It removes the successful-MP zero push.
An independent source audit checks the unique incoming edge to deleted
interval [3646,3665), every remaining opcode and successor, and the exact
literal-row difference.

Dense SHA-256:
  e250b15fb2ad284cffaab5ed2842593f51d2ad7eec6c707aa42786c5ce3cfac6
Native SHA-256:
  56c34634a1e60f73545bd14617bd47f3933c85bae6bfd0854bf9dd6117f09c4c

Reproduction
------------

From this directory, using Python 3.10+ and its standard library:

  python3 -B verify.py
  python3 -B check_splice.py
  python3 -B check_source_bindings.py
  python3 -B check_emitter.py inputs/grammar.json --mask 0 --tag-swap --output emitter_receipt.json
  python3 -B proof/recoding_audit.py

Assertions must remain enabled. The verifier regenerates machine/*.json and
both literal tables. No checkout or network is required. The emitter checker
imports neither the compiler nor the runtime. It checks exact free-formula
terms for all ten pushed entries and the final gate. The recoding audit is a
bounded supporting calculation; the separate proof of involution is universal.

The source-binding checker verifies all 46 arithmetic-box rows against the
frozen original table, all 61 constructor prefixes and four-increment bodies,
and equality of the complete resolved instruction graph before and after
reassociating the four-increment macro. The no-push source change is checked
separately by the 19-instruction splice auditor.

The primitive instructions in the new source are certified for arbitrary
natural registers, an affine header gap, and a complete symbolic register
file through the inherited block interface. The startup check covers all
tape ones and the zero exterior. These are not bounded samples of the main
proof-search run and do not infer consistency or infinite nonhalting by test.

Inherited attribution and licenses are retained under licenses/. The main
report describes the unsuccessful search for a 194-state realization of this
alternative coding and the separate accepted 194-state fallback.
