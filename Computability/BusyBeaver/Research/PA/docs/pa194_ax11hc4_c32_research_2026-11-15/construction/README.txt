Two new 194-state physical designs
=================================

Preferred consistency construction: PA194AX11HC4, in ax11hc4/machine/.
It preserves the exact source of the written iPRA-calibrated AX11H parent,
changes the physical locations of T,A,D,Y, and has an exact 57,406-step blank
initialization. Read ax11hc4/PROOF_TRANSFER.txt for the iPRA transport argument
and its explicit inherited-calibration scope. The new literal certificates
instantiate the mathematical soundness audit of the parent's interpreter;
no new end-to-end Lean/Rocq proof is claimed.

Additional physical construction: PA194C32, in cycle32/.
It changes the T,A,D positions and exchanges H,X in the primary PA194 source.
Its exact startup is 56,250 transitions. Read PROOF_C32.txt for its relative
source equivalence and the different logical-calibration status of that
older parent. It is not a sub-194 machine.

Reconstruct complete tables and exact startup offline:
  python3 reconstruct.py --output rebuilt_c32
  python3 ax11hc4/reconstruct.py --output rebuilt_hc4

Replay all symbolic source contracts in two languages:
  python3 verify_source.py
  node verify_source.cjs
  python3 ax11hc4/verify_source.py
  node ax11hc4/verify_source.cjs

Replay the stronger universal literal checks, including positive affine clocks
and four arbitrary-list lemmas derived from each candidate's actual rows:
  python3 verify_literal.py C32
  python3 verify_literal.py HC4

Python 3.10+ and Node.js18+ suffice. No third-party packages are used.
Do not enable Python -O or PYTHONOPTIMIZE; inherited engines use assertions.
The compact source grammars regenerate all 3,673 or 3,671 source sites.
They replace large copies of the site/instruction JSON data while retaining
canonical hashes checked against the pinned original source arrays.

The completed literal receipts are:
  receipts/literal/receipt.json                  (C32,4,780 outcomes)
  ax11hc4/receipts/literal/receipt.json           (HC4,4,778 outcomes)
The contract arrays and four list-lemma certificates are beside them.
Both machines have 194 graph-reachable working states and 388 binary rows.

SEARCH_METHOD.txt documents fresh completed searches for 193-state local
contractions and their exact limits. The C++17 search is optional and is not
needed to reconstruct or verify either accepted machine.

The source calculus, compiler ancestry, arithmetic engine, and inherited
logical proofs remain attributed to their original authors. Licenses are
retained under licenses/, and PROVENANCE.json pins copied inputs. The new
work is the literal physical allocations and their verification/transport.

