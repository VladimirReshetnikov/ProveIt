Smaller complete checker modules for the existing iPRA presentations
==================================================================

Recommended arbitrary-input interface: code/strict637.py.
It checks both the full closed native Eq/D goal and the entire certificate's
integer/list alphabet. Run it on a JSON proof with standard input:

  python3 code/strict637.py < fixtures/strict_proofs/computation_zero_local.json

A valid proof prints exactly ACCEPT and exits successfully. Other outcomes
are rejection. Python -O does not change this convention.

Other measured contracts:
  code/compact479.py: inherited compact guarded public-goal contract.
    The caller supplies a canonical closed guarded Eq/D public goal. The
    compact module is not a whole-input or public-grammar validator.
  code/native607.py: full closed native Eq/D public-goal validation, without
    a whole-input alphabet gate. Correctness retains the inherited consumed
    integer/list certificate contract; unused JSON prefix values are allowed.

Metrics (CPython 3.12.14):
  file                       tokens    AST nodes    normalized bytes
  controls/compact487.py        276       308              487
  code/compact479.py            272       304              479
  controls/native629.py         324       374              629
  code/native607.py             337       383              607
  controls/strict646.py         343       392              646
  code/strict637.py             344       392              637

Run python3 reproduce.py to regenerate verification.json. Controls, fixtures,
source identities, and the inherited license are bundled. No fixture,
compiler, decoder implementation, test driver, or support file is imported
by any measured checker module.

The new compact byte record improves the observed envelope from
(248 tokens,270 AST nodes,487 bytes) to (248,270,479), attained by different
programs. It does not improve the independent token/AST record and does not
prove a mathematical lower bound. The arithmetic axioms are unchanged.
See PROOF_NOTES.txt for universal simulations and the distinction between
compact, native, and strict contracts.
