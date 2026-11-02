#!/usr/bin/env python3
"""Check that the exposed parts duplicate the already graph-checked literal."""
import hashlib
from pathlib import Path
import subprocess
import sys
if not __debug__:
    raise RuntimeError('checks require Python assertions enabled')
here=Path(__file__).resolve().parent
literal=here.parent/'literal-prototype/Ordinary12Literal.lean'
source=here/'Ordinary12ConcreteSplit.lean'
def section(s):
    return s[s.index('  let j : Expr'):s.index('  -- END LITERAL GRAPH')+len('  -- END LITERAL GRAPH')]
def check(s):
    assert section(s)==section(literal.read_text()), 'literal graph mismatch'
    assert s.count('  ⟨qm,Z,g41,U,a,c,Dstar,AN,oneQ,vn,den,Q⟩')==1, 'parts tuple mismatch'
    assert s.count('firstPattern (parts p).qm (parts p).z (parts p).n')==1
    assert s.count('mainPattern (parts p).u (parts p).a (parts p).c (parts p).d')==1
    assert s.count('ordinaryPattern (parts p).an (parts p).x (parts p).y (parts p).den (parts p).q')==1
s=source.read_text(); check(s)
for mutant in (s.replace('let qm := J * beta','let qm := J + beta',1),
               s.replace('⟨qm,Z,g41','⟨qm,Z,g40',1),
               s.replace('firstPattern (parts p).qm','firstPattern (parts p).z',1)):
    try: check(mutant)
    except AssertionError: pass
    else: raise AssertionError('mutation accepted')
r=subprocess.run([sys.executable,str(here.parent/'literal-prototype/check_literal.py')],text=True,capture_output=True)
if r.returncode: raise RuntimeError((r.returncode,r.stdout,r.stderr))
print('PASS_CONCRETE_PARTS_BINDING 100 rows 12 parts 3 mutations rejected')
