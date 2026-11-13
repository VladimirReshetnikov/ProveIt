#!/usr/bin/env python3
"""Accept only the three exact source-pinned standard-theory simp warnings."""
from pathlib import Path
from hashlib import sha256
import json,sys
H=Path(__file__).resolve().parent;D=H.parents[1];OBS=H/'observations/attempt02'
SOURCE=D/'Lean/DiophantineConsistency/IPRAStandardTheory.lean'
EXPECTED=H/'expected-standard-warning.txt'
PINS={
 SOURCE:'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
 OBS/'stage-04.source.lean':'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
 OBS/'stage-04.stdout':'f5818e501c68cad86a28a22ddd349e1e0880d37e22c1decb1580bf71cdc7e9f8',
 OBS/'stage-04.stderr':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
 OBS/'stage-04.json':'a6c83a28ff10a68f8109a7d2ffd6628dcf14860785b8df38e3589b5d1cf24d9a',
 EXPECTED:'97d21d17b2e82cd1f87c74a35b3bb9e8fd98d610e6cb33b7f8e1cf1faab59006'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
need(len(sys.argv)==3,'expected retry stdout and source paths')
for p,h in PINS.items():need(sha(p)==h,'baseline drift '+str(p))
d=json.loads((OBS/'stage-04.json').read_text());need(d['exit']==0 and d['reason'] is None,'invalid baseline process')
old_source=d['command'][-3];new_source=sys.argv[2]
old=(OBS/'stage-04.stdout').read_text();new=Path(sys.argv[1]).read_text();expected=EXPECTED.read_text()
need(old.count(old_source)==3 and new.count(new_source)==3,'warning source count')
need(old.replace(old_source,'<SOURCE>')==expected and new.replace(new_source,'<SOURCE>')==expected,'warning text changed')
need(expected.count('warning:')==3 and 'error:' not in expected and 'sorryAx' not in expected,'invalid expected warnings')
print('PASS exact three source-pinned unused-simp-argument warnings')
