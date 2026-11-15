#!/usr/bin/env python3
"""Bind frozen tables/contracts to the uniform quadratic relative clock bound."""
from pathlib import Path
import hashlib,json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required')
ROOT=Path(__file__).resolve().parents[1]
C=[542,8]+[4]*9+[2,2]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
results=[]
for parent,new in [('PA194AX11GH','PA194LCAX11GHF'),('PA194AX11GHS','PA194LCAX11GHSF')]:
 assert json.loads((ROOT/'inputs'/parent/'instructions.json').read_text())==json.loads((ROOT/'machines'/new/'instructions.json').read_text())
 for name,table,cert in [(parent,ROOT/'inputs'/parent,ROOT/'verification/parent_recorded'/parent),(new,ROOT/'machines'/new,ROOT/'verification/independent/results'/new)]:
  receipt=json.loads((cert/'receipt.json').read_text());cs=json.loads((cert/'contracts.json').read_text())
  assert digest(table/'machine.tm')==receipt['dense_sha256']
  assert digest(table/'machine.native.tm')==receipt['native_sha256']
  assert digest(cert/'contracts.json')==receipt['contracts_sha256']
  assert len(cs)==receipt['source_outcomes']
  mn=min(c['duration'][0]for c in cs);mx=[max(c['duration'][i]for c in cs)for i in range(13)]
  assert mn>=3 and all(x<=y for x,y in zip(mx,C)),(name,mn,mx)
  assert receipt['startup_steps']<=57922
  results.append(dict(name=name,source_outcomes=len(cs),minimum_duration_constant=mn,maximum_duration_coefficients=mx,startup_steps=receipt['startup_steps'],contracts_sha256=receipt['contracts_sha256'],dense_sha256=receipt['dense_sha256'],origin='retained upstream literal certificates'if name==parent else 'newly replayed literal certificates'))
receipt=dict(status='PASS',envelope=C,source_step_bound={'constant':702,'slope':26},normal_source_clock=[57922,689,13],cross_halting_clock=[58624,715,13],coefficient_order=['constant','gap']+['r'+str(i)for i in range(9)]+['first_spare','tail_width'],machines=results,scope='Finite coefficient audit; the iPRA soundness and synchronization argument is written in proof/relative_proof.tex, not kernel checked.')
print(json.dumps(receipt,indent=2))
if len(sys.argv)>1:Path(sys.argv[1]).write_text(json.dumps(receipt,indent=2)+'\n')
