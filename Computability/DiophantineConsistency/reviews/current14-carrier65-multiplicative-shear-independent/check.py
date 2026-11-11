#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert hashlib.sha256(p.read_bytes()).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(p.read_bytes());base=g['source'];names={r[0] for r in base};assert len(names)==65
for anchor in ('N1','Nt'):
 rows=[[r[0],r[1]]+['rank_times_anchor' if x=='R' else x for x in r[2:]] for r in base]+[['rank_times_anchor','*','R',anchor]];assert len(rows)==66
 deps={r[0]:r[2:] for r in rows};seen=set();stack=[g['output']]
 while stack:
  x=stack.pop()
  if x in deps and x not in seen:seen.add(x);stack.extend(deps[x])
 assert len(seen)==66
 # Kahn topological sort validates acyclicity and includes all arithmetic nodes.
 pending={r[0]:r for r in rows};ready=set(g['witnesses']+g['fixed_numerals']);order=[]
 while pending:
  eligible=[r for r in rows if r[0] in pending and all(not isinstance(x,str) or x in ready for x in r[2:])];assert eligible,('cycle',anchor)
  for r in eligible:ready.add(r[0]);order.append(r[0]);del pending[r[0]]
 assert len(order)==66 and order.index('R')<order.index('rank_times_anchor') and order.index(anchor)<order.index('rank_times_anchor')<order.index('tau') and order.index('rank_times_anchor')<order.index('cTminusR')
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-main-norm-shear-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','scope':'R times N1 or Nt gives acyclic 66-live-gate anchor shear; zero preservation follows independent anchor proof; no Lean/minimum claim'},indent=2))
