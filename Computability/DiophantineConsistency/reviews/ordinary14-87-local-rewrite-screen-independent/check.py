#!/usr/bin/env python3
"""Reproduce the bounded search and check its sphere source delta; no Lean."""
from pathlib import Path
import json,subprocess,sys,hashlib
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-local-rewrite-screen';G=D/'research/ordinary14-shifted-guard87-probe/candidate.json'
readme=(A/'README.md').read_bytes()
tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary14-87-local-rewrite-screen-independent/`.\n'
assert hashlib.sha256(readme).hexdigest()=='83a5e61b80a9d5bc5e55a33a0d895b5bf2f9519d281fc349a19ebe1cc6349089' and readme.endswith(tail)
restored=readme[:-len(tail)].replace(b'This packet does not cover arbitrary new integer leaves,',b'This packet has not received separate independent review. It does not cover arbitrary new integer leaves,')
assert hashlib.sha256(restored).hexdigest()=='258ff4b747e85505586eb5187a2ad261ad047287494d626a44d3a2c9d4b4d012'
g=json.loads(G.read_bytes()); old=g['source']; out=g['output']; new=[]
for name,op,a,b in old:
 if name=='Fam':assert [name,op,a,b]==['Fam','-','Fa',1];continue
 if name=='Fam2':assert [name,op,a,b]==['Fam2','*','Fam','Fam'];a=b='Fa'
 if name==out:name='sphere_sum'
 new.append([name,op,a,b])
new.append([out,'-','sphere_sum',1]);assert len(old)==len(new)==87
for rows in (old,new):
 seen=set(g['witnesses']+g['fixed_numerals']);live={out}
 for name,op,a,b in rows:
  assert name not in seen and all(isinstance(x,int) or x in seen for x in (a,b));seen.add(name)
 for name,op,a,b in reversed(rows):
  if name in live:live.update(x for x in (a,b) if isinstance(x,str))
 assert all(r[0] in live for r in rows) and set(g['witnesses']+g['fixed_numerals'])<=live
# The mod-4 sign control is a tautology over all residues.
for a in range(4):
 for f in range(4):
  for V in range(4):
   for y in range(4):
    d=((a+2)**2-1)%4;Q=d*(f*f-1)%4;Fa=(y*y-Q*(y*y-V*V))%4
    assert Q in (0,1) and Fa in (0,1)
for args,receipt in [(['local.py'],'local-result.json'),(['beam.py'],'beam-parent.txt'),(['beam.py','--sphere'],'beam-sphere.txt')]:
 r=subprocess.run([sys.executable,'-I','-S','-B',str(A/args[0]),*args[1:]],cwd=D,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)
 assert not r.stderr and r.stdout==(A/receipt).read_bytes()
print(json.dumps({'scope':'positive-domain sphere proof and listed bounded searches; no global minimality or Lean','graph_delta_and_liveness':True,'mod4_exhaustive':True,'three_receipts_reproduced':True,'readme_sha256':hashlib.sha256(restored).hexdigest()},sort_keys=True,indent=2))
