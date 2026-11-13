#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group05-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'327b72ac8619a0bec1c73fd75954453863861274f7249ea80749c7e56401b97e','provider_preflight.py':'85e60cb66732f853022c5a974c7b5c36842e8b6e049c22c82b618ef974aa6e66','source-manifest.json':'109b393e9471e6662ed758706d9ab260484e8727366c3da1664cb85c3187c4f9','src/DiophantineConsistency/Norm38MacroPrefixQNCarry.lean':'c68a5a6d3aa61292fe900c2df32c4fe8199c1bfb005f4ef3e0ee2adc62eae97d'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Norm38MacroPrefixQNCarry.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='c68a5a6d3aa61292fe900c2df32c4fe8199c1bfb005f4ef3e0ee2adc62eae97d';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Norm38MacroPrefixGlarge'];assert re.findall(r'^theorem (\w+)',s,re.M)==['d10_q','d10_N'];assert re.findall(r'^#print axioms (\w+)',s,re.M)==['d10_q','d10_N']
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled q/N short-prefix preservation; no Lean replay'},sort_keys=True,indent=2))
