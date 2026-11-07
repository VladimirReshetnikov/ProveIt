#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group05-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'9cee097cfc4eaa76d93526e08ee3a5ae48e6e64ab8a9d5329d80188039e2180f','source-manifest.json':'029d8a59e2df4231ae2ab69c850b43a96f48d895c461a7b7960ac254b5a68be9','src/DiophantineConsistency/Sign33MacroPrefixQNCarry.lean':'a5e7f505e0c23c3b2d2923645180dc43e99cd854d6c1f9a5ebf62b2ef29d633d'}.items():assert H(P/n)==h
s=(P/'src/DiophantineConsistency/Sign33MacroPrefixQNCarry.lean').read_text();old=D/'research/nine-seed38-jones-prefix-group05-check/src/DiophantineConsistency/Norm38MacroPrefixQNCarry.lean';assert H(old)=='c68a5a6d3aa61292fe900c2df32c4fe8199c1bfb005f4ef3e0ee2adc62eae97d' and s==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34')
rows=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['imports']==['DiophantineConsistency.Sign33MacroPrefixGlarge'] and rows[0]['source_sha256']==H(P/'src/DiophantineConsistency/Sign33MacroPrefixQNCarry.lean')
for name,birth in [('q',3),('N',4)]:
 part=s.split('theorem d10_'+name,1)[1].split('#print axioms',1)[0].split('\ntheorem ',1)[0]
 got=[int(v) for v in re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+)',part)];assert got==list(range(9,birth-1,-1)),(name,got)
 assert f'prefix_{name} a' in part and '5 ^ 34' in part
assert '5 ^ 39' not in s and s.count('#print axioms d10_')==2
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':1,'scope':'q and N preservation at d10 only'},sort_keys=True,indent=2))
