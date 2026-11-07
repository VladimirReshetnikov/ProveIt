#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-rank-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='96108a0b7ba16b87ba6fe17e85d69f279d56f19729cd27c70b0b9b08c25d1307' and H(P/'source-manifest.json')=='4d560a3a609dd3b83fbe9f2d9656b5d22c4fc11d68ed68a8437e7b225cbd4cdc'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'] for r in m]==['DiophantineConsistency.Sign33MacroRankRaw','DiophantineConsistency.Sign33MacroRankCarry'];texts=[]
for row,n in zip(m,['Raw','Carry']):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroRank{n}.lean';old=D/'research/nine-seed38-jones-prefix-rank-retry01/src/DiophantineConsistency'/f'Norm38MacroRank{n}.lean';s=f.read_text();assert s==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34') and H(f)==row['source_sha256'];texts.append(s)
a,b=texts
assert 'rankRaw (indexZ seed 0 : R)' in a and all(f'd10.values a ⟨{i}, by decide⟩' in a for i in range(9)) and 'd11.values a (Fin.last 10)' in a
assert all(x in b for x in ('d10_b_carry','d10_B_carry','d10_q','d10_N','d10_e_carry','d10_ell_carry','d10_lambda_carry','d10_g_carry','d10_theta_carry','5 ^ 34'))
assert m[0]['imports']==['DiophantineConsistency.Sign33MacroPrefixCarrySums','DiophantineConsistency.Sign33MacroPrefixCarryOthers'] and m[1]['imports']==['DiophantineConsistency.Sign33MacroRankRaw']
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':2,'scope':'symbolic d11 raw rank and carried short-prefix identity; no rankCode or output semantics'},sort_keys=True,indent=2))
