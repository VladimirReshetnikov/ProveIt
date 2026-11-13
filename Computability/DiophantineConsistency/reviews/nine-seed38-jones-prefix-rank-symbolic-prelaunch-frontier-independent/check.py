#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-symbolic-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'2eef945ec9cda74163e1a0f87b6d89a498c630b0ce95ad27fc9c8cd85681b4ee','provider_preflight.py':'abce8225229f14b1ed4880331e2063d8b75f13b706542f5ddc766c61e3166a78','source-manifest.json':'ae3f668f4becb82b9e8e4bd1ac108bee5eaf91d52b94f7d088959357edd2153f'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroRankValuesSums','bbba5ddc203be9f227a16a34972094c0df0b39a02d504a153d531b1d08d5e457',['Norm38MacroRankComposition','Norm38MacroPrefixE','Norm38MacroPrefixEll','Norm38MacroPrefixLambda'],['d10_e_value','d10_ell_value','d10_lambda_value']),('Norm38MacroRankValuesOther','ee3eebe4c841142a901c1cb93e77e2a59999be949e7d6557ce1a36d52814648b',['Norm38MacroRankValuesSums','Norm38MacroPrefixGsmall','Norm38MacroPrefixTheta'],['d10_b_value','d10_g_value','d10_theta_value']),('Norm38MacroRankSymbolic','e87602c26e25d62e2ab8f72aa1864a3f6017dd105d9a7f721099e7b1ffdd4f60',['Norm38MacroRankValuesOther'],['d11_rank_symbolic'])];assert len(rows)==3
for row,(n,sha,imps,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+x for x in imps];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for prefix,idx,casts in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(prefix)==int(idx)+1+casts.count('.castSucc')
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==3
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled symbolic d11 rank values; no Lean replay'},sort_keys=True,indent=2))
