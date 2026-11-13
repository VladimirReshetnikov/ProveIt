#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-rank-symbolic-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'30c3aa07efc46971a8940fb8efc1931f2a4ef6c9312f0435f2a590eb0665995d','source-manifest.json':'b4e5cc850d869034f541013811970a37d38528b40c9833ce2933d37175a340d3','values-survey.py':'4a0b1384aef69c99413ac545406e3a99463467147274b0eb2dc15ccf3cb77206'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];suffixes=['ValuesSums','ValuesOther','Symbolic'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroRank'+x for x in suffixes];texts=[]
for row,x in zip(m,suffixes):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroRank{x}.lean';old=D/'research/nine-seed38-jones-prefix-rank-symbolic-check/src/DiophantineConsistency'/f'Norm38MacroRank{x}.lean';s=f.read_text();t=old.read_text().replace('Norm38','Sign33').replace('codingStar 38 4','codingStar 33 4').replace('codingExpo 38 4','codingExpo 33 4').replace('Finset.range 38','Finset.range 33').replace('5 ^ 39','5 ^ 34');assert s==t and H(f)==row['source_sha256'];texts.append(s)
a,b,c=texts
for n,k in [('e',4),('ell',5),('lambda',6)]:assert f'd10_{n}_carry a).trans (prefix_{n} a)' in a and f'Fin.last {k}' in a
for n,k,base in [('b',0,'d9_b'),('g',7,'prefix_g'),('theta',8,'prefix_theta')]:assert f'd10_{n}_carry a).trans ({base} a)' in b and f'Fin.last {k}' in b
assert all(x in c for x in ['codingStar 33 4','codingExpo 33 4','Finset.range 33','5 ^ 34','rw [d11_rankCode]','d10_b_value, d10_e_value, d10_g_value, d10_ell_value,','d10_N, d10_q, d10_theta_value, d10_lambda_value'])
part=c.split('change NinePolynomial.rankCode',1)[1].split('= _',1)[0];assert [int(x) for x in re.findall(r'Fin.last (\d)',part)]==[0,4,7,5,3,2,8,6]
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':3,'scope':'symbolic d11 rank from local prefixes, no full recipe semantics'},sort_keys=True,indent=2))
