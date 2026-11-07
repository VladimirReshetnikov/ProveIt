#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-remaining-cuts-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'870368fda93183ba99bbdd71db0e4957b412285c2b60694c2c608193791c290e','source-manifest.json':'a3fcedba8a2d9ac47a68e8be0db0efa2087905913ae2257f6ec7b7841a4a8a03','mapping-check.py':'3cff90be6069e3caa2d86b0ad65c6dadbdba76537743e7cb8f90ca26b6ea9657'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign31RemainingCuts00','Sign31RemainingCuts01']
source=[]
for row in m:
 n=row['module'].split('.')[-1];p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();source.append(s);assert sha(p)==row['source_sha256'];assert [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports']
assert [r['source_sha256'] for r in m]==['bff7451e2d89ed0b5f7bbb629b6e9b133f4c1d5334558bf8ec11e8fe7d994b9d','a995e1cd758387edbee9e95507b47ff85c0cc8e1f847b036fec6a15e0d2971bd']
expected=[('X',0,0),('Y',1,1),('E',2,2),('kY',3,3),('ell',4,4),('Delta',5,5),('mainRoot',6,6),('c2',7,7),('Dc2',8,8),('N1',9,9),('gap',10,10),('tau',11,11),('N0',12,12),('Nt',13,13),('cTminusR',15,14),('normalizedS',17,16),('normalizedS2',18,17),('V2minusY2',19,18),('Na',20,19)]
old=json.loads((D/'research/nine-sharing-sign32-sextic-candidate-v2/seed.json').read_text())['residuals'][1:];new=json.loads((D/'research/nine-sharing-sign31-sextic-candidate/seed.json').read_text())['residuals'][1:]
for i,(n,oi,ni) in enumerate(expected):
 s=source[0 if i<9 else 1];assert old[oi]['gate']==new[ni]['gate']
 for which,j in [('old',oi),('new',ni)]:
  target='SharingSeed32Sextic' if which=='old' else 'SharingSeed31Sextic';assert re.search(r'theorem '+which+'_'+n+r'_row\b.*?\('+target+r'\.remainingResiduals p\)\.drop '+str(j)+r'\)\.head\? = some \('+which+n+r' p\)',s,re.S)
 assert re.search(r'theorem '+n+r'_eval\b.*?\(old'+n+r' p\)\.evalRing \(fun j => ι \(Sign31FirstCut.lift v j\)\) = \(new'+n+r' p\)\.evalRing \(fun j => ι \(v j\)\)',s,re.S)
assert 'theorem q3_eval' in source[0] and sum(len(re.findall(r'^theorem \w+_eval\b',s,re.M)) for s in source)==20
x=subprocess.run([sys.executable,'-I','-S','-B',str(P/'mapping-check.py')],capture_output=True,check=True,timeout=30);assert not x.stderr and json.loads(x.stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_STATIC','scope':'q3 and 19 unaffected row-position/evaluation proposals only; no full bridge'}))
