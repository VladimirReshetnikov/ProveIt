#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-remaining-cuts-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'5976532eabb710666179c4dcb52e1204f4403e964a32513fbd6b97ecb04a81b9','source-manifest.json':'4612f32a0c59eab6d793590ff6b27e0df2a75bc545a22f0e171cce50d8e61971','mapping-check.py':'f827c6e2328d194707bfae0e0e914f25127311e6e3eb826f1371a2946782af0e'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign28RemainingCuts00','Sign28RemainingCuts01'];ss=[]
for row in m:
 n=row['module'].split('.')[-1];p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();ss.append(s);assert sha(p)==row['source_sha256'] and [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports']
expected=[('Y',1,0),('kY',3,2),('ell',4,3),('Delta',5,4),('N1',9,7),('gap',10,8),('tau',11,9),('N0',12,10),('Nt',13,11),('cTminusR',14,12),('V',15,13),('normalizedS',16,14),('V2minusY2',18,15)];old=json.loads((D/'research/nine-sharing-sign31-sextic-candidate/seed.json').read_text())['residuals'][1:];new=json.loads((D/'research/nine-sharing-sign28-sextic-candidate/seed.json').read_text())['residuals'][1:]
for i,(n,oi,ni) in enumerate(expected):
 s=ss[0 if i<6 else 1];assert old[oi]['gate']==new[ni]['gate']
 for which,j in [('old',oi),('new',ni)]:
  target='SharingSeed31Sextic' if which=='old' else 'SharingSeed28Sextic';assert re.search(r'theorem '+which+'_'+n+r'_row\b.*?\('+target+r'\.remainingResiduals p\)\.drop '+str(j)+r'\)\.head\? = some \('+which+n+r' p\)',s,re.S)
 assert re.search(r'theorem '+n+r'_eval\b.*?\(old'+n+r' p\)\.evalRing \(fun j => ι \(Sign28FirstCuts.lift beta v j\)\) = \(new'+n+r' p\).evalRing \(fun j => ι \(v j\)\)',s,re.S)
assert 'theorem q3_eval' in ss[0] and sum(len(re.findall(r'^theorem \w+_eval\b',s,re.M)) for s in ss)==14 and all('hp0 :' not in s for s in ss)
x=subprocess.run([sys.executable,'-I','-S','-B',str(P/'mapping-check.py')],capture_output=True,check=True,timeout=30);assert not x.stderr and json.loads(x.stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_STATIC','scope':'q3 and 13 unaffected row-position/evaluation proposals only; no full bridge'}))
