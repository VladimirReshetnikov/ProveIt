#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-first-cuts-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'6252e4b24b8b02c5605a45203be6dbfc0f67c89ad711e703e29186e96498733d','source-manifest.json':'593b1565abcc5e23403fe9eddfbb31da2e63e80fa192f52e88a28de3b7d7e4bf','sign31-survey.py':'3f9ea740e340d1c7dfeeaee2bb870c6eded43a5d6abe4a7d6514a0c18be63239'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=[f'Sign28FirstCuts0{i}' for i in range(3)];assert [r['module'].split('.')[-1] for r in m]==names;ss=[]
for row,n in zip(m,names):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();ss.append(s);assert sha(p)==row['source_sha256'] and [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports'] and s==(D/'research/nine-sharing-sign28-first-cuts-draft'/f'{n}.lean').read_text()
old=json.loads((D/'research/nine-sharing-sign31-sextic-candidate/seed.json').read_text())['residuals'][1:];new=json.loads((D/'research/nine-sharing-sign28-sextic-candidate/seed.json').read_text())['residuals'][1:]
spec=[('X',0,0,[('E','E',2,1),('mainRoot','main_root',6,5)]),('c2',7,1,[('Dc2','Dc2',8,6)]),('normalizedS2',17,2,[('Na','Na',19,16),('scaledNs','scaled_Ns',20,17)])]
for n,oi,i,uses in spec:
 s=ss[i];assert old[oi]['gate']=={'normalizedS2':'normalized_S2'}.get(n,n)
 assert re.search(r'theorem old_'+n+r'_row\b.*?\(SharingSeed31Sextic.remainingResiduals p\)\.drop '+str(oi)+r'\)\.head\? = some \(old'+n+r' p\)',s,re.S) and 'theorem old_'+n+'_zero' in s
 for t,gate,oj,nj in uses:
  assert old[oj]['gate']==new[nj]['gate']==gate
  for which,j,target in [('old',oj,'SharingSeed31Sextic'),('new',nj,'SharingSeed28Sextic')]:assert re.search(r'theorem '+which+'_'+t+r'_row\b.*?\('+target+r'\.remainingResiduals p\)\.drop '+str(j)+r'\)\.head\? = some \('+which+t+r' p\)',s,re.S)
  assert re.search(r'theorem '+t+r'_eval\b.*?\(old'+t+r' p\)\.evalRing \(fun j => ι \(lift beta v j\)\) = \(new'+t+r' p\).evalRing \(fun j => ι \(v j\)\)',s,re.S)
assert ss[0].count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)')==3 and all('hp0 :' not in s for s in ss[1:])
bridge=(D/'research/nine-sharing-sign28-sextic-lean-draft/SharingSeed28BridgeDraft.lean').read_text();assert ss[0].split('def lift ',1)[1].split('\n\n',1)[0]==bridge.split('def lift ',1)[1].split('\n\n',1)[0]
print(json.dumps({'status':'PASS_STATIC','scope':'three removed-row zeros and five affected survivor row/eval proposals only'}))
