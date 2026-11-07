#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-remaining-cuts-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'df61006a404d208289f394e29cde914e3e61e6f7ddf70074bcf1a53d74a39a33','source-manifest.json':'ba9cea99106cee225f87d7f848b48548573df0f4609037d2ef42e8ea40182a9b'}.items():assert H(P/n)==h
rows=[]
for n in (28,27):
 t=(D/f'research/nine-sharing-sign{n}-sextic-lean-draft/SharingSeed{n}Sextic.lean').read_text().split('def remainingResiduals ',1)[1].split('\n  [\n',1)[1].split('\n  ]',1)[0];rows.append([x.strip().removesuffix(',') for x in t.splitlines()]);assert len(rows[-1])==n-10
manifest=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(manifest)==2
allindices=[]
for stage,e in enumerate(manifest):
 name=f'Sign27RemainingCuts0{stage}';s=(P/'src/DiophantineConsistency'/f'{name}.lean').read_text();assert H(P/'src/DiophantineConsistency'/f'{name}.lean')==e['source_sha256']==H(D/f'research/nine-sharing-sign27-remaining-cuts-draft/{name}.lean');assert e['module']=='DiophantineConsistency.'+name;assert e['imports']==['DiophantineConsistency.'+('Sign27FirstCut' if stage==0 else 'Sign27RemainingCuts00')]
 indices=[int(x) for x in re.findall(r'^def oldR(\d+) ',s,re.M)];assert len(indices)==7;allindices+=indices
 for i in indices:
  label=f'R{i:02d}';oi=i-1;ni=i-1 if i<8 else i-2
  old=s.split(f'def old{label} ',1)[1].split(':=\n',1)[1].split('\n',1)[0].strip();new=s.split(f'def new{label} ',1)[1].split(':=\n',1)[1].split('\n',1)[0].strip();assert old==rows[0][oi] and new==rows[1][ni]
  assert not re.search(r'Expr.var (21|22)\b',old)
  shifted=re.sub(r'Expr.var (\d+)',lambda m:'Expr.var '+str(int(m[1])-(int(m[1])>=23)),old);assert shifted==new
  for tag,idx,n in [('old',oi,28),('new',ni,27)]:assert f'((SharingSeed{n}Sextic.remainingResiduals p).drop {idx}).head? = some ({tag}{label} p)' in s
  assert f'theorem {label}_eval' in s and s.count(f'#print axioms DiophantineConsistency.Sign27RemainingCuts.{label}_eval')==1
assert allindices==[1,2,3,4,5,9,10,11,12,13,14,16,17,18]
up=D/'reviews/nine-sharing-sign27-first-cut-retry01-terminal-frontier-independent/check.py';assert H(up)=='d049db4de12602c490af2b6649f1d6c850a5d2982014b2eddd6acc138fdb1549';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'14 unaffected residual identities, two stages, exact old/new positions and index shift; no assembled bridge or Lean replay'},sort_keys=True,indent=2))
