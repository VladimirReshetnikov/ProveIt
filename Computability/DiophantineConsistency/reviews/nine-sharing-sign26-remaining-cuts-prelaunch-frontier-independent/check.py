#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-remaining-cuts-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'dbb4618c5a30639872d7b33fa0690e4ec1de59981540c790d8f41e2cfe79820d','source-manifest.json':'a818849f6fa9a488340e23e96f6b0b7f07b0efd3f7e1983b1a6636f194b723ec'}.items():assert H(P/n)==h
rows=[]
for n in (27,26):
 t=(D/f'research/nine-sharing-sign{n}-sextic-lean-draft/SharingSeed{n}Sextic.lean').read_text().split('def remainingResiduals ',1)[1].split('\n  [\n',1)[1].split('\n  ]',1)[0];rows.append([x.strip().removesuffix(',') for x in t.splitlines()]);assert len(rows[-1])==n-10
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2;allindices=[]
for stage,e in enumerate(m):
 name=f'Sign26RemainingCuts0{stage}';p=P/'src/DiophantineConsistency'/f'{name}.lean';s=p.read_text();assert H(p)==e['source_sha256']==H(D/f'research/nine-sharing-sign26-remaining-cuts-draft/{name}.lean');assert e['module']=='DiophantineConsistency.'+name and e['imports']==['DiophantineConsistency.'+('Sign26CongruenceCuts' if stage==0 else 'Sign26RemainingCuts00')]
 indices=[int(x) for x in re.findall(r'^def oldR(\d+) ',s,re.M)];assert len(indices)==7;allindices+=indices
 for i in indices:
  label=f'R{i:02d}';oi=i-1;ni=i-1 if i<8 else i-2
  old=s.split(f'def old{label} ',1)[1].split(':=\n',1)[1].split('\n',1)[0].strip();new=s.split(f'def new{label} ',1)[1].split(':=\n',1)[1].split('\n',1)[0].strip();assert old==rows[0][oi] and new==rows[1][ni] and not re.search(r'Expr.var 22\b',old)
  assert re.sub(r'Expr.var (\d+)',lambda m:'Expr.var '+str(int(m[1])-(int(m[1])>=23)),old)==new
  for tag,idx,n in [('old',oi,27),('new',ni,26)]:assert f'((SharingSeed{n}Sextic.remainingResiduals p).drop {idx}).head? = some ({tag}{label} p)' in s
  th=s.split(f'theorem {label}_eval ',1)[1].split(':= by',1)[0];assert '(gap : V)' in th and '(hgap' not in th and '(hq3' not in th
assert allindices==[1,2,3,4,5,6,7,10,11,13,14,15,16,17]
up=D/'reviews/nine-sharing-sign26-congruence-cuts-terminal-frontier-independent/check.py';assert H(up)=='e72267a51d1d650ea77c4346360e6f0a537b78729b52b58101bf14570cf0652f';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'14 gap-independent residual identities, exact old/new positions and shifts; no assembled bridge or Lean replay'},sort_keys=True,indent=2))
