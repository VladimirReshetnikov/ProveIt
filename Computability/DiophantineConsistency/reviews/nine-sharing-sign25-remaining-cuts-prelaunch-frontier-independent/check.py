#!/usr/bin/env python3
import hashlib,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-remaining-cuts-check';Q=D/'research/nine-sharing-sign25-remaining-cuts-draft';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'e35c28431cf4d52bdfcd7e4f90e74bfab2fbb12a120fb726c2417c3b2e59101b','source-manifest.json':'b09e97f802ad3001cd4748276b039a638afc24c7e52f2e6bb76027c0ec23ae46'}.items():assert H(P/n)==h
assert H(Q/'generate.py')=='5717781a7cfa837e2e0b207a219c7225abb6141a8b9e5eeb278f0b5cf46ca3a9';rows=[]
for n,label in [(26,'Sextic'),(25,'Octic')]:
 t=(D/f'research/nine-sharing-sign{n}-{label.lower()}-lean-draft'/f'SharingSeed{n}{label}.lean').read_text();first=t.split(f'def firstResidual (p : Fin 4 → ℤ) : Expr (Fin {n+1}) :=\n  ',1)[1].split('\n',1)[0];block=t.split('def remainingResiduals ',1)[1].split('\n  [\n',1)[1].split('\n  ]',1)[0];rows.append((first,[x.strip().removesuffix(',') for x in block.splitlines()]))
assert len(rows[0][1])==16 and len(rows[1][1])==15 and rows[0][0]==rows[1][0]
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2;allindices=[]
for stage,e in enumerate(m):
 name=f'Sign25RemainingCuts0{stage}';p=P/'src/DiophantineConsistency'/f'{name}.lean';s=p.read_text();assert H(p)==e['source_sha256']==H(Q/f'{name}.lean') and e['module']=='DiophantineConsistency.'+name and e['imports']==['DiophantineConsistency.'+('Sign25FirstCut' if stage==0 else 'Sign25RemainingCuts00')];indices=[int(x) for x in re.findall(r'^def oldR(\d+) ',s,re.M)];assert len(indices)==7;allindices+=indices
 for i in indices:
  label=f'R{i:02d}';oi=i-1;ni=i-1 if i<4 else i-2;old=s.split(f'def old{label} ',1)[1].split(':=\n',1)[1].split('\n',1)[0].strip();new=s.split(f'def new{label} ',1)[1].split(':=\n',1)[1].split('\n',1)[0].strip();assert old==rows[0][1][oi] and new==rows[1][1][ni] and not re.search(r'Expr.var 19\b',old);assert re.sub(r'Expr.var (\d+)',lambda x:'Expr.var '+str(int(x[1])-(int(x[1])>=20)),old)==new
  for tag,idx,n,k in [('old',oi,26,'Sextic'),('new',ni,25,'Octic')]:assert f'((SharingSeed{n}{k}.remainingResiduals p).drop {idx}).head? = some ({tag}{label} p)' in s
  th=s.split(f'theorem {label}_eval ',1)[1].split(':= by',1)[0];assert '(v : Fin 26 → V)' in th and 'Sign25FirstCut.lift v' in th
 if stage==0:assert 'theorem first_eval' in s and 'SharingSeed26Sextic.firstResidual' in s and 'SharingSeed25Octic.firstResidual' in s
assert allindices==[1,2,3,5,6,7,8,10,11,12,13,14,15,16]
with tempfile.TemporaryDirectory(prefix='sign25-cuts-review-',dir=D/'research') as t:
 t=Path(t);shutil.copyfile(Q/'generate.py',t/'generate.py');r=subprocess.run([sys.executable,'-I','-S','-B',str(t/'generate.py')],capture_output=True,text=True,check=True,timeout=120)
 for stage in range(2):assert (t/f'Sign25RemainingCuts0{stage}.lean').read_bytes()==(Q/f'Sign25RemainingCuts0{stage}.lean').read_bytes()
up=D/'reviews/nine-sharing-sign25-first-cut-terminal-frontier-independent/check.py';assert H(up)=='bdd993aaa2ab6425fb1497842b5de8765d7338b81d2b9e01d7780e296dbf9b7c';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'q3 first residual and 14 ell-independent row evaluations; ell and N0 in separately checked first cut; no full bridge'},sort_keys=True,indent=2))
