#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group04-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'8a43b1b662beee16c80a9daa79533dfb0e1869f5885b22bdb1461b0ece16cf79','source-manifest.json':'ffcdb2d9124eeb0ba8d999323cc09a78e762b9e97815a5d2af942f33679508f6','src/DiophantineConsistency/Sign32Substitution04.lean':'0a4fb6825ff0d966a64e63e4f36c5b83198a5c1b6a39b0b57a31553f77783d9b'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Sign32Substitution03']
s=(P/'src/DiophantineConsistency/Sign32Substitution04.lean').read_text();assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s
old=(D/'research/nine-sharing-sign33-seed-syntax-draft/SharingSeed33Syntax.lean').read_text();new=(D/'research/nine-sharing-sign32-sextic-lean-draft/SharingSeed32Sextic.lean').read_text()
def rows(s):return [x.strip().removesuffix(',') for x in s.split('def remainingResiduals',1)[1].split('[\n',1)[1].split('\n  ]',1)[0].splitlines()]
for prefix,src,offset in [('old',old,10),('new',new,9)]:
 data=rows(src)
 for i,n in enumerate(('N1','gap','tau')):
  expr=s.split('def '+prefix+n,1)[1].split(':=',1)[1].split('\n\n',1)[0];assert ''.join(expr.split())==''.join(data[i+offset].split())
  if prefix=='old':assert bool(re.search(r'Expr\.var 15\b',expr))==(n=='tau')
  assert f'((SharingSeed{"33" if prefix=="old" else "32Sextic"}.remainingResiduals p).drop {i+offset}).head? = some ({prefix}{n} p)' in s
for n in ('N1','gap','tau'):
 t=s.split(f'theorem {n}_eval',1)[1].split('\n\n',1)[0];assert '(beta : V) (v : Fin 33 → V)' in t and 'Sign32Substitution00.lift beta v j' in t and f'({prefix if False else "old"}{n} p).evalRing' in t and f'(new{n} p).evalRing' in t and (('hp0' in t)==(n=='tau'))
assert '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s
assert re.findall(r'^theorem (\w+)',s,re.M)==[x for n in ('N1','gap','tau') for x in (f'old_{n}_row',f'new_{n}_row',f'{n}_eval')]
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not r.stderr;pre=json.loads(r.stdout);assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':pre,'scope':'old/new list rows N1,gap,tau and same-valuation lift eval; tau has explicit port-cast assumption; others do not; no full bridge'},indent=2,sort_keys=True))
