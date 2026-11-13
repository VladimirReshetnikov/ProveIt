#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group07-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'d544bd45b77ab7daef9eb66b14457e35212bfff8d2a978aa1b94a4c80a9ce7c4','source-manifest.json':'ed82f9b11d8eaf24da610995e694e554f50c62ae8dda008c81ea7a296e175b8a','src/DiophantineConsistency/Sign32Substitution07.lean':'e83dc77bc439b2ee86414616693ad653002244f3dc1613c50c6cb6a3d86ecff1'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Sign32Substitution06']
s=(P/'src/DiophantineConsistency/Sign32Substitution07.lean').read_text();assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s
old=(D/'research/nine-sharing-sign33-seed-syntax-draft/SharingSeed33Syntax.lean').read_text();new=(D/'research/nine-sharing-sign32-sextic-lean-draft/SharingSeed32Sextic.lean').read_text()
def rows(s):return [x.strip().removesuffix(',') for x in s.split('def remainingResiduals',1)[1].split('[\n',1)[1].split('\n  ]',1)[0].splitlines()]
for prefix,src,offset in [('old',old,19),('new',new,18)]:
 data=rows(src)
 for i,n in enumerate(('normalizedS2','V2minusY2','Na','scaledNs')):
  expr=s.split('def '+prefix+n,1)[1].split(':=',1)[1].split('\n\n',1)[0];assert ''.join(expr.split())==''.join(data[i+offset].split())
  if prefix=='old':assert not re.search(r'Expr\.var 15\b',expr)
  assert f'((SharingSeed{"33" if prefix=="old" else "32Sextic"}.remainingResiduals p).drop {i+offset}).head? = some ({prefix}{n} p)' in s
for n in ('normalizedS2','V2minusY2','Na','scaledNs'):
 t=s.split(f'theorem {n}_eval',1)[1].split('\n\n',1)[0];assert '(beta : V) (v : Fin 33 → V)' in t and 'Sign32Substitution00.lift beta v j' in t and f'({prefix if False else "old"}{n} p).evalRing' in t and f'(new{n} p).evalRing' in t and 'hp0' not in t
assert re.findall(r'^theorem (\w+)',s,re.M)==[x for n in ('normalizedS2','V2minusY2','Na','scaledNs') for x in (f'old_{n}_row',f'new_{n}_row',f'{n}_eval')]
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not r.stderr;pre=json.loads(r.stdout);assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':pre,'scope':'old/new list rows normalizedS2,V2minusY2,Na,scaledNs and same-valuation lift eval; no port-cast assumption needed and no full bridge'},indent=2,sort_keys=True))
