#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group02-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'e012481cd15af7126c7b562bccaa95cb93201dca10b215fc52c981176f3f0948','source-manifest.json':'0b7d0c707e412a6c0c922d6af911d483d43faac3ec3208268c00c7c61e6bca3e','src/DiophantineConsistency/Sign32Substitution02.lean':'528f3c02b24dc15bbe41c9de4ce66515643cad080abb9badf255162b053c846c'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Sign32Substitution01']
s=(P/'src/DiophantineConsistency/Sign32Substitution02.lean').read_text();assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s
old=(D/'research/nine-sharing-sign33-seed-syntax-draft/SharingSeed33Syntax.lean').read_text();new=(D/'research/nine-sharing-sign32-sextic-lean-draft/SharingSeed32Sextic.lean').read_text()
def rows(s):return [x.strip().removesuffix(',') for x in s.split('def remainingResiduals',1)[1].split('[\n',1)[1].split('\n  ]',1)[0].splitlines()]
for prefix,src,offset in [('old',old,4),('new',new,3)]:
 data=rows(src)
 for i,n in enumerate(('kY','ell','Delta')):
  expr=s.split('def '+prefix+n,1)[1].split(':=',1)[1].split('\n\n',1)[0];assert ''.join(expr.split())==''.join(data[i+offset].split())
  if prefix=='old':assert not re.search(r'Expr\.var 15\b',expr)
  assert f'((SharingSeed{"33" if prefix=="old" else "32Sextic"}.remainingResiduals p).drop {i+offset}).head? = some ({prefix}{n} p)' in s
for n in ('kY','ell','Delta'):
 t=s.split(f'theorem {n}_eval',1)[1].split('\n\n',1)[0];assert '(beta : V) (v : Fin 33 → V)' in t and 'Sign32Substitution00.lift beta v j' in t and f'({prefix if False else "old"}{n} p).evalRing' in t and f'(new{n} p).evalRing' in t and 'hp0' not in t
assert re.findall(r'^theorem (\w+)',s,re.M)==[x for n in ('kY','ell','Delta') for x in (f'old_{n}_row',f'new_{n}_row',f'{n}_eval')]
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not r.stderr;pre=json.loads(r.stdout);assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':pre,'scope':'old/new list rows kY,ell,Delta and same-valuation lift eval; no port-cast assumption needed and no full bridge'},indent=2,sort_keys=True))
