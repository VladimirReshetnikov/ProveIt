#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group06-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'8fbb118c53e530979616c9454def6bef8b5f02fae743ea320c9b223d5cb7c074','source-manifest.json':'b7f60a52c547f3a639e3f1160ca30f09e540693309abd2ba2e719e28199ec57a','src/DiophantineConsistency/Sign32Substitution06.lean':'a5fc42f991fbb0b5bc8891a798d7ab04fd692a8708b8e84e76ffe2b0c62a096b'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Sign32Substitution05']
s=(P/'src/DiophantineConsistency/Sign32Substitution06.lean').read_text();assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s
old=(D/'research/nine-sharing-sign33-seed-syntax-draft/SharingSeed33Syntax.lean').read_text();new=(D/'research/nine-sharing-sign32-sextic-lean-draft/SharingSeed32Sextic.lean').read_text()
def rows(s):return [x.strip().removesuffix(',') for x in s.split('def remainingResiduals',1)[1].split('[\n',1)[1].split('\n  ]',1)[0].splitlines()]
for prefix,src,offset in [('old',old,16),('new',new,15)]:
 data=rows(src)
 for i,n in enumerate(('cTminusR','V','normalizedS')):
  expr=s.split('def '+prefix+n,1)[1].split(':=',1)[1].split('\n\n',1)[0];assert ''.join(expr.split())==''.join(data[i+offset].split())
  if prefix=='old':assert bool(re.search(r'Expr\.var 15\b',expr))==(n=='cTminusR')
  assert f'((SharingSeed{"33" if prefix=="old" else "32Sextic"}.remainingResiduals p).drop {i+offset}).head? = some ({prefix}{n} p)' in s
for n in ('cTminusR','V','normalizedS'):
 t=s.split(f'theorem {n}_eval',1)[1].split('\n\n',1)[0];assert '(beta : V) (v : Fin 33 → V)' in t and 'Sign32Substitution00.lift beta v j' in t and f'({prefix if False else "old"}{n} p).evalRing' in t and f'(new{n} p).evalRing' in t and (('hp0' in t)==(n=='cTminusR'))
assert '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s
assert re.findall(r'^theorem (\w+)',s,re.M)==[x for n in ('cTminusR','V','normalizedS') for x in (f'old_{n}_row',f'new_{n}_row',f'{n}_eval')]
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not r.stderr;pre=json.loads(r.stdout);assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':pre,'scope':'old/new list rows cTminusR,V,normalizedS and same-valuation lift eval; cTminusR has explicit port-cast assumption; others do not; no full bridge'},indent=2,sort_keys=True))
