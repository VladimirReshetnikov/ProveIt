#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-checkpoint43-kc-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'ee0bcfd5cb5a522cceb6ac5bff27be47b215b87a617b63662f7979998b55cd73','provider_preflight.py':'4c5727df4c50eba6b94268fc28840c229343d31f72c2b0b7f06d09c41d0706e5','source-manifest.json':'152e66d3c3602240d9195efb2ee72746906600fa6258f81ba2c0b2ebda674bde','src/DiophantineConsistency/Norm38MacroKcValue.lean':'c754b51cffbadef259c6c2a6196a704d84909cb8b80850261abf14ae270d005b'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Norm38MacroDmValue']
p=P/'src/DiophantineConsistency/Norm38MacroKcValue.lean';s=p.read_text();assert re.findall(r'^theorem (\w+)',s,re.M)==['d42_Bd_value','d43_Kc_value']==re.findall(r'^#print axioms (\w+)',s,re.M)
def rhs(p,n):return ''.join(p.read_text().split('theorem '+n,1)[1].split(':= by',1)[0].split('=',1)[1].split())
bd=rhs(D/'research/nine-seed38-jones-checkpoint40-41-bdcd-check/src/DiophantineConsistency/Norm38MacroBdValue.lean','d40_Bd_value');dm=rhs(D/'research/nine-seed38-jones-checkpoint42-dm-check/src/DiophantineConsistency/Norm38MacroDmValue.lean','d42_Dm_value');assert rhs(p,'d42_Bd_value')==bd
v=rhs(p,'d43_Kc_value')
for k,x in sorted([('B',bd),('D',dm)],key=lambda z:-len(z[1])):v=v.replace(x,k)
assert v=='(B)*(((2:Int):R)*(D)-((1:Int):R))'
assert s.count('Norm38MacroCuts.snoc_previous')==2 and '(⟨39, by decide⟩ : Fin 42)' in s and '(⟨41, by decide⟩ : Fin 42)' in s
nodes=(D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d43 : Dag 43 := .snoc d42 (.mul (.ref ⟨39, by decide⟩) (.sub (.mul (.constant (2 : Int)) (.ref ⟨41, by decide⟩)) (.constant (1 : Int))))' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=300,check=True);assert not r.stderr;pre=json.loads(r.stdout);assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':pre,'scope':'short-prefix Kc = Bd*(2*Dm-1) only; no Lean or full-output claim'},indent=2,sort_keys=True))
