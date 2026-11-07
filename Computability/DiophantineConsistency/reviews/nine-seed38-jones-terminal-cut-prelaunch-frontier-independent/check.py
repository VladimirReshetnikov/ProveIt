#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-terminal-cut-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'44d7d111b519fe9888f1708413b400f0febf371f96a2c4c39db066bffffc8b80','provider_preflight.py':'1425a37eb18fb670e4d9fa710478ca094e4b5af05ac3baf48a5e53426a57f6e1','source-manifest.json':'f478f47801300e36ee60960d4cfe8785e30bdcb9d7eb4d261e727bd4e1356d75'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroTerminalT','bda39c06525a17959e951b2c689ed5f31571324a3b0aacfbdf2f3b489d4bddd3',['Norm38MacroKcValue','Norm38MacroPath18to41','Norm38MacroPrefixInputsB','Norm38MacroDependentOutput'],['lookup41_43','lookup41_44','d41_t_value','d44_T_cut']),('Norm38MacroTerminalOutput','b7a3a71a4b27f29d3b018407dff71036e8188ced11d3996d214d73344ff81a36',['Norm38MacroTerminalT'],['d45_output_cut','recipe_output_cut'])];assert len(rows)==2
for r,(n,h,im,ts) in zip(rows,expected):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n and re.findall(r'^import ([\w.]+)$',s,re.M)==r['imports']==['DiophantineConsistency.'+x for x in im]
 assert re.findall(r'^theorem (\w+)',s,re.M)==ts==re.findall(r'^#print axioms (\w+)',s,re.M)
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
t=(P/'src/DiophantineConsistency/Norm38MacroTerminalT.lean').read_text();o=(P/'src/DiophantineConsistency/Norm38MacroTerminalOutput.lean').read_text();norm=lambda x:''.join(x.split())
assert norm(t.split('def terminalT',1)[1].split(':=',1)[1].split('\ndef terminalOutput',1)[0])=='bd*t+cd-kc*(cd+v0*v1)'
assert norm(t.split('def terminalOutput',1)[1].split(':=',1)[1].split('\ntheorem',1)[0])=='(t^(2:Nat)+kc^(2:Nat)*a0-kc^(2:Nat)*v0^(2:Nat)*a1)^(2:Nat)-((4:Int):R)*t^(2:Nat)*kc^(2:Nat)*a0'
assert 'PrefixPath d41 d43' in t and 'PrefixPath d41 d44' in t and 'lookup18_41 a (Fin.last 17)' in t and 'Norm38MacroPrefixGroup04.prefix_t a' in t and 'a ⟨8, by decide⟩' in t
for x in (39,17,40,37,38):assert f'h{x} : d43.values a ⟨{x}, by decide⟩' in t
for x in (35,36,37):assert f'h{x} : d44.values a ⟨{x}, by decide⟩' in o
assert 'Norm38MacroCuts.snoc_previous a d43 _ (Fin.last 42)' in o and 'rw [recipe_eq_named]' in o
nodes=(D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d44 : Dag 44 := .snoc d43 (.sub (.add (.mul (.ref ⟨39, by decide⟩) (.ref ⟨17, by decide⟩)) (.ref ⟨40, by decide⟩)) (.mul (.ref ⟨42, by decide⟩) (.add (.ref ⟨40, by decide⟩) (.mul (.ref ⟨37, by decide⟩) (.ref ⟨38, by decide⟩)))))' in nodes
assert 'def d45 : Dag 45 := .snoc d44 (.sub (.pow (.sub (.add (.pow (.ref ⟨43, by decide⟩) (.lit 2)) (.mul (.pow (.ref ⟨42, by decide⟩) (.lit 2)) (.ref ⟨35, by decide⟩))) (.mul (.mul (.pow (.ref ⟨42, by decide⟩) (.lit 2)) (.pow (.ref ⟨37, by decide⟩) (.lit 2))) (.ref ⟨36, by decide⟩))) (.lit 2)) (.mul (.mul (.mul (.constant (4 : Int)) (.pow (.ref ⟨43, by decide⟩) (.lit 2))) (.pow (.ref ⟨42, by decide⟩) (.lit 2))) (.ref ⟨35, by decide⟩)))' in nodes
def rhs(s,n):return norm(s.split('theorem '+n,1)[1].split(':= by',1)[0].split('=',1)[1])
Tc='terminalT(d41.valuesa⟨39,bydecide⟩)(d41.valuesa⟨40,bydecide⟩)(d43.valuesa(Fin.last42))(d41.valuesa⟨37,bydecide⟩)(d41.valuesa⟨38,bydecide⟩)(a⟨8,bydecide⟩)'
assert rhs(t,'d44_T_cut')==Tc
final='terminalOutput('+Tc+')(d43.valuesa(Fin.last42))(d41.valuesa⟨35,bydecide⟩)(d41.valuesa⟨36,bydecide⟩)(d41.valuesa⟨37,bydecide⟩)'
assert rhs(o,'d45_output_cut')==rhs(o,'recipe_output_cut')==final
print(json.dumps({'status':'PASS_STATIC','scope':'T and final recipe output in seven unevaluated cuts and input t; no named-formula semantics or JSON binding'},indent=2,sort_keys=True))
