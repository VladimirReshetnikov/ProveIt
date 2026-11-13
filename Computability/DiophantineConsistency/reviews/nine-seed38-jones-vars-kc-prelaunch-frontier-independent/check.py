#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-kc-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'593caa4dadefdad8569e024d5e8cc63b0a56c60e67626efd6e4a32fa684ad13f','provider_preflight.py':'b653a1f72d6392e0e7d54f584116aa9e8dc0c7f60d516f1bea82d7ea9d3dfdd2','source-manifest.json':'bd81281046e1934eb07e4cd163077d8099078426776664449e94d2ddccc1cc28'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];want=[('Norm38MacroVarsDm','eee78f45150d3b4f47ff6723fe76daf2226db330e62512941cb300a0d7fc339c','Norm38MacroVarsWt1','d42_Dm_eq_marg'),('Norm38MacroVarsKc','9b4bddfa3add30f4502b242af00f4c56f23ad6e9639e80a08009f891b513a491','Norm38MacroVarsDm','d43_Kc_eq')];assert len(rows)==2
for r,(n,h,im,t) in zip(rows,want):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n and r['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+im] and re.findall(r'^theorem (\w+)',s,re.M)==[t]==re.findall(r'^#print axioms (\w+)',s,re.M)
a=(P/'src/DiophantineConsistency/Norm38MacroVarsDm.lean').read_text();b=(P/'src/DiophantineConsistency/Norm38MacroVarsKc.lean').read_text()
assert 'd42.values a (Fin.last 41) = (vars a).marg' in a and 'rw [d42_Dm_value]' in a and 'RingVars.marg' in a and 'Int.cast_one' in a
for x in ['d43.values a (Fin.last 42) = (vars a).dvsr * (((2 : Int) : R) * (vars a).marg - ((1 : Int) : R))','d42.values a ⟨39, by decide⟩ = (vars a).dvsr','Norm38MacroCuts.snoc_previous','d41_Bd_eq_dvsr','d42_Dm_eq_marg','prefix_Kc']:assert x in b
core=(D/'Lean/DiophantineConsistency/JonesSyntaxCore.lean').read_text();assert 'def marg : R := v.K ^ 2 * v.G - 4 * (v.C - v.K * v.Y) ^ 2 * v.G - 8 * v.g * v.K ^ 2' in core
nodes=(D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d43 : Dag 43 := .snoc d42 (.mul (.ref ⟨39, by decide⟩) (.sub (.mul (.constant (2 : Int)) (.ref ⟨41, by decide⟩)) (.constant (1 : Int))))' in nodes
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==2
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'Dm=marg and Kc=dvsr*(2*marg-1) short-prefix cuts only; no Lean or full named-formula equality'},indent=2,sort_keys=True))
