#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-wt-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'ad02f4a2115a512174c6a4d741d0a80f37789218c9202b69612d484f372869d3','provider_preflight.py':'bd7bf93357ab67b53eb3025245c69bee0934975de1257b28e5bd9c38b7f6800a','source-manifest.json':'cbab7ae7652d57afe0efe3f1204763c5ea04af6f2d44448c5b6057123fe92bfe'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];want=[('Norm38MacroVarsWt0','8798255354b32257ba2f0daaeee61e71d7fc32ea79238a0b5d7347fadab50f45','Norm38MacroVarsRad1','d41_V0_eq_wt0',37),('Norm38MacroVarsWt1','4c438960a38a6e12ce16cc3d0d20e4d4e16f16da68fa8ae45b7c591be780a056','Norm38MacroVarsWt0','d41_V1_eq_wt1',38)];assert len(rows)==2
for i,(r,(n,h,im,t,index)) in enumerate(zip(rows,want)):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n and r['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+im] and re.findall(r'^theorem (\w+)',s,re.M)==[t]==re.findall(r'^#print axioms (\w+)',s,re.M)
 for x in [f'd41.values a ⟨{index}, by decide⟩ = (vars a).wt {i}',f'prefix_V{i}',f'd{37+i}_A{i}_carry',f'd41_A{i}_eq_rad{i}','RingVars.wt','Int.cast_ofNat','lookup39_41']:assert x in s
core=(D/'Lean/DiophantineConsistency/JonesSyntaxCore.lean').read_text();assert 'def wt : Fin 2 → R := fun k => v.rad k ^ 2 + 2' in core
nodes=(D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for i in [0,1]:assert f'def d{38+i} : Dag {38+i} := .snoc d{37+i} (.add (.pow (.ref ⟨{35+i}, by decide⟩) (.lit 2)) (.constant (2 : Int)))' in nodes
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==2
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'symbolic V0/V1 = vars.wt0/wt1 only; no Lean or named-formula equality'},indent=2,sort_keys=True))
