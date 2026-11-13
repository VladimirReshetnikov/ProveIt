#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-cd-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'9436d56e73eb11bd1792f929d76e9ce5ecbbc528eb347dcd05338d4f64213fa8','provider_preflight.py':'9691d64f8fe04161b6762abc398fc28e973c51e9901bded96074b9c36f6ebfe7','source-manifest.json':'d67c010b3f107737387e22db24351e90498909be73efd0b84deeb0238dacf3ae','src/DiophantineConsistency/Norm38MacroVarsCd.lean':'fa636d77fbc32142d8aa67c3d556cb970cd536e79a964e57c88a64a538253c79'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Norm38MacroVarsBd']
s=(P/'src/DiophantineConsistency/Norm38MacroVarsCd.lean').read_text();assert re.findall(r'^theorem (\w+)',s,re.M)==['d41_Cd_eq_dvnd']==re.findall(r'^#print axioms (\w+)',s,re.M)
for x in ['d41.values a ⟨40, by decide⟩ = (vars a).dvnd','(⟨40, by decide⟩ : Fin 41) = Fin.last 40','rw [hi, d41_Cd_value]','RingVars.dvnd','RingVars.Q','RingVars.H','RingVars.J','RingVars.F','Int.cast_one']:assert x in s
core=(D/'Lean/DiophantineConsistency/JonesSyntaxCore.lean').read_text();assert 'def dvnd : R := (v.Q * v.F + v.J * (v.H - v.C)) ^ 2' in core
prev=(D/'reviews/nine-seed38-jones-checkpoint40-41-bdcd-prelaunch-frontier-independent/result.json').read_text();assert 'PASS_STATIC' in prev
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'Cd cut = vars.dvnd only; d11 rank opaque; no Lean or named-formula equality'},indent=2,sort_keys=True))
