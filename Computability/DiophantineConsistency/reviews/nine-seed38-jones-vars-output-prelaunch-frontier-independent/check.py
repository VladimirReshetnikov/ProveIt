#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-output-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'b8ee0019e07f2fde1b3e02a4f0ac7724f77bdf1fe19a2abc4a232a837b4b0736','provider_preflight.py':'a4efef05d21e26c6daa41b6f6fd8a8754ec9a306b80308d7a6ca4f73ba7ebf3a','source-manifest.json':'d786546fc6b8ba5b9540f724734fd71521308eeafbb73ce4a400f23669149210','src/DiophantineConsistency/Norm38MacroVarsOutput.lean':'4d1240af3ed3a10a9dcc4244e7aa07836816a8bcca632f315a4789a37e6f8f12'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Norm38MacroVarsKc']
s=(P/'src/DiophantineConsistency/Norm38MacroVarsOutput.lean').read_text();assert re.findall(r'^theorem (\w+)',s,re.M)==['recipe_eq_refined']==re.findall(r'^#print axioms (\w+)',s,re.M)
for x in ['Norm38MacroRecipe.recipe.values a (Fin.last 44)','RefinedPair.value ((vars a).rad 0) ((vars a).rad 1) ((vars a).wt 0) ((vars a).wt 1)','(a ⟨8, by decide⟩) (vars a).dvsr (vars a).dvnd (vars a).marg','recipe_output_cut, d41_Bd_eq_dvsr, d41_Cd_eq_dvnd, d43_Kc_eq,','d41_V0_eq_wt0, d41_V1_eq_wt1, d41_A0_eq_rad0, d41_A1_eq_rad1','terminalOutput, terminalT, RefinedPair.value, Int.cast_ofNat, Int.cast_one']:assert x in s
core=(D/'Lean/DiophantineConsistency/JonesSyntaxCore.lean').read_text();assert 'let K := B * (2 * D - 1)' in core and 'let T := B * n + C - K * (C + V0 * V1)' in core and '(T ^ 2 + K ^ 2 * A0 - K ^ 2 * V0 ^ 2 * A1) ^ 2 - 4 * T ^ 2 * K ^ 2 * A0' in core
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'recipe output to RefinedPair on symbolic vars only; rank/named formula equality and JSON binding separate'},indent=2,sort_keys=True))
