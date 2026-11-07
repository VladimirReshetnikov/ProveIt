#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint26-27-c-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'a73c0f9425a631f4842e81b3067f469ab6eee65797eb00c4bc2f24a121739e91','source-manifest.json':'7009be47cba3b3c12dfa2c34dc1a3f7f695a25795307afdd208bc75efda5071f','values-survey.py':'b4eedeaa4a9d2ebbab0247410eff21dd45aba1973f255313e0b430013d87ccd7'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['CInputs','CBW','CValue'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint26-27-c-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint26-27-c-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b,c=ss
for x in ['d18_b_value','d18_phi_value','d18_b_carry','d18_phi_carry','prefix_phi']:assert x in a
for x in ['d26_Bprime_value','d26_W_value','prefix_Bprime','prefix_W','d24_R_carry','d18_R_carry','d25_b_carry','d25_w_carry','d18_b_value','d18_w_value']:assert x in b
for x in ['d27_C_value','prefix_C','⟨24, by decide⟩ : Fin 26','⟨25, by decide⟩ : Fin 26','⟨14, by decide⟩ : Fin 26','d26_Bprime_value, d26_W_value, d26_phi_carry, d18_phi_value']:assert x in c
up=D/'reviews/nine-seed33-jones-checkpoint28-41-j-terminal-frontier-independent/check.py';assert H(up)=='4016222664cc8081a8e8d45986c0237479bc70ff33781a3bedc07d48657eed9e';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'d27 C from Bprime/W/phi, rank opaque; no output semantics or Lean replay'},sort_keys=True,indent=2))
