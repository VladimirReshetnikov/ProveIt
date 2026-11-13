#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoints27-45-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'f5d6fd726a26cd541798f11afb50cf2ab11c34467832cd2c4657fe716a6f245c','source-manifest.json':'517ba03e659010b60588baed547ec930c686053acefb51f6d4a14b04f6eb2ff2','values-survey.py':'27b32b222c451ded6215933d9f7f0a80220d00bc3b77520aac8ce8ea0d87fc5c'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==3
for (start,end),e in zip([(27,34),(34,41),(41,45)],m):
 name=f'Sign33MacroCheckpoint{start}to{end}';assert e['module']=='DiophantineConsistency.'+name;p=P/'src/DiophantineConsistency'/f'{name}.lean';assert H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoints27-45-staged-draft/{name}.lean');old=D/f'research/nine-seed38-jones-checkpoint{start}-{end}-check/src/DiophantineConsistency/Norm38MacroCheckpoint{start}to{end}.lean';s=p.read_text();assert s==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33')
 statement=s.split(f'theorem path{start}_{end} ',1)[1].split(':= by',1)[0];proof=s.split(f'theorem path{start}_{end} ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==end-start and proof.count('PrefixPath.step')==end-start
 lookup=s.split(f'theorem lookup{start}_{end} ',1)[1].split(':= by',1)[0];assert f'(i : Fin {start})' in lookup and lookup.count('.castSucc')==end-start
 if start==27:assert 'theorem d34_phi_value' in s and 'a ⟨5, by decide⟩' in s and 'd18_phi_carry' in s and 'prefix_phi' in s
 if start==34:assert 'theorem d41_N_value' in s and '5 ^ 34' in s and 'd18_N_carry' in s and 'd10_N' in s
 if start==41:assert all(x in s for x in ['rw [recipe_eq_named]','theorem d41_g_value','theorem d41_G_value','5 ^ 33','d18_g_carry','d18_G_carry','prefix_g','prefix_G'])
up=D/'reviews/nine-seed33-jones-prefix-path18-45-staged-terminal-frontier-independent/check.py';assert H(up)=='84b526564578d6e72fcb47fea066c1b199f9731ad344b2c251bb904695306513';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'three checkpoint paths and four symbolic phi/N/g/G values only; no output semantics or Lean replay'},sort_keys=True,indent=2))
