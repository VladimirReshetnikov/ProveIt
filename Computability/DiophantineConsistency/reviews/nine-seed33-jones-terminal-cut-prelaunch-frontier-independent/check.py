#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-terminal-cut-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'4916d9b71d8e6cba98c52b78efb0853be99d93600b37be089e80074c3bc1b06f','source-manifest.json':'e828426fb577378f786060e069ad5c4fa6fb0e4cc1b468937c60c2bc7f8bc844','values-survey.py':'a6e1e045742bae129bf1bf11ce3c7919350d1483511afe4fa2dd5735d14df101'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2;ss=[]
for suffix,e in zip(['TerminalT','TerminalOutput'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-terminal-cut-retry01/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-terminal-cut-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['bd * t + cd - kc * (cd + v0 * v1)','d41_t_value','d44_T_cut','lookup41_43','lookup41_44','rw [h39, h17, h40, h37, h38, hit, d41_t_value, hik]']);assert all(x in b for x in ['d45_output_cut','recipe_output_cut','rw [recipe_eq_named]','d44_T_cut','rw [hik, hit, hk, h35, h36, h37, d44_T_cut]'])
for x in (39,17,40,37,38):assert f'd43.values a ⟨{x}, by decide⟩' in a
for x in (35,36,37):assert f'd44.values a ⟨{x}, by decide⟩' in b
up=D/'reviews/nine-seed33-jones-checkpoint43-kc-terminal-frontier-independent/check.py';assert H(up)=='42d3b7bde1a5133c601dc2e40df0d18b1eb7c846e60a23c87a387f1f8bb57095';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'T/output cut in terms of earlier d41/d43 values and recipe transfer; no named-evaluator equality or JSON binding'},sort_keys=True,indent=2))
