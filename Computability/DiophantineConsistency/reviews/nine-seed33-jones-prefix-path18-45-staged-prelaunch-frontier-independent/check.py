#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-path18-45-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'873ae4af6a0db433fba0c3f7ba403b9942881e47f615c72e7c29a171b6b394ba','source-manifest.json':'c2a16f596a09e969f15d2073e1357b9072537521a41b0a686f2b86bfa3b819b8','embedding-survey.py':'6b2d3ded1068eb943bdee95dac3c8aff38fe5699ec9e341209c3db767a881191'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==5
ends=(20,27,34,41,45);prev=18
for k,(end,e) in enumerate(zip(ends,m)):
 name=f'Sign33MacroPath18to{end}';assert e['module']=='DiophantineConsistency.'+name
 assert e['imports']==(['DiophantineConsistency.Sign33MacroDependentOutput','DiophantineConsistency.Sign33MacroPrefixEmbedding'] if k==0 else ['DiophantineConsistency.Sign33MacroPath18to'+str(prev)])
 src=P/'src/DiophantineConsistency'/f'{name}.lean';assert H(src)==e['source_sha256'];old=D/f'research/nine-seed38-jones-prefix-path18-{end}-check/src/DiophantineConsistency/Norm38MacroPath18to{end}.lean';s=src.read_text();assert s==old.read_text().replace('Norm38','Sign33')
 statement=s.split(f'theorem path18_{end} ',1)[1].split(':= by',1)[0];assert statement.count('.castSucc')==end-18
 proof=s.split(f'theorem path18_{end} ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert proof.count('PrefixPath.step')==end-prev
 lookup=s.split(f'theorem lookup18_{end} ',1)[1].split(':= by',1)[0];assert '(i : Fin 18)' in lookup and lookup.count('.castSucc')==end-18
 if end==45:assert 'rw [recipe_eq_named]' in s and 'exact lookup18_45 a i' in s
 prev=end
up=D/'reviews/nine-seed33-jones-dependent08-staged-terminal-frontier-independent/check.py';assert H(up)=='f8908d411729a7b1f1bcf121aeb653e43f7902749bf83a8dca7e40e03291f0ce';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'Fin18 lookup transported to five checkpoints and recipe only; no output semantic identity or Lean replay'},sort_keys=True,indent=2))
