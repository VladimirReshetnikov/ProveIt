#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-vars-cd-rad-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'9d7822ba5cffc55e421fe115f146fa8693931e9f67e7168aa51acf3418784e98','source-manifest.json':'4b92a7929b1744345771bbb02bed58bfd75e51472639015c18f5b923da168595','values-survey.py':'ad5a6325247e64dabd6b15c271db6a4163633145acb6381c45d4fad4c869e8fe'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==3
for suffix,part,e in zip(['VarsCd','VarsRad0','VarsRad1'],['cd','rad','rad'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-vars-{part}-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-vars-{part}-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33')
for name,terms in [('VarsCd',['d41_Cd_eq_dvnd','d41_Cd_value','RingVars.dvnd']),('VarsRad0',['d41_A0_eq_rad0','d41_A0_value','(vars a).rad 0']),('VarsRad1',['d41_A1_eq_rad1','d41_A1_value','(vars a).rad 1'])]:
 s=(P/'src/DiophantineConsistency'/f'Sign33Macro{name}.lean').read_text();assert all(x in s for x in terms)
up=D/'reviews/nine-seed33-jones-vars-bd-terminal-frontier-independent/check.py';assert H(up)=='32bab5f50f326c17c0b51ae13d91db78a9fcfe7f698a9d490069ec7caa306bcb';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'symbolic Cd=dvnd and A0/A1 radicands only; rank opaque, no full output semantics'},sort_keys=True,indent=2))
