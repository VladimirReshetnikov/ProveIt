#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-current-source-iff-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'run.py':'eded4160e6d5c573439a5af18bd30f47b81d468ca5e3ab5a1959e584abfd2074','union-survey.py':'0d564026184ecef90c83defecee633fdcabe32c318935b56cfda1f5a7360b60a','union.json':'bf02ec17cfafbdfbdf0e9d5ac5ae5f694de27a2912aa3392c4f67022b89f08fc','source-manifest.json':'07abb1a3038379f066e0ca01723c5364e4a06be72e319b7c03d5b93701c607c9','src/DiophantineConsistency/Sign31CurrentSourceIff.lean':'037b472c62fabdb7ac18d392ffe53615e5bb472b031fe8e006263f77fcabd76a'}
for n,h in pins.items():assert H(P/n)==h,n
s=(P/'src/DiophantineConsistency/Sign31CurrentSourceIff.lean').read_text();assert '∃ w : Fin 31 → V' in s and '∃ u : Fin 14 → V' in s and 'exists_same_input CurrentWindowCarry2011.ports (1 : V)' in s and 'h32.symm.trans Sign32CurrentSourceIff.seed_exists_iff_source' in s
u=json.loads((P/'union.json').read_text());assert u['overlap_count']==1059 and len(u['extra'])==225
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],cwd=D,text=True,capture_output=True,timeout=120);assert r.returncode==0,(r.returncode,r.stderr);assert json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS','preflight_exit':r.returncode,'overlap':1059,'injected_extra':225,'scope':'Source and point-in-time provider prelaunch; no Lean replay or transitive trace.'},sort_keys=True))
