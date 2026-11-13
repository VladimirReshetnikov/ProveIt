#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-rankcode-link-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'7ce0bd1d3f67f1c41782e72ef5b56d9ac1ec5e8b3e8caf3d38c66bcd063d2a9d','provider_preflight.py':'bcfd53f1985f0dfc0f2c6782231408ed6139874f6f5b60ea126bebc65715894d','source-manifest.json':'7e31d072f3aa3191f65e9c74eebcfc31d62a5336ff7cab1f5d74395ad337676a','src/DiophantineConsistency/Norm38MacroRankCodeLink.lean':'4cfa6b974a6243ad55b2b311c4bc3049498cf7ef62cb9dc836e2ae7886918f43'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Norm38MacroRankCodeLink.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='4cfa6b974a6243ad55b2b311c4bc3049498cf7ef62cb9dc836e2ae7886918f43';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Norm38MacroRankCarry'];assert re.findall(r'^theorem (\w+)',s,re.M)==['rankRaw_eq_rankCode'];assert 'rankRaw z b (b ^ (5 : Nat)) q n e ell lam g theta' in s and 'NinePolynomial.rankCode (1 : R) z b e g ell n q theta lam' in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled generic rank identity only; no Lean replay'},sort_keys=True,indent=2))
