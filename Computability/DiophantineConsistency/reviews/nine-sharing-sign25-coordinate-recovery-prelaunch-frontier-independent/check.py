#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-coordinate-recovery-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'3b942630630747fad1a75990b1a4168944f6f6d73066a860160442bc15caaa00','source-manifest.json':'87c17b40bd0c1e0899410f5083c822447b67842f586518cc7921d7995743ab8c','first-cut-survey.py':'7b604547d6df49e8d3349c086541204318afe5bcc3eafa8c7b5aee52a5ab7687','src/DiophantineConsistency/Sign25CoordinateRecover.lean':'32100b3564db789bf174c4d87f04030aa960b9d580be54bc857012e4ac0d9a99','src/DiophantineConsistency/Sign25CoordinateDrop.lean':'bd81cbd03bc7d9291e5ce941192129852ab1564de4bcf5487a747b909aeffe65'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2
for e in m:
 n=e['module'].split('.')[-1];assert H(P/'src/DiophantineConsistency'/f'{n}.lean')==e['source_sha256']==H(D.parents[1]/e['source'])
a=(P/'src/DiophantineConsistency/Sign25CoordinateRecover.lean').read_text();b=(P/'src/DiophantineConsistency/Sign25CoordinateDrop.lean').read_text();assert all(x in a for x in ['v 19 = v 17 * v 18','Sign25FirstCut.old_ell_row p','SharingSign26Squares.seed_zero_iff_residuals','apply ι_injective','rw [map_mul]','sub_eq_zero.mp he']);vec=re.search(r'!\[([^\]]+)\]',b);assert vec and [x.strip() for x in vec[1].split(',')]==[f'v {i}' for i in range(19)]+[f'v {i}' for i in range(20,27)];assert all(x in b for x in ['Sign25FirstCut.lift (drop v) = v','ell_coordinate p v hz','fin_cases j'])
for n,h in [('nine-sharing-sign25-remaining-cuts-terminal-frontier-independent','8d992e71b6a1982c205deea43b8a3e74002c5750f2e7231da53f04f5dcf3b3f0'),('nine-sharing-sign25-first-cut-terminal-frontier-independent','bdd993aaa2ab6425fb1497842b5de8765d7338b81d2b9e01d7780e296dbf9b7c')]:
 q=D/'reviews'/n/'check.py';assert H(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],check=True,capture_output=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],check=True,capture_output=True,text=True,timeout=180);assert json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'old zero implies product-coordinate recovery and lift(drop v)=v; no full zero bridge'},sort_keys=True,indent=2))
