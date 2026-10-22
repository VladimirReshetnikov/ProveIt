from pathlib import Path
import json,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');S=Path('/tmp/k215-phase13-upstream-shared');O=Path('/tmp/k215-phase13-root')
base=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase13'
rows=[
('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean',S/'expected/upstream-core.lean','a128ddd54eebe7a49f75ea25c513c6229f1304fb51a9d9b07539a89b8a094656','bd07364a829e8a1535b0ecf1ee6ed0c292d5af35e01a6db8f152dd2610e247d8'),
('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Lukasiewicz.lean',S/'expected/upstream-lukas.lean','5bae5186d702414adc6f1f7006d241a48ef9f24e53de48c90f84394ce3c500d3','7d443a733b5c5ddd0d49728cf1ea7d855dd445f156934c13578bacc008c59874'),
('Computability/BusyBeaver/Research/ZFC/k225-formal/generate_dominated_implication_lean.py',S/'production/generate_dominated_implication_lean.py','31fdd538a6cf001d30fa26cb3d4d411306d3df52bea1ede62a54fc17608f1882','ebcbb86642d4d389748451dc662b42f7ac62e7aa4b235bbf4e5d8e5a1ec5c1e9'),
('Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/derivation_core.txt',S/'production/rho8cd/derivation_core.txt','f0a2e60d3574615aefa8ce987e783b69a89dd95516dc7238caa569b4a938f116','4141248ed90a6813c07f274351336963acde1d82f6ea463a33e5f7d64bed8005'),
('Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/generate_domrho8_cd.py',R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase12/upstream-merge/inputs/Research/ZFC/k225-formal/rho8cd/generate_domrho8_cd.py','7aedc93ec04262ae0f7f70bcb89f58cd0875c82eeffa863da1072c847f1b5034','63da860d3a957010c53d783a2b8995acef3d8e3806823f24fc5833738dc1d56a'),
]
files=[]
for target,source,before,after in rows:
 old=(R/target).read_bytes();new=source.read_bytes();assert hashlib.sha256(old).hexdigest()==before and hashlib.sha256(new).hexdigest()==after
 archived=base/'integration/before'/target;assert not archived.exists();archived.parent.mkdir(parents=True,exist_ok=True);archived.write_bytes(old)
 files.append({'target':target,'source':str(source),'bytes':len(new),'sha256':after,'before_bytes':len(old),'before_sha256':before,'archived_before':str(archived.relative_to(R))})
record={'status':'PLANNED_NOT_APPLIED','files':files,'scope':'Two candidate Lean sources and the synchronized own maintained producer/ancestry input; upstream research renderer copied as data only. No proof-source adoption, producer or compiler execution in this preparation.'}
(O/'adoption-plan.json').write_text(json.dumps(record,indent=2)+'\n');print('PASS five-target plan and exact before archives; no current-source writes')
