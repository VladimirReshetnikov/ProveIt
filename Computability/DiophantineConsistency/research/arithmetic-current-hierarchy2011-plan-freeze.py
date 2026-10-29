from pathlib import Path
import hashlib, json, shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency/research'
plan=D/'arithmetic-current-hierarchy2011-cache-plan.json'
H=D/'arithmetic-current-hierarchy2011-plan-history'
def rec(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
x=json.loads(plan.read_text())
assert rec(plan)['sha256']=='b5170702be3f9d00916436b1fe26af3edc1db2defe02303d6c0bf1e671ac1c3f'
for pin in x['pins']:
 assert rec(Path(pin['path']))['sha256']==pin['sha256'],pin['path']
shutil.copy2('/tmp/current-hierarchy2011-plan-attempt4.log',H/'v4-log.txt')
shutil.copy2(__file__,D/'arithmetic-current-hierarchy2011-plan-freeze.py')
readme=D/'arithmetic-current-hierarchy2011-plan-README.md'
readme.write_text('''# Current equation hierarchy: frozen build proposal

The exact named no-zero and ZFC consistency sentences will receive Π1 certificates,
and their unchanged biconditional will receive a Π2 certificate. This supplies no
PRA calculus, conservation theorem or PRA derivation.

The final read-only audit passed 4,747 comparisons over 2,259 paths. Its current
header closure has 430 modules, including 139 Foundation modules. There are 338
reusable modules (755 artifacts), 92 required non-Foundation source refreshes,
and two proposed new leaves. The external boundary has 57 primaries and 171
companions; all 983 existing first providers were checked. No Foundation refresh.

The original successful 40-refresh plan and both rejected follow-ups are retained.
The final 92-refresh plan records the new BinderAbsorption source change. It uses
no source-stale descendants and no unaudited upstream endpoint objects. No overlay,
Lean compiler, Lake compiler, shared source/object mutation or Git change occurred.

Implementation awaits independent verification. Every refreshed source, both new
sources and the exact future driver must be read before capped private execution.
Successful objects and failures must be retained; all inputs are snapshotted first.
''')
files=[plan,D/'arithmetic-current-hierarchy2011-cache-audit.py',D/'arithmetic-current-hierarchy2011-proposal.md',D/'arithmetic-current-hierarchy2011-plan-freeze.py',readme,*sorted(H.iterdir())]
manifest=D/'arithmetic-current-hierarchy2011-plan-FILES.json'
manifest.write_text(json.dumps(dict(scope='Read-only exact hierarchy plan; no implementation or compiler',files=[rec(p)for p in files]),indent=2)+'\n')
print(json.dumps(dict(plan=rec(plan),proposal=rec(D/'arithmetic-current-hierarchy2011-proposal.md'),auditor=rec(D/'arithmetic-current-hierarchy2011-cache-audit.py'),manifest=rec(manifest),file_count=len(files),snapshot_head=x['snapshot_head'],final_head=x['final_head']),indent=2))
