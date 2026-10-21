#!/usr/bin/env python3
"""Queue the already-reviewed closed clients after this exact serial build completes."""
from pathlib import Path
import json,subprocess,sys,time
P=Path(__file__).resolve().parent
while not (P/'build-complete.json').exists():
 if not Path('/proc/3741806').exists():raise SystemExit('Build process ended without complete receipt; no audits started.')
 time.sleep(2)
x=json.loads((P/'build-complete.json').read_text())
assert x['status']=='FULL_CURRENT_SOURCE_CLOSURE_PASS' and x['modules']==204
commands=[
 [sys.executable,'-B',str(P/'audit_serial_v3.py'),'/tmp/k215-endpoint-audit/EndpointAudit215.lean','independent'],
 [sys.executable,'-B',str(P/'audit_serial_v3.py'),str(P/'workspace/K215Audit.lean'),'axiom-components'],
 [sys.executable,'-B',str(P/'review_final.py')],
 [sys.executable,'-B',str(P/'publish_lean_evidence.py'),'--complete'],
]
for command in commands:
 print('START',command,flush=True)
 result=subprocess.run(command)
 if result.returncode:raise SystemExit(result.returncode)
print('ALL_LEAN_CLOSURE_AUDIT_PUBLICATION_PASS',flush=True)
