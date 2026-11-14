#!/usr/bin/env python3
"""Rebuild and independently verify every delivered PA194DHS certificate."""
from pathlib import Path
import hashlib,json,subprocess,sys
if not __debug__:raise RuntimeError('Run verification without Python -O')
root=Path(__file__).resolve().parent
provenance=json.loads((root/'PROVENANCE.json').read_text())
for name,want in provenance['copied_or_pinned_input_hashes'].items():
 actual=hashlib.sha256((root/name).read_bytes()).hexdigest()
 assert actual==want,('Pinned input changed',name,want,actual)
for command in [[sys.executable,'-B','build.py'],[sys.executable,'-B','proof/check_commands.py','--output','evidence/commands.json'],[sys.executable,'-B','verification/check.py']]:
 subprocess.run(command,cwd=root,check=True)
subprocess.run([sys.executable,'-B','comparison/compare_candidate.py','machine/machine.tm','--output','evidence/novelty.json'],cwd=root,check=True)
assert json.loads((root/'evidence/novelty.json').read_text())['new_relative_to_this_frontier']
subprocess.run([sys.executable,'-B','search/append_zero/verify_all_starts.py','search/append_zero/rejected_append0.native.tm','--baseline','search/append_zero/baseline_pa194.tm','--labels','search/append_zero/baseline_labels.json','--output','search/append_zero/independent_receipt.json'],cwd=root,check=True)
print(json.dumps({'PA194DHS':'PASS','working_states':194,'scope':'All specified executable checks; ordinary mathematical PA calibration is documented separately, not a proof-assistant kernel export.'},indent=2))
