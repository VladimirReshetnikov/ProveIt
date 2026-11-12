"""Check the unrestricted byte control against the full symbolic fixture set."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
kernel = HERE.parent / 'code/unrestricted_control.py'
cases = json.loads((HERE/'certificates.json').read_text())
results = []
for case in cases:
    expected = case['expected'] or case['name'] == 'direct_compound_transport_rejected'
    for optimized in [False, True]:
        command = [sys.executable]+(['-O'] if optimized else [])+[str(kernel)]
        result = subprocess.run(command,input=json.dumps(case['packet']),text=True,
                                capture_output=True,timeout=30)
        actual = result.returncode == 0 and result.stdout == 'ACCEPT\n'
        if actual != expected:
            raise ValueError((case['name'],optimized,result.stdout,result.stderr))
        results.append({'name':case['name'],'optimized':optimized,
                        'expected':expected,'actual':actual})
receipt = {'passed':True,'kernel_sha256':hashlib.sha256(kernel.read_bytes()).hexdigest(),
           'cli_runs':len(results),'results':results}
(HERE/'control_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'passed':True,'cli_runs':len(results)}))
