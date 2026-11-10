"""Compare the same forbidden compound-transport packet in two checkers."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

here = Path(__file__).resolve().parent
atomic, unrestricted = map(lambda p: Path(p).resolve(), sys.argv[1:3])
cases = json.loads((here/'certificates.json').read_text())
case = next(c for c in cases if c['name']=='direct_compound_transport_rejected')
results = []
for kernel, expected in [(atomic,False),(unrestricted,True)]:
    for optimized in [False,True]:
        command = [sys.executable]+(['-O'] if optimized else [])+[str(kernel)]
        p = subprocess.run(command,input=json.dumps(case['packet']),text=True,capture_output=True)
        actual = p.returncode == 0 and p.stdout == 'ACCEPT\n'
        if actual != expected: raise AssertionError((str(kernel),optimized,p.stdout,p.stderr))
        results.append({'kernel':str(kernel),'sha256':hashlib.sha256(kernel.read_bytes()).hexdigest(),
                        'optimized':optimized,'expected':expected,'actual':actual})
record={'passed':True,'case':case['name'],'cli_runs':len(results),'results':results}
(here/'guard_control.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
