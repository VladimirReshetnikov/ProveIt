
if not __debug__:
    raise RuntimeError("Verification requires enabled assertions; do not use python -O or PYTHONOPTIMIZE.")

from copy import deepcopy
from pathlib import Path
import json
from check_patch import verify
p=json.load(open(Path(__file__).parent/'patch.json'));tests=[]
for kind in('missing_block','short_history','bad_initial_state','wrong_duration','missing_local_cell'):
 q=deepcopy(p)
 if kind=='missing_block':q['blocks'].pop()
 elif kind=='short_history':q['history_depth']['13']=1
 elif kind=='bad_initial_state':q['start']=13
 elif kind=='wrong_duration':q['blocks'][0]['durations'][0]=1
 else:del q['blocks'][0]['context']['-2']
 try:verify(q)
 except (AssertionError,KeyError):tests.append(dict(mutation=kind,rejected=True))
 else:raise AssertionError(('accepted mutant',kind))
print(json.dumps(tests))
