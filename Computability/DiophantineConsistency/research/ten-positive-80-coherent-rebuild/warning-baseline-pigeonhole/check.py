#!/usr/bin/env python3
"""Compare failed replay warnings with the retained source-pinned baseline."""
from hashlib import sha256
from pathlib import Path
import json
H=Path(__file__).resolve().parent; D=H.parents[2]
ATT=H.parent/'observations/attempt01';OUT=H/'observation.json'
REC=D/'reviews/nine-variable-ipra-stages-6-9-author-observation/author/receipts/008.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'observation exists')
receipt=json.loads(REC.read_text()); run=json.loads((ATT/'result.json').read_text())
stage=run['stages'][2];need(stage['module']=='DiophantineConsistency.ArithmeticPellPigeonhole' and stage['exit']==0 and stage['reason'] is None,'stage failed')
need(stage['source_sha256']==receipt['source_sha256'],'source hash mismatch')
baseline=Path('/tmp/nine-ipra-guarded-author-20261102-h/warning-policies/008.log')
need(sha(baseline)==receipt['warning_policy']['baseline_sha256'],'baseline drift')
source=next(s for s in stage['command'] if s.endswith('.lean'))
stdout=(ATT/'stage-003.stdout').read_text();stderr=(ATT/'stage-003.stderr').read_text()
normalized=(stdout+stderr).replace(source,'<SOURCE>')
expected=baseline.read_text();need(normalized==expected,'normalized log differs')
def accept(text):return text==expected
tests={'exact':accept(normalized),'changed_location':accept(normalized.replace(':40:4:',':40:5:',1)),
       'added_warning':accept(normalized+'warning(lean.extra): extra\n'),
       'added_error':accept(normalized+'error(lean.extra): extra\n'),
       'removed_warning':accept(normalized.replace('warning:', 'notice:',1))}
need(tests=={'exact':True,'changed_location':False,'added_warning':False,'added_error':False,'removed_warning':False},'mutation policy failed')
result={'status':'MATCH_EXACT_NORMALIZED','source_sha256':stage['source_sha256'],
 'baseline':str(baseline),'baseline_sha256':sha(baseline),'receipt':str(REC),'receipt_sha256':sha(REC),
 'observed_stdout_sha256':sha(ATT/'stage-003.stdout'),'observed_stderr_sha256':sha(ATT/'stage-003.stderr'),
 'tests':tests,'scope':'exact warning-text comparison only; exception not yet approved for a replay'}
OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'sha256':sha(OUT),'tests':tests},sort_keys=True))
