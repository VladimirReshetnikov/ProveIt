#!/usr/bin/env python3
"""Read-only source and preterminal-refusal review; never runs the audit."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2];d=base/'reviews/current14-extension-v3-terminal-independent';audit=d/'audit.py';refusal=d/'preterminal-refusal.json';runner=base/'research/current14-structured-endpoint-coherent-runner-v3/runner.py'
expected={'audit':'572f47d8361b58f342bb1b11725e76c1099a1bc67a0d9996cc00443ff5ec5236',
          'refusal':'a07e2f706f7c9a960040390dbb79ff4802df4261ad6d3cd8675692337b81c338',
          'runner':'cf8a7b0d6df7b6c99f3eb4d9247f226c3fc0f0051fefa6dede438b2511ade349'}
need(sha(audit)==expected['audit'] and sha(refusal)==expected['refusal'] and sha(runner)==expected['runner'],'pin mismatch')
rec=json.loads(refusal.read_text());need(rec['exit']==1 and rec['audit_sha256']==expected['audit'] and
 'missing observed supervisor terminal evidence' in rec['stderr'] and not rec['stdout'],'refusal mismatch')
s=audit.read_text()
for tok in ("audit_sha=sha(__file__)","need(not RESULT.exists()", "need(OBS.is_file() and SUP.is_file()",
            "obs.get('observed_session_exit')==0", "sup.get('child_exit')==0",'client.authenticate()',
            'len(records)==len(ctx[\'order\'])==61', "occurrences=collections.Counter(lines)",
            "count in (1,2) if module=='Init' else count==1", "q['session_drained'] is True",
            "sha(__file__)==audit_sha and sha(RUNNER)==EXPECTED_RUNNER", "with RESULT.open('x')"):
    need(tok in s,'missing source gate '+tok)
out={'status':'PASS_SOURCE_AND_REFUSAL_REVIEW','script_sha256':sha(__file__),
     'audit_sha256':expected['audit'],'refusal_sha256':expected['refusal'],'runner_sha256':expected['runner'],
     'scope':'Static source and retained preterminal refusal only; no live audit, supervisor exit observation, Lean replay or positive-path test.'}
print(json.dumps(out,indent=2,sort_keys=True))
