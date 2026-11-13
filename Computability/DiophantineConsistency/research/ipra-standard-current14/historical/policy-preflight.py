#!/usr/bin/env python3
"""Check the current14 policy against each recorded author module log."""
import hashlib,json,re
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];TRIAL=ROOT/'reviews/ipra-standard-current14-author-trial'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
policy_path=HERE/'task-policy.json';manifest_path=HERE.parent/'author-additions.json';state_path=TRIAL/'state.json'
inputs=[Path(__file__),policy_path,manifest_path,state_path];policy=json.loads(policy_path.read_text());manifest=json.loads(manifest_path.read_text());state=json.loads(state_path.read_text())
logs=sorted((TRIAL/'logs').glob('*.log'));inputs.extend(logs)
before={str(p.resolve()):H(p) for p in inputs}
assert H(policy_path)=='aed46974c461c626aa93781e5e927fb1b63b93d92c51202343ea0e2e3ef08413'
assert H(manifest_path)=='005af2258215bedb54a8f0589eaf898a2b80c6cfa443ce8fa48621cea40b022a'
assert H(state_path)=='bd643e25b07538400b7f7cc397ff64af6ddc6d73f1e563d69fb5c6aed863da61'
order=manifest['order'];assert len(order)==16 and policy['addition_order']==order==[r['module'] for r in state['rows']]
assert policy['sources']==manifest['sources'] and policy['target']==order[-1]
expected={n:manifest['axiom_reports'].get(n,[]) for n in order}
assert policy['expected_axiom_by_module']==expected and policy['expected_axiom_names']==expected[order[-1]]
assert sum(map(len,expected.values()))==4 and sum(bool(x) for x in expected.values())==1
pattern=re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",re.M)
for i,row in enumerate(state['rows']):
    files=list((TRIAL/'logs').glob(f'{i:03d}-*.log'));assert len(files)==1
    path=files[0];assert H(path)==row['log_sha256'] and row['exit']==0
    assert [name for name,_ in pattern.findall(path.read_text())]==expected[row['module']]
assert len(logs)==16 and {str(p.resolve()):H(p) for p in inputs}==before
result={'status':'PASS_CURRENT14_AUTHOR_POLICY_LOG_PREFLIGHT','inputs_sha256':before,'modules':16,'diagnostics':4,
        'scope':'Finite policy/log comparison only; not a Lean replay, independent external audit, or matched extension.'}
out=HERE/'policy-preflight-receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(result['status'],H(out))
