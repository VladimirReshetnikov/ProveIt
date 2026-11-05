#!/usr/bin/env python3
"""Verify exact topology retry delta and prior failed evidence; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];a=D/'research/nine-sharing-norm38-reference-base-retry01';b=D/'research/nine-sharing-norm38-reference-base-retry02';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in [(b/'run.py','2f2f131adab6a2093c7815a874616e8445a6c1b3ca13f375d31f1eac4a735814'),(b/'source-manifest.json','5ec698212f0d6960885d3b524834dc36f9f59c4b970866d4fc59575dd00bd6b7'),(b/'src/DiophantineConsistency/Norm38ReferenceBase.lean','be7f61985d51b07cfda37da0d1ca40c7d44a01950ef6cf94866a5cb3e2bf1da2')]:assert sha(p)==h
old=(a/'src/DiophantineConsistency/Norm38ReferenceBase.lean').read_text();new=(b/'src/DiophantineConsistency/Norm38ReferenceBase.lean').read_text();frag='  simp only [NormAssignment38.gates, initialNodes, Topological]\n  all_goals decide';assert old.count(frag)==1 and old.replace(frag,'  simp only [NormAssignment38.gates, initialNodes, Topological]\n  repeat\' apply And.intro\n  all_goals decide')==new
old=(a/'run.py').read_text();new=(b/'run.py').read_text();assert old.replace('/tmp/nine-sharing-norm38-reference-base-retry01-20261105','/tmp/nine-sharing-norm38-reference-base-retry02-20261105').replace('4577e5397a6107c9d4d35012e930c1845b9830ed85f432e7445b6da2de5e4b06','5ec698212f0d6960885d3b524834dc36f9f59c4b970866d4fc59575dd00bd6b7')==new
st=a/'attempt01/state.json';assert sha(st)=='c683e8adf77e556f26790d94e14b712160b7d495e5170481fb14a3c93c9d17ea';s=json.loads(st.read_text());r=s['rows'][0];assert s['status']=='FAILED' and r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None and 'object_sha256' not in r
log=a/'attempt01/Norm38ReferenceBase-compile.txt';assert sha(log)==r['compile']['log_sha256']=='f36f14028dce35f310f819210be02e029b74bc4588dde5ecb2cc5af1c39c49d2';t=log.read_text();assert 'failed to synthesize' in t and 'Decidable' in t and 'sorryAx' in t
print(json.dumps({'status':'PASS_RETRY02_DELTA_AND_PRIOR_FAILURE_ONLY','source_sha256':sha(b/'src/DiophantineConsistency/Norm38ReferenceBase.lean'),'runner_sha256':sha(b/'run.py'),'prior_state_sha256':sha(st),'scope':'No Lean retry, new topology proof or endpoint.'},indent=2,sort_keys=True))
