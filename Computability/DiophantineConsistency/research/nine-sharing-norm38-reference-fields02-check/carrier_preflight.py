#!/usr/bin/env python3
"""Compare retained successful Carrier65 producer to the reference-base overlay."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];B=D/'research/normalized106-fresh-base-model-build/attempt02/state.json';R=D/'research/nine-sharing-norm38-reference-base-retry02/attempt01/state.json';BT=Path('/tmp/normalized106-fresh-model-build-v2-20261105');RT=Path('/tmp/nine-sharing-norm38-reference-base-retry02-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(sha(B)=='c42e5d49c4234ff93e61b7dbadf63fe8e2d465f470f4772879694796d898272c' and sha(R)=='d3dc44f113f3cb6c176a67259b3d8df3c825a3ab9009f05374764ccddd7fb3ce','state pins');b=json.loads(B.read_text());r=json.loads(R.read_text());need(b['status']=='FAILED' and r['status']=='PASS' and len(r['rows'])==1,'state status');matches=[x for x in b['records'] if x['module']=='DiophantineConsistency.Carrier65'];need(len(matches)==1,'unique carrier');c=matches[0];need(c['deps_run']['exit']==0 and c['compile']['exit']==0,'carrier exits');need(sha(BT/'src/DiophantineConsistency/Carrier65.lean')==sha(D/'Lean/DiophantineConsistency/Carrier65.lean')==c['source_sha256']=='be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154' and sha(BT/'lib/DiophantineConsistency/Carrier65.olean')==c['object_sha256']=='10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f','carrier source/object')
for phase in ('deps_run','compile'):need(sha(c[phase]['log'])==c[phase]['log_sha256'],'carrier log '+phase)
for path,v in c['guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'carrier unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'carrier guard '+path)
link=RT/'lib/DiophantineConsistency/Carrier65.olean';need(link.is_symlink() and link.resolve()==(BT/'lib/DiophantineConsistency/Carrier65.olean').resolve() and sha(link)==c['object_sha256'],'carrier overlay');need(not os.path.lexists(RT/'lib/DiophantineConsistency/Norm38ReferenceFields02.olean'),'target shadow');print(json.dumps({'status':'PASS_POINT_IN_TIME_CARRIER_PROVIDER','carrier_guards':len(c['guard']),'carrier_sha256':c['object_sha256'],'scope':'Successful recorded Carrier65 producer in an overall-failed run and selected reference-overlay route only; no Lean or full transitive/dynamic ancestry.'},sort_keys=True,indent=2))
