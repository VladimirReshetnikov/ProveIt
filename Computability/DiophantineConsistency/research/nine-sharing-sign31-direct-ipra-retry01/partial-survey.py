#!/usr/bin/env python3
"""Authenticate only the successful generic row of a failed earlier run."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=Path('/tmp/nine-sharing-sign32-direct-ipra-retry01-20261106');BASE=Path('/tmp/nine-sharing-sign31-current-source-iff-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign32-direct-ipra-retry01/attempt01';need(H(p/'state.json')=='1049b0cfc7b7c7235f941802d1d160ed4477c3565195ef87f727fc1d1dfb0a7c' and H(p/'outer-result.json')=='06e7806e4d54cf82a37ac4d5678cb2903930e12207d2a268ac9b8f877a1920aa','receipt pins');d=json.loads((p/'state.json').read_text());need(d['status']=='FAILED' and len(d['rows'])==2,'partial scope');r=d['rows'][0];n='Sign32GenericRemoveInput';need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0 and r['object_sha256']=='0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b','successful row');need(H(ROOT/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(ROOT/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'],'source/object')
for k in ('deps','compile'):need(H(ROOT/f'{n}-{k}.txt')==r[k]['log_sha256'],'log '+k)
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
failed=d['rows'][1];need(failed['module']=='Sign32DirectExpressionSplit' and failed['compile']['exit']==-6 and H(ROOT/'Sign32DirectExpressionSplit-compile.txt')==failed['compile']['log_sha256'],'failure row')
need(not os.path.lexists(BASE/'lib/DiophantineConsistency/Sign32GenericRemoveInput.olean'),'generic collision')
for root in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(root/'DiophantineConsistency/Sign32GenericRemoveInput.olean'),'generic fallback collision')
print(json.dumps({'status':'PASS','generic_sha256':r['object_sha256'],'generic_realpath':str((ROOT/'lib/DiophantineConsistency/Sign32GenericRemoveInput.olean').resolve()),'scope':'only successful generic row used; later failed row excluded; inherited deeper ancestry'},sort_keys=True))
