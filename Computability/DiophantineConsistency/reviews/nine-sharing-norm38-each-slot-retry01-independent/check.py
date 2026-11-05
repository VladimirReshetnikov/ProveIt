#!/usr/bin/env python3
"""Verify retained failure and narrow explicit-theorem-argument retry, no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());O=D/'research/nine-sharing-norm38-each-slot-check';N=D/'research/nine-sharing-norm38-each-slot-retry01';T=Path('/tmp/nine-sharing-norm38-each-slot-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(O/'run.py','78d0525ff975850259ed0b48c0ceae45d627f375e9ab693d67afc2bf8b7356ab'),(O/'source-manifest.json','ad0aded0521481691a4e9e23158053e3634ce6f7b0314f99669378daf6ed2a8c'),(N/'run.py','79e41695f3df41b1b50e91236e42e11666f95cd3461e86ab0588f5ac062ad0d9'),(N/'source-manifest.json','573cb5d57dc7d15544fc6e1b274ab42f8bd6f61fa84999c84bb891ad853e376b'),(O/'attempt01/state.json','8d0a9a33484138c7ae8ccb9e91641a6d5fa2d6da54f23388c01a8b078973cbb4'),(O/'attempt01/outer-terminal-author-record.json','e8042a265aa98adecb1240ff01663fb5481b4cbf69305248a26ec43352b86fab')]:need(sha(p)==h,'pin '+str(p))
r=(O/'run.py').read_text().replace('/tmp/nine-sharing-norm38-each-slot-check-20261105','/tmp/nine-sharing-norm38-each-slot-retry01-20261105').replace('ad0aded0521481691a4e9e23158053e3634ce6f7b0314f99669378daf6ed2a8c','573cb5d57dc7d15544fc6e1b274ab42f8bd6f61fa84999c84bb891ad853e376b');need(r==(N/'run.py').read_text(),'runner delta')
f='src/DiophantineConsistency/Norm38EachSlot.lean';old=(O/f).read_text();new=(N/f).read_text();a='exact (internalZero_iff.mp (all _ hm))';b='exact ((internalZero_iff _ _).mp (all _ hm))';need(old.count(a)==1 and new==old.replace(a,b) and sha(N/f)=='54cc7ca1a6fa4c6dac835a3ac5826d71b9edbf166d4c8505d8ac72a3f84f5232','proof delta');m=json.loads((N/'source-manifest.json').read_text())['rows'];need(len(m)==1 and m[0]['module']=='DiophantineConsistency.Norm38EachSlot' and sha(root/m[0]['source'])==m[0]['source_sha256']==sha(N/f) and m[0]['imports']==re.findall(r'^import ([A-Za-z0-9_.]+)$',new,re.M),'manifest')
s=json.loads((O/'attempt01/state.json').read_text());ob=json.loads((O/'attempt01/outer-terminal-author-record.json').read_text());need(sha(T/'state.json')==sha(O/'attempt01/state.json') and s['status']=='FAILED' and len(s['rows'])==1 and ob['outer_session_id']==12176 and ob['outer_exit_code']==1,'previous terminal');row=s['rows'][0];need(row['deps']['exit']==0 and row['compile']['exit']==1 and row['compile']['stop_reason'] is None and not row.get('object_sha256'),'failure status')
for typ in ('deps','compile'):
 p=O/'attempt01'/('Norm38EachSlot-'+typ+'.txt');need(sha(p)==sha(T/p.name)==row[typ]['log_sha256'],'log '+typ)
need(sha(O/'attempt01/Norm38EachSlot-compile.txt')=='9ee5c0717047e4fd5fa6924cfd83b664b7446df70b56c776f9fc7c1af5d7dc82' and 'Unknown constant' in (O/'attempt01/Norm38EachSlot-compile.txt').read_text(),'failed diagnostic')
for path,v in row['direct_guard'].items():
 p=Path(path)
 if v is None:need(not os.path.lexists(p),'absence '+path)
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'guard '+path)
for path,target in s['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
q=subprocess.run([sys.executable,'-I','-S','-B',str(N/'run.py'),'--preflight'],capture_output=True,text=True,timeout=60);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT','preflight '+q.stderr)
print(json.dumps({'status':'PASS_SCOPED_PRELAUNCH_REVIEW','prior_guards':len(row['direct_guard']),'prior_overlay_links':len(s['overlay_links']),'preflight_exit':q.returncode,'scope':'Prior author-recorded failure and source/provider point checks only; no Lean.'},sort_keys=True,indent=2))
