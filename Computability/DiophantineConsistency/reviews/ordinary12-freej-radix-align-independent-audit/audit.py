#!/usr/bin/env python3
"""Read-only paired free-J conditional radix alignment audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-radix-align-prototype'
PARENT=BASE/'reviews/ordinary12-freej-power-cancel-independent-audit'
OUT=Path('/tmp/ipra-freej-radix-align-pair-01')
PRIOR=Path('/tmp/ipra-freej-power-cancel-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='47032d5f0cca7c2aa42ccf5247ddccee06d2b238a9856b2aac664a62717fe998'
AUDIT='3ca8ec87488143974e542c82edc6d2a544c1f0bc4b55fe18fec2fb5dd3601a01'
SOURCE='5def0e56555cdac09d101f59b61c470220c3c14ea9e858bf288e258c43d90f56'
SEED='86d1ccdf0108ae983c926ece94d3df311859c820b65553711505a2271bb7de4e'
OBJECT='ebc83df3fa0343d2e20f265927c715e9bf813b79cb5338c72540ec3f6dfe84e4'
LOG='cc6044423f1466659a52a1415d399e7bf6efd3da0c2f7d61e2d7341ef0132f42'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'FreeJRadixAlignment.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.txt','author.log','peer.log'))]:
        blob=subprocess.run(['git','show','2400122be6:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=(PKG/'evidence/terminal.txt').read_text()
    need('Actual outer wrapper session 55579 exited 0.' in obs and
         'PASS_PAIRED_FREEJ_RADIX_ALIGN '+RECEIPT in obs,'outer observation')
    for f in (PKG/'observations/attempt01.log',PKG/'observations/attempt01.txt'):
        blob=subprocess.run(['git','show','2400122be6:'+str(f.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(f),'exploratory committed bytes')
    need('exited 0' in (PKG/'observations/attempt01.txt').read_text() and
         not re.search(r'warning:|error:|sorryAx', (PKG/'observations/attempt01.log').read_text()),'exploratory observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_FREEJ_RADIX_ALIGN' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/FreeJRadixAlignment.lean';obj=run/'FreeJRadixAlignment.olean';seed=proj/'FreeJPowerCancel.olean'
        need(sha(src)==sha(PKG/'FreeJRadixAlignment.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'FreeJPowerCancel.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==92 and links==parentfiles,'parent coverage')
        for name in links:
            q=proj/name;target=prior/name
            need(q.resolve()==target.resolve() and sha(q)==sha(target),'parent link '+name)
        bb=run/'lib/BusyBeaver';priorbb=PRIOR/side/'lib/BusyBeaver'
        bbfiles={p.relative_to(priorbb) for p in priorbb.rglob('*.olean')}
        need({p.relative_to(bb) for p in bb.rglob('*.olean')}==bbfiles,'BusyBeaver coverage')
        for name in bbfiles:
            q=bb/name;need(q.is_symlink() and q.resolve()==(priorbb/name).resolve() and sha(q)==sha(priorbb/name),'BusyBeaver link')
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(seed),str(proj/'ArithmeticRadixAlignment.olean')},'direct imports')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        log=PKG/'evidence'/(side+'.log')
        need(sha(log)==sha(run/'compiler.log')==row['log_sha256']==LOG and log.read_text()==row['stdout'],'logs')
        reports=re.findall(r"^'FreeJRadixAlignment\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['graph_alignment'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound'] and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':92,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_RADIX_ALIGN_AUDIT','source_commit':'2400122be6',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':55579,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, power identity, cancellation, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
