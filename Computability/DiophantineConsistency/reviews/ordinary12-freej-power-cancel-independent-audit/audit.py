#!/usr/bin/env python3
"""Read-only paired free-J conditional Mersenne cancellation audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-power-cancel-prototype'
PARENT=BASE/'reviews/ordinary12-freej-power-finish-independent-audit'
OUT=Path('/tmp/ipra-freej-power-cancel-pair-01')
PRIOR=Path('/tmp/ipra-freej-power-finish-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='e352772228bbaa752ee58f698acab67b26c596231390e05944db210683c73c26'
AUDIT='1f0357d7cb23f09fe6079e5ee744f7cf8cab6bd06d96b6e80b3167fbc9c86d7b'
SOURCE='8bf1b748ebe2486089d5af53dd2c6cc83744e6f8e371e364eb0e9aa2ee97ced8'
SEED='8070610cbaee1c035ba5a877e7c8605f42b84fd78a9a455b6a062b68f2dfc8b8'
OBJECT='86d1ccdf0108ae983c926ece94d3df311859c820b65553711505a2271bb7de4e'
LOG='7db187539a7340eab79303992ddf3343dd5a47c08923be393e06d51b1f71404e'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'FreeJPowerCancel.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.txt','author.log','peer.log'))]:
        blob=subprocess.run(['git','show','1fe43b4204:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=(PKG/'evidence/terminal.txt').read_text()
    need('Actual outer wrapper session 18464 exited 0.' in obs and
         'PASS_PAIRED_FREEJ_POWER_CANCEL '+RECEIPT in obs,'outer observation')
    for f in (PKG/'observations/attempt01.log',PKG/'observations/attempt01.txt'):
        blob=subprocess.run(['git','show','1fe43b4204:'+str(f.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(f),'exploratory committed bytes')
    need('exited 0' in (PKG/'observations/attempt01.txt').read_text() and
         not re.search(r'warning:|error:|sorryAx', (PKG/'observations/attempt01.log').read_text()),'exploratory observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_FREEJ_POWER_CANCEL' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/FreeJPowerCancel.lean';obj=run/'FreeJPowerCancel.olean';seed=proj/'FreeJPowerFinish.olean'
        need(sha(src)==sha(PKG/'FreeJPowerCancel.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'FreeJPowerFinish.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==91 and links==parentfiles,'parent coverage')
        for name in links:
            q=proj/name;target=prior/name
            need(q.resolve()==target.resolve() and sha(q)==sha(target),'parent link '+name)
        bb=run/'lib/BusyBeaver';priorbb=PRIOR/side/'lib/BusyBeaver'
        bbfiles={p.relative_to(priorbb) for p in priorbb.rglob('*.olean')}
        need({p.relative_to(bb) for p in bb.rglob('*.olean')}==bbfiles,'BusyBeaver coverage')
        for name in bbfiles:
            q=bb/name;need(q.is_symlink() and q.resolve()==(priorbb/name).resolve() and sha(q)==sha(priorbb/name),'BusyBeaver link')
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(seed),str(proj/'ArithmeticAdaptiveMersenne2011.olean')},'direct imports')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        log=PKG/'evidence'/(side+'.log')
        need(sha(log)==sha(run/'compiler.log')==row['log_sha256']==LOG and log.read_text()==row['stdout'],'logs')
        reports=re.findall(r"^'FreeJPowerCancel\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['graph_divides_power'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound'] and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':91,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_POWER_CANCEL_AUDIT','source_commit':'1fe43b4204',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':18464,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, power identity, cancellation, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
