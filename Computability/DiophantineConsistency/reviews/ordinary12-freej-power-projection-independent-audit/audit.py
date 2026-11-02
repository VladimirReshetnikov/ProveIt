#!/usr/bin/env python3
"""Read-only paired free-J power projection audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-power-projection-prototype'
PARENT=BASE/'reviews/ordinary12-freej-exact-transport-independent-audit'
OUT=Path('/tmp/ipra-freej-power-projection-pair-01')
PRIOR=Path('/tmp/ipra-freej-exact-transport-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='046ea7ed43ed4bce073bfd3a07cf59b2345aed4d9384361758887b9432cda10b'
AUDIT='d6d96fcb0ff3c1f8a6b6811eaf4f09ccbe981bb08a956200649b746a3e259da5'
SOURCE='0a30e58ab582c03e634a672171da821f82c48c75d17212237bd4b9d9ac81d42f'
SEED='5a182673c66b9e0815fc395e7ab1991fccb14f7cb6ba3491c503b5e0f19dfc79'
OBJECT='bff8f46bce63d3e960d243a77f8901b340f7a66c7492983494abe5b22ecb1014'
LOG='1300195fd7f58351500875d1d8016268e3f34ea078c2ec33c89bb8861579b756'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'FreeJPowerProjection.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.txt','author.log','peer.log'))]:
        blob=subprocess.run(['git','show','46f110ef9d:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=(PKG/'evidence/terminal.txt').read_text()
    need('Actual outer wrapper session 6760 exited 0.' in obs and
         'PASS_PAIRED_FREEJ_POWER_PROJECTION '+RECEIPT in obs,'outer observation')
    for f in (PKG/'observations/attempt01.log',PKG/'observations/attempt01.lean',PKG/'observations/attempt02.log',PKG/'observations/attempts.txt'):
        blob=subprocess.run(['git','show','46f110ef9d:'+str(f.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(f),'exploratory committed bytes')
    need('error:' in (PKG/'observations/attempt01.log').read_text() and 'sorryAx' in (PKG/'observations/attempt01.log').read_text() and
         not re.search(r'warning:|error:|sorryAx', (PKG/'observations/attempt02.log').read_text()),'exploratory observations')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_FREEJ_POWER_PROJECTION' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/FreeJPowerProjection.lean';obj=run/'FreeJPowerProjection.olean';seed=proj/'FreeJExactTransport.olean'
        need(sha(src)==sha(PKG/'FreeJPowerProjection.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'FreeJExactTransport.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==88 and links==parentfiles,'parent coverage')
        for name in links:
            q=proj/name;target=prior/name
            need(q.resolve()==target.resolve() and sha(q)==sha(target),'parent link '+name)
        bb=run/'lib/BusyBeaver';priorbb=PRIOR/side/'lib/BusyBeaver'
        bbfiles={p.relative_to(priorbb) for p in priorbb.rglob('*.olean')}
        need({p.relative_to(bb) for p in bb.rglob('*.olean')}==bbfiles,'BusyBeaver coverage')
        for name in bbfiles:
            q=bb/name;need(q.is_symlink() and q.resolve()==(priorbb/name).resolve() and sha(q)==sha(priorbb/name),'BusyBeaver link')
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(seed)},'direct imports')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        log=PKG/'evidence'/(side+'.log')
        need(sha(log)==sha(run/'compiler.log')==row['log_sha256']==LOG and log.read_text()==row['stdout'],'logs')
        reports=re.findall(r"^'FreeJPowerProjection\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['graph_projection'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound'] and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':88,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_POWER_PROJECTION_AUDIT','source_commit':'46f110ef9d',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':6760,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, power identity, cancellation, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
