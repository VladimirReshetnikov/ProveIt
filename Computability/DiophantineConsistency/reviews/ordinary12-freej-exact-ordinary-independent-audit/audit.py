#!/usr/bin/env python3
"""Read-only paired exact ordinary carrier index audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-exact-ordinary-prototype'
PARENT=BASE/'reviews/ordinary12-freej-ordinary-rank-independent-audit'
OUT=Path('/tmp/ipra-freej-exact-ordinary-pair-01')
PRIOR=Path('/tmp/ipra-freej-ordinary-rank-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='fec23d0d6fdc8b66041bf67b41f10a80e8dc3b9d48bd0b7138cfb6bf19374c6c'
AUDIT='76117c3b55df96ae16ff4074d76687c9ffea58ad965b2e05f5db017bb88ad976'
SOURCE='f132220a2a5cc38c73858ddc3b7cf943567199de5ab13cbcdec8126f232d7049'
SEED='3fc535096df439cff6393b7920dda436909ab792923fc40fb1d949223a1b3179'
OBJECT='d30414abd21b28eb9a9c2d62caccc6945a3cb6d2b699d35ebc3d3ab4fe033a5e'
LOG='a83b7c71bdcef14c7f44b62cc63e4799a6b41d80dc68079a0e1f47b1ad79aeac'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'FreeJExactOrdinary.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.txt','author.log','peer.log'))]:
        blob=subprocess.run(['git','show','4daaa04277:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=(PKG/'evidence/terminal.txt').read_text()
    need('Actual outer wrapper session 82674 exited 0.' in obs and
         'PASS_PAIRED_FREEJ_EXACT_ORDINARY_INDEX '+RECEIPT in obs,'outer observation')
    failed=PKG/'observations/attempt01.log';need('error:' in failed.read_text() and 'sorryAx' in failed.read_text(),'failed attempt retained')
    for f in (failed,PKG/'observations/attempt01.lean'):
        blob=subprocess.run(['git','show','4daaa04277:'+str(f.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(f),'failed attempt committed bytes')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_FREEJ_EXACT_ORDINARY_INDEX' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/FreeJExactOrdinary.lean';obj=run/'FreeJExactOrdinary.olean';seed=proj/'FreeJOrdinaryRank.olean'
        need(sha(src)==sha(PKG/'FreeJExactOrdinary.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'FreeJOrdinaryRank.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==86 and links==parentfiles,'parent coverage')
        for name in links:
            q=proj/name;target=prior/name
            need(q.resolve()==target.resolve() and sha(q)==sha(target),'parent link '+name)
        bb=run/'lib/BusyBeaver';priorbb=PRIOR/side/'lib/BusyBeaver'
        bbfiles={p.relative_to(priorbb) for p in priorbb.rglob('*.olean')}
        need({p.relative_to(bb) for p in bb.rglob('*.olean')}==bbfiles,'BusyBeaver coverage')
        for name in bbfiles:
            q=bb/name;need(q.is_symlink() and q.resolve()==(priorbb/name).resolve() and sha(q)==sha(priorbb/name),'BusyBeaver link')
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(seed),str(proj/'ArithmeticPellResidueAux.olean')},'direct imports')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        log=PKG/'evidence'/(side+'.log')
        need(sha(log)==sha(run/'compiler.log')==row['log_sha256']==LOG and log.read_text()==row['stdout'],'logs')
        reports=re.findall(r"^'FreeJExactOrdinary\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['exact_ordinary_indices'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound'] and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':86,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_EXACT_ORDINARY_AUDIT','source_commit':'4daaa04277',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':82674,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, f-exponent equality, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
