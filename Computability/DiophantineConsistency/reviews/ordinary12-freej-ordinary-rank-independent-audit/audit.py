#!/usr/bin/env python3
"""Read-only paired graph ordinary rank audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-ordinary-rank-prototype'
PARENT=BASE/'reviews/ordinary12-freej-graph-auxiliary-independent-audit'
OUT=Path('/tmp/ipra-freej-ordinary-rank-pair-01')
PRIOR=Path('/tmp/ipra-freej-graph-auxiliary-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='fc8653e042d8a04a0a304820251d9315f43360c915d31116368cd76261a23ee6'
AUDIT='f7f557359dca73b583d7dff59db23cc743b59eb7a55c078b89e15ea1a031fe0c'
SOURCE='1cbc9b564edff3d1c7fe8cbdbb292577cfe6acdb46e280d9983755d53f78e4fc'
SEED='abe39b30a9ab0d68cdd666957a91f1f06b11edeae7055ca220f9d37182ccfff7'
OBJECT='3fc535096df439cff6393b7920dda436909ab792923fc40fb1d949223a1b3179'
LOG='250a4365aaa14928a4cb312b212e11cae610f5d040f22295ab3f020a8007b796'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'FreeJOrdinaryRank.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.json','author.log','peer.log'))]:
        blob=subprocess.run(['git','show','95c7720e0a:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=json.loads((PKG/'evidence/terminal.json').read_bytes())
    need(obs['session_id']==46503 and obs['actual_wrapper_exit']==0 and obs['receipt_sha256']==RECEIPT,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_FREEJ_ORDINARY_RANK_INTERMEDIATE' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/FreeJOrdinaryRank.lean';obj=run/'FreeJOrdinaryRank.olean';seed=proj/'FreeJGraphAuxiliary.olean'
        need(sha(src)==sha(PKG/'FreeJOrdinaryRank.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'FreeJGraphAuxiliary.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==85 and links==parentfiles,'parent coverage')
        for name in links:
            q=proj/name;target=prior/name
            need(q.resolve()==target.resolve() and sha(q)==sha(target),'parent link '+name)
        bb=run/'lib/BusyBeaver';priorbb=PRIOR/side/'lib/BusyBeaver'
        bbfiles={p.relative_to(priorbb) for p in priorbb.rglob('*.olean')}
        need({p.relative_to(bb) for p in bb.rglob('*.olean')}==bbfiles,'BusyBeaver coverage')
        for name in bbfiles:
            q=bb/name;need(q.is_symlink() and q.resolve()==(priorbb/name).resolve() and sha(q)==sha(priorbb/name),'BusyBeaver link')
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(seed),str(proj/'ArithmeticPellIntegralSolution.olean')},'direct imports')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        log=PKG/'evidence'/(side+'.log')
        need(sha(log)==sha(run/'compiler.log')==row['log_sha256']==LOG and log.read_text()==row['stdout'],'logs')
        reports=re.findall(r"^'FreeJOrdinaryRank\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['graph_ordinary_rank'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound'] and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':85,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_ORDINARY_RANK_AUDIT','source_commit':'95c7720e0a',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':46503,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, exact rank equality, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
