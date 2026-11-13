#!/usr/bin/env python3
"""Read-only paired graph positive strong-norm audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-graph-strong-prototype'
PARENT=BASE/'reviews/ordinary12-freej-graph-integrality-independent-audit'
OUT=Path('/tmp/ipra-freej-graph-strong-pair-01')
PRIOR=Path('/tmp/ipra-freej-graph-integrality-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='59d42977f9c3d3969c4d115d83a2ec33fa24aba55cad87ca6dae780995f8ab58'
AUDIT='f52064c6cd1fca7221f33c6a3720e667cd9da407d8419cee2a1953096fe104f4'
SOURCE='5e8dd0b50d47864f8b786f1c77f5c9373dcc3f4e71f832e4809c56472a71e346'
SEED='826781b0eec49929248439fc8b5fd71c9d788b99b21bd1fbcd5c21ab2c865a39'
OBJECT='199912ed40dfca20fc484a4b99590d342d326a19a46c1ef904e5fd4f969d8006'
LOG='c6118d5d01a5412980c7d8a28fe4ec8c6b05ab25abda802d7bf7de5b3b6df922'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'FreeJGraphStrong.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.json','author.log','peer.log')),
      *(PKG/'observations'/x for x in ('attempt01-terminal.json','attempt01.lean','attempt02-terminal.json','attempt02.lean','attempt03-terminal.json','attempt03.lean'))]:
        blob=subprocess.run(['git','show','722f45617f:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=json.loads((PKG/'evidence/terminal.json').read_bytes())
    need(obs['session_id']==72917 and obs['actual_wrapper_exit']==0 and obs['receipt_sha256']==RECEIPT,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_FREEJ_GRAPH_POSITIVE_STRONG' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/FreeJGraphStrong.lean';obj=run/'FreeJGraphStrong.olean';seed=proj/'FreeJGraphIntegrality.olean'
        need(sha(src)==sha(PKG/'FreeJGraphStrong.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'FreeJGraphIntegrality.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==83 and links==parentfiles,'parent coverage')
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
        reports=re.findall(r"^'FreeJGraphStrong\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['graph_signed_multiplier','graph_positive_strong'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound']*2 and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':83,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_GRAPH_STRONG_AUDIT','source_commit':'722f45617f',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':72917,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, auxiliary-positive witness, rank recovery, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
