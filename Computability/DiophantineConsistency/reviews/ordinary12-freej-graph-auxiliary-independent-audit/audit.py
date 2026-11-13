#!/usr/bin/env python3
"""Read-only paired graph positive auxiliary audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-graph-auxiliary-prototype'
PARENT=BASE/'reviews/ordinary12-freej-graph-strong-independent-audit'
OUT=Path('/tmp/ipra-freej-graph-auxiliary-pair-01')
PRIOR=Path('/tmp/ipra-freej-graph-strong-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='db0dce9fb7f47c6d52c18789d717d126b175df14611d05cf9719cb17b85af5f6'
AUDIT='222f28c5b4f159f19708c7bf3d3239f9a03fb742e421c76495d1a4198166fb93'
SOURCE='b35d86b03c6df60384d0d1ee2459fb96918ae4fe264106dc101030366bc8d3ee'
SEED='199912ed40dfca20fc484a4b99590d342d326a19a46c1ef904e5fd4f969d8006'
OBJECT='abe39b30a9ab0d68cdd666957a91f1f06b11edeae7055ca220f9d37182ccfff7'
LOG='36fd6153be3dcbc1c324e0fab6cd161514b8032f5cb83f1cbc023278dc8d77d5'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'FreeJGraphAuxiliary.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.json','author.log','peer.log')),
      *(PKG/'observations'/x for x in ('attempt01-terminal.json','attempt01.lean','replay-attempt01-terminal.json','replay-attempt01.py'))]:
        blob=subprocess.run(['git','show','ccf54c0b30:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=json.loads((PKG/'evidence/terminal.json').read_bytes())
    need(obs['session_id']==53593 and obs['actual_wrapper_exit']==0 and obs['receipt_sha256']==RECEIPT,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_FREEJ_GRAPH_POSITIVE_AUXILIARY' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/FreeJGraphAuxiliary.lean';obj=run/'FreeJGraphAuxiliary.olean';seed=proj/'FreeJGraphStrong.olean'
        need(sha(src)==sha(PKG/'FreeJGraphAuxiliary.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'FreeJGraphStrong.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==84 and links==parentfiles,'parent coverage')
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
        reports=re.findall(r"^'FreeJGraphAuxiliary\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['graph_positive_auxiliary'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound'] and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':84,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_GRAPH_AUXILIARY_AUDIT','source_commit':'ccf54c0b30',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':53593,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, rank recovery, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
