#!/usr/bin/env python3
"""Read-only paired reduced denominator induction audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/reduced-model-induction-prototype'
PARENT=BASE/'reviews/ordinary12-reduced-model-state-independent-audit'
OUT=Path('/tmp/ipra-reduced-model-induction-pair-01')
PRIOR=Path('/tmp/ipra-reduced-model-state-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='298e528a7c814b129ff41e4551f5b18768d52c500bfff86322f430ad4af82199'
AUDIT='28444ab851b01f053ab64e4f917728fcf51a01aaa7b50dcd2cf43dc5de655ef3'
SOURCE='d1190a9e8bfb44341c99b07c3e33ce463d63866ced5f22a042920c3fedaedcae'
SEED='4a2201c3246f1506a6ba0e8c51138e49e266e9428c3c40636eae16b1bb6fd774'
OBJECT='d7e50376225d34ca5b5356af28e14ffb5061b245165c89e35f51f654e25df6a1'
LOG='a28bc0601b7237885401f617277d00e1cf4975477931aa36ea356cbb85f25fae'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'ReducedNormInduction.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.json','author.log','peer.log')),
      *(PKG/'observations'/x for x in ('attempt01-terminal.json','attempt01.lean'))]:
        blob=subprocess.run(['git','show','dd11641315:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=json.loads((PKG/'evidence/terminal.json').read_bytes())
    need(obs['session_id']==54640 and obs['actual_wrapper_exit']==0 and obs['receipt_sha256']==RECEIPT,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_REDUCED_MODEL_INTEGRAL_DENOMINATOR' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/ReducedNormInduction.lean';obj=run/'ReducedNormInduction.olean';seed=proj/'ReducedNormState.olean'
        need(sha(src)==sha(PKG/'ReducedNormInduction.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'ReducedNormState.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==67 and links==parentfiles,'parent coverage')
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
        reports=re.findall(r"^'ReducedNormInduction\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['zero_impossible','unit_index_denominator','reduced_denominator_one'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound']*3 and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':67,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_REDUCED_MODEL_INDUCTION_AUDIT','source_commit':'dd11641315',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':54640,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, arbitrary signed-fraction normalization, graph bridge or iPRA proof.'},indent=2))

if __name__=='__main__':main()
