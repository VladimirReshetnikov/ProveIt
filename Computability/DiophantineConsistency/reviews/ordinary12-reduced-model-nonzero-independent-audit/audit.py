#!/usr/bin/env python3
"""Read-only paired nonzero-measure audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/reduced-model-nonzero-prototype'
PARENT=BASE/'reviews/ordinary12-reduced-model-descent-independent-audit'
OUT=Path('/tmp/ipra-reduced-model-nonzero-pair-01')
PRIOR=Path('/tmp/ipra-reduced-model-descent-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='01af03ae511a9a94c65fb60d1d2a634dc1b502e18bcd6a9584296bdb2d14bedb'
AUDIT='1770548da56fea9cf429d1d218eb71395f8352474bc5371e7d317e87c607089b'
SOURCE='e54bb769e2417db708e06d1c352bae565d8746fd77ed25c6d3dc7575ca94ee00'
SEED='1a7e42a08cc3ae1de1d9162ef2af94855b7cc86ebe8c98551fb384883f0a8a9b'
OBJECT='29137245243c5b38a7213cc6c00a5db877a80a39373833bb03bd973d59e82482'
LOG='4a22e5bbffcbc3efb94a8fc01d23f63c6fe52cdc3074e8b55a4d413796544342'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'ReducedNormNext.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.json','author.log','peer.log')),
      *(PKG/'observations'/x for x in ('attempt01-terminal.json','attempt01.lean','attempt02-terminal.json','attempt02.lean'))]:
        blob=subprocess.run(['git','show','691db2bc02:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=json.loads((PKG/'evidence/terminal.json').read_bytes())
    need(obs['session_id']==88085 and obs['actual_wrapper_exit']==0 and obs['receipt_sha256']==RECEIPT,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_REDUCED_MODEL_NONZERO_MEASURE' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/ReducedNormNext.lean';obj=run/'ReducedNormNext.olean';seed=proj/'ReducedNormBounds.olean'
        need(sha(src)==sha(PKG/'ReducedNormNext.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'ReducedNormBounds.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==65 and links==parentfiles,'parent coverage')
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
        reports=re.findall(r"^'ReducedNormNext\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['ring_transform_v_ne_zero','model_smaller_first'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound']*2 and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':65,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_REDUCED_MODEL_NONZERO_AUDIT','source_commit':'691db2bc02',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':88085,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, simultaneous new state, iteration, graph bridge or iPRA proof.'},indent=2))

if __name__=='__main__':main()
