#!/usr/bin/env python3
"""Read-only paired signed model integrality audit over independently audited parents."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/reduced-model-signed-prototype'
PARENT=BASE/'reviews/ordinary12-reduced-model-normalization-independent-audit'
OUT=Path('/tmp/ipra-reduced-model-signed-pair-01')
PRIOR=Path('/tmp/ipra-reduced-model-normalization-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='576041dbd94d2aaa76a63ab4515164e6b783d106f9d92a3891c260c88eb8b30a'
AUDIT='1360057b0ae7d567e9462094dcfec04937d663a47a3cf3b2c15e9bc5bff20346'
SOURCE='df5f982306cfa877484581a7e80103d1467f7d32d4905b3a9e9cbcf6689df10f'
SEED='9247dd40a71d6ca1c7be0c90e905f175537b16ad3dc3c4b484a93b8d9a627771'
OBJECT='e6038c81aa28be30bf0d9709d1b46067c1828b51a37c214c9fe16c2ebd92cef3'
LOG='ebcb22853e01ad8839e17acbc330c8b175dc5abfd4cc12fd7ea2779ec26408c0'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for p in [PKG/'replay.py',PKG/'ReducedNormSigned.lean',
      *(PKG/'evidence'/x for x in ('receipt.json','terminal.json','author.log','peer.log')),
      *(PKG/'observations'/x for x in ('attempt01-terminal.json','attempt01.lean'))]:
        blob=subprocess.run(['git','show','4fd9069119:'+str(p.relative_to(ROOT))],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+str(p))
    obs=json.loads((PKG/'evidence/terminal.json').read_bytes())
    need(obs['session_id']==62334 and obs['actual_wrapper_exit']==0 and obs['receipt_sha256']==RECEIPT,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_REDUCED_MODEL_SIGNED_INTEGRALITY' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['pins'].items():need(sha(path)==h,'pin '+path)
    need(sha(PARENT/'CHECK.json')==AUDIT,'parent audit pin')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;proj=run/'lib/DiophantineConsistency';prior=PRIOR/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'exits')
        src=run/'src/DiophantineConsistency/ReducedNormSigned.lean';obj=run/'ReducedNormSigned.olean';seed=proj/'ReducedNormNormalization.olean'
        need(sha(src)==sha(PKG/'ReducedNormSigned.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT and not seed.is_symlink() and sha(seed)==sha(PRIOR/side/'ReducedNormNormalization.olean')==row['seed_sha256']==SEED,'object and seed')
        parentfiles={p.name for p in prior.glob('*.olean')};links={p.name for p in proj.glob('*.olean') if p.is_symlink()}
        need(len(links)==69 and links==parentfiles,'parent coverage')
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
        reports=re.findall(r"^'ReducedNormSigned\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['natural_magnitude_square','signed_denominator_divides'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound']*2 and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'parent_links':69,'seed_sha256':SEED,'object_sha256':OBJECT,
          'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_REDUCED_MODEL_SIGNED_AUDIT','source_commit':'4fd9069119',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':62334,'recorded_outer_exit':0,
      'parent_audit_receipt_sha256':AUDIT,'parent_audit_rerun_exit':0,'runs':summaries,
      'scope':'Read-only paired suffix audit; no Lean rerun, graph bridge or iPRA proof.'},indent=2))

if __name__=='__main__':main()
