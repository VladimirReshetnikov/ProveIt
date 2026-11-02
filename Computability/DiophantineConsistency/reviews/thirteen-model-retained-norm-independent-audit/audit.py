#!/usr/bin/env python3
"""Read-only audit of the actual-zero retained-norm paired suffix."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-retained-norm'
OUT=Path('/tmp/ipra-thirteen-retained-norm-pair-01')
PARENT=Path('/tmp/ipra-thirteen-model-view-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDIT=BASE/'reviews/thirteen-model-view-map-independent-audit'
RECEIPT='a23e98dabd32e7a92086dabc035364c7e544ef150fcffed174e84bb9212d70fc'
SOURCE='dc0fc6b25fdbbab4c47fc560538c40795dd3cfa5c44a5ed6e8e05afe0bcd88ca'
OBJECT='c79d697bd7ee6305c272b6ae66ab73eed751a1f25df241dca2570bdc3b529370'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    names=('README.md','Model69RetainedNorm.lean','Model69RetainedNormBase.lean','failed-xy-normalization.lean','failed-current-rank-vector.lean','failed-broad-simp-memory.lean','failed-vector-composition.lean','failed-vector-change-memory.lean','replay.py','replay-receipt.json','terminal-observation.json')
    for name in names:
        p=PKG/name
        b=subprocess.run(['git','show','59ffdf8411:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session']==87211 and obs['actual_exit_code']==0 and obs['receipt_sha256']==RECEIPT and obs['stdout']=='PASS_PAIRED_THIRTEEN_RETAINED_NORM '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN_RETAINED_NORM' and len(r['runs'])==2 and len(r['parent_audits'])==1,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    need(sha(AUDIT/'CHECK.json')=='4b90ba8d095ba9e0a22343b5a32163e59ada61a34db348102f4e622dbd1aedad','parent receipt hash')
    parent=json.loads((AUDIT/'CHECK.json').read_bytes())
    need(r['parent_audits']==[parent],'recorded parent receipt')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==parent,'parent audit rerun')
    summaries=[]
    reports=['first_norm','main_norm','current_bounds_for_map','current_norms','view_rank','current_view_rank','view_P_formula','view_Q_formula','current_graph_norms']
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;src=run/'src/Model69RetainedNorm.lean';obj=run/'Model69RetainedNorm.olean'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'recorded exits')
        need(sha(src)==sha(PKG/'Model69RetainedNorm.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source and object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        deps={str(PACKAGE/'Init.olean'),str(PARENT/side/'Model69ViewMap.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(q).is_file() for q in deps),'direct deps')
        found=re.findall(r"^'Model69RetainedNorm\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in found]==reports and [a for _,a in found]==['propext, Classical.choice, Quot.sound']*9 and row['axiom_reports']==[a for _,a in found] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'object_sha256':OBJECT,'recorded_compiler_exit':0,'recorded_deps_exit':0,'axiom_reports':len(found)})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_RETAINED_NORM_AUDIT','source_commit':'59ffdf8411','author_receipt_sha256':RECEIPT,'recorded_outer_session':87211,'recorded_outer_exit':0,'parent_audit_rerun_exit':p.returncode,'runs':summaries,'scope':'Read-only audit; the three rank-relevant port equalities are hypotheses, slot 1 is unrestricted; no full graph converse, fixed-tuple binding, complete provider axiom inventory or iPRA claim.'},indent=2))
if __name__=='__main__':main()
