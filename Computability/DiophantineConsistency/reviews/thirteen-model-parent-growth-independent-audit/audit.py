#!/usr/bin/env python3
"""Read-only paired conditional growth artifact audit."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-parent-growth'
OUT=Path('/tmp/ipra-thirteen-parent-growth-replay-01')
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='5276d8d1ee367ce6ea079a710cfe6873dcfa4ff587be1a838a460acdc0237660'
SOURCE='740fe98c2e72b4b88af2d9d2f96d08c0f41c2d40f417124b3782620ec8c473d9'
OBJECT='7f062fb1680bbcb16fac40d101ad8ba0c6751327e32f94884c82a7d27aa4587f'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for name in ('README.md','replay.py','Model69Growth.lean','replay-receipt.json','terminal-observation.json'):
        p=PKG/name
        blob=subprocess.run(['git','show','f448bc311b:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed source '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session_id']==55261 and obs['outer_exit_code']==0 and obs['receipt_sha256']==RECEIPT and
         obs['stdout']=='PASS_PAIRED_THIRTEEN_PARENT_GROWTH '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN_PARENT_GROWTH' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    comparator=BASE/'research/fresh-project-closure/compare.py'
    p=subprocess.run([sys.executable,'-I','-S',str(comparator),str(PAIR/'author/child-output/state.json'),str(PAIR/'peer/child-output/state.json')],capture_output=True,timeout=120)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==r['parent_comparison'],'parent comparator')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;prior=PAIR/side/'child-output';src=run/'src/Model69Growth.lean';obj=run/'Model69Growth.olean'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'child exits')
        need(sha(src)==sha(PKG/'Model69Growth.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        deps={str(PACKAGE/'Init.olean'),str(PACKAGE/'Foundation/FirstOrder/Arithmetic/Exponential/Log.olean'),str(PACKAGE/'Mathlib/Tactic/Ring.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct package imports')
        reports=re.findall(r"^'Model69Growth\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['double_le_rank','radix_le_multiplier_of_population'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound']*2 and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'recorded_compiler_exit':0,'recorded_deps_exit':0,'object_sha256':OBJECT})
    samples=0
    for u in range(10):
     for R in range(3*u+2,3*u+12):
      count=3*u+2;q=1<<u;w=1<<(R-u)
      need(count<=R and w*q==1<<R and q<=w,'finite growth');samples+=1
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_PARENT_GROWTH_AUDIT','source_commit':'f448bc311b',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':55261,'recorded_outer_exit':0,
      'parent_comparator_rerun_exit':0,'finite_valid_states':samples,'runs':summaries,
      'scope':'Read-only paired artifact audit and finite sanity check; no Lean rerun, actual-zero population extraction, rank phase, model converse, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
