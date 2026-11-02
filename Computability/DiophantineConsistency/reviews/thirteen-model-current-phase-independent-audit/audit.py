#!/usr/bin/env python3
"""Read-only paired actual 2011 positive-zero rank phase artifact audit."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-current-phase'
OUT=Path('/tmp/ipra-thirteen-current-phase-pair-01')
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='7e034466442c0a20b76af839e055e8da68c357f393ab52e644af6b60cbec1749'
SOURCE='b9d32d43c44209f9fb29893d48c37094d81e9b8bdeaeb806daef05e5a3e227be'
OBJECT='cae68faf5da024029d51ed8c970124f0f7b80a44e0943bc703d95d2b32dff6d4'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for name in ('README.md','replay.py','Model69CurrentPhase.lean','replay-receipt.json','terminal-observation.json'):
        p=PKG/name
        blob=subprocess.run(['git','show','1e1db672d2:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed source '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session']==11439 and obs['actual_exit_code']==0 and obs['receipt_sha256']==RECEIPT and
         obs['stdout']=='PASS_PAIRED_THIRTEEN_CURRENT_PHASE '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN_CURRENT_PHASE' and len(r['parent_audits'])==2 and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    parents=[('thirteen-model-parent-window-pair-independent-audit','4a358f8fd09fa3be38d32aa2314ad063406ea2d363f74d1a13f41dedcc3e0ec9'),
             ('thirteen-model-parent-phase-independent-audit','2e5692be17c5d7ff16d07706fab9408d3150d72ab7820a518fc89fba01c1e7ea')]
    for name,h in parents:
        d=BASE/'reviews'/name
        need(sha(d/'CHECK.json')==h,'parent audit pin')
        p=subprocess.run([sys.executable,'-I','-S','-B',str(d/'audit.py')],capture_output=True,timeout=180)
        need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((d/'CHECK.json').read_bytes()),'parent rerun '+name)
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;prior=PAIR/side/'child-output';src=run/'src/Model69CurrentPhase.lean';obj=run/'Model69CurrentPhase.olean'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'child exits')
        need(sha(src)==sha(PKG/'Model69CurrentPhase.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        lib=Path('/tmp/ipra-thirteen-parent-window-pair-01')/side/'lib/DiophantineConsistency'
        zero=lib/'ArithmeticWindowZero.olean';rank=lib/'ArithmeticRankForcing2011.olean'
        phase=Path('/tmp/ipra-thirteen-parent-phase-replay-01')/side/'Model69Phase.olean'
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(zero),str(rank),str(phase)},'direct imports')
        parent_receipt=json.loads((BASE/'research/thirteen-model-parent-window/replay-receipt.json').read_bytes())
        for obj,name,h in ((zero,'ArithmeticWindowZero','7fa1bc696a3bd60733f4382aee821fd16449a8d158ef821a8213497bf8692228'),
                           (rank,'ArithmeticRankForcing2011','69f900908a859c01c8ff2368904812f9e07b1b9aea516ae1718041af7fd84ceb')):
            parent=next(x for x in parent_receipt['runs'] if x['label']==side and x['module']=='DiophantineConsistency.'+name)
            need(sha(obj)==parent['object_sha256']==h,'window parent object '+name)
        need(sha(phase)=='a1172a5b308cd2da9eef9cca5ae9dd33eefefd4a5cae22af8cc281e52f43f5c6','conditional phase object')
        need(row['stdout']=="'Model69CurrentPhase.current_rank_phase' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and
             row['axiom_reports']==['propext, Classical.choice, Quot.sound'] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'report')
        summaries.append({'side':side,'recorded_compiler_exit':0,'recorded_deps_exit':0,'object_sha256':OBJECT,'window_zero_sha256':sha(zero),'rank_forcing_sha256':sha(rank),'conditional_phase_sha256':sha(phase)})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_CURRENT_PHASE_AUDIT','source_commit':'1e1db672d2',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':11439,'recorded_outer_exit':0,
      'independent_parent_rerun_exits':[0,0],'runs':summaries,
      'scope':'Read-only paired artifact audit ; no Lean rerun, model converse, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
