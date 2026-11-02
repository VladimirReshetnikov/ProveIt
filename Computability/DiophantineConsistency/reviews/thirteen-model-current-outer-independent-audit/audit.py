#!/usr/bin/env python3
"""Read-only paired actual 2011 positive-zero outer data artifact audit."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-current-outer'
OUT=Path('/tmp/ipra-thirteen-current-outer-pair-01')
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='4fdcf2e09603016712d10a8f22f50de58d0c32ac8d87b4867910a01b73ef0d8c'
SOURCE='c390faa06b821e5e0c3b8b96bf898fbf3ac8230bb0dc0e04cc6b2520cf566441'
OBJECT='a9de729634c8ef2beaf23f669fe4c72c3de4f97905ef2f1c810e975a68e98957'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for name in ('README.md','replay.py','Model69CurrentOuter.lean','replay-receipt.json','terminal-observation.json'):
        p=PKG/name
        blob=subprocess.run(['git','show','b23c9f7b72:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed source '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session_id']==24583 and obs['outer_exit_code']==0 and obs['receipt_sha256']==RECEIPT and
         obs['stdout']=='PASS_PAIRED_THIRTEEN_CURRENT_OUTER '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN_CURRENT_OUTER' and len(r['parent_audits'])==2 and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    parents=[('thirteen-model-parent-prefix-pair-independent-audit','dcca147c2f1aea76821ae7089da6dc1ceb1096dbdbbb33429d7c50ce40a1945d'),
             ('thirteen-model-parent-outer-independent-audit','f5dc903d2fe78878ca53468acbb9a5a4466c7420624fbe68f7ea983e8eaeedfa')]
    for name,h in parents:
        d=BASE/'reviews'/name
        need(sha(d/'CHECK.json')==h,'parent audit pin')
        p=subprocess.run([sys.executable,'-I','-S','-B',str(d/'audit.py')],capture_output=True,timeout=180)
        need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((d/'CHECK.json').read_bytes()),'parent rerun '+name)
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;prior=PAIR/side/'child-output';src=run/'src/Model69CurrentOuter.lean';obj=run/'Model69CurrentOuter.olean'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'child exits')
        need(sha(src)==sha(PKG/'Model69CurrentOuter.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        prefix=Path('/tmp/ipra-thirteen-parent-prefix-pair-01')/side/'lib/DiophantineConsistency/ArithmeticHalfBinomial2011.olean'
        outer=Path('/tmp/ipra-thirteen-parent-outer-pair-01')/side/'Model69Outer.olean'
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(prefix),str(outer)},'direct imports')
        prefix_receipt=json.loads((BASE/'research/thirteen-model-parent-prefix/pair-receipt.json').read_bytes())
        parent=next(x for x in prefix_receipt['runs'] if x['label']==side and x['module']=='DiophantineConsistency.ArithmeticHalfBinomial2011')
        need(sha(prefix)==parent['object_sha256']=='5409bff1e1ea08ddd5d678e879a2ba463504573dec30df9a02d97728313cbfbb' and
             sha(outer)=='58a724c9452e8c86b04c567956ddb4343ea1dcb9bbb67905bfe7881b2a5b5b64','direct parent objects')
        need(row['stdout']=="'Model69CurrentOuter.current_outer' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and
             row['axiom_reports']==['propext, Classical.choice, Quot.sound'] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'report')
        summaries.append({'side':side,'recorded_compiler_exit':0,'recorded_deps_exit':0,'object_sha256':OBJECT,'prefix_sha256':sha(prefix),'outer_sha256':sha(outer)})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_CURRENT_OUTER_AUDIT','source_commit':'b23c9f7b72',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':24583,'recorded_outer_exit':0,
      'independent_parent_rerun_exits':[0,0],'runs':summaries,
      'scope':'Read-only paired artifact audit ; no Lean rerun, rank phase, model converse, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
