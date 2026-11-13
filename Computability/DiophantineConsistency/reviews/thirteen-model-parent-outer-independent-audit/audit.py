#!/usr/bin/env python3
"""Read-only paired conditional outer scalar composition artifact audit."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-parent-outer'
OUT=Path('/tmp/ipra-thirteen-parent-outer-pair-01')
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='5690d4452611aea1e96809c73c549bc46dbfde87ddcaa5decd6386b5b4edb8c9'
SOURCE='4b3e5589fb6df55741cb84599faa34e247d6cdd65c790b5ed2e7d935b19bd133'
OBJECT='58a724c9452e8c86b04c567956ddb4343ea1dcb9bbb67905bfe7881b2a5b5b64'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for name in ('README.md','replay.py','Model69Outer.lean','replay-receipt.json','terminal-observation.json'):
        p=PKG/name
        blob=subprocess.run(['git','show','35d1e2f8a3:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed source '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session_id']==72974 and obs['outer_exit_code']==0 and obs['receipt_sha256']==RECEIPT and
         obs['stdout']=='PASS_PAIRED_THIRTEEN_PARENT_OUTER '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN_PARENT_OUTER' and len(r['parent_audits'])==2 and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    parents=[('thirteen-model-parent-growth-independent-audit','09598aac3944f8d7bd2758954d1dea4cf1c9e9ccd3550f70b520d5a62a24a3b8'),
             ('thirteen-model-parent-transport-independent-audit','501224b4a459e8569b63f32d9a2ed5bf3d7a2fbd733003ad0e27f461528c5edc')]
    for name,h in parents:
        d=BASE/'reviews'/name
        need(sha(d/'CHECK.json')==h,'parent audit pin')
        p=subprocess.run([sys.executable,'-I','-S','-B',str(d/'audit.py')],capture_output=True,timeout=180)
        need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==json.loads((d/'CHECK.json').read_bytes()),'parent rerun '+name)
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;prior=PAIR/side/'child-output';src=run/'src/Model69Outer.lean';obj=run/'Model69Outer.olean'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'child exits')
        need(sha(src)==sha(PKG/'Model69Outer.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        dep=prior/'lib/DiophantineConsistency/ArithmeticPellFirstIndex.olean'
        growth=Path('/tmp/ipra-thirteen-parent-growth-replay-01')/side/'Model69Growth.olean'
        transport=Path('/tmp/ipra-thirteen-parent-transport-replay-01')/side/'Model69Transport.olean'
        need(set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(dep),str(growth),str(transport)},'direct imports')
        state=json.loads((prior/'state.json').read_bytes())
        parent=next(x for x in state['records'] if x['module']=='DiophantineConsistency.ArithmeticPellFirstIndex')
        need(sha(dep)==parent['object_sha256'] and sha(growth)=='7f062fb1680bbcb16fac40d101ad8ba0c6751327e32f94884c82a7d27aa4587f' and sha(transport)=='7c614f9ed3796b2717ed37c6babc946530fd41a0d9fdea572fd6eacff9177b8f','parent objects')
        need(row['stdout']=="'Model69Outer.outer_of_scalar_data' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and
             row['axiom_reports']==['propext, Classical.choice, Quot.sound'] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'report')
        summaries.append({'side':side,'recorded_compiler_exit':0,'recorded_deps_exit':0,'object_sha256':OBJECT,'direct_parent_sha256':sha(dep),'growth_sha256':sha(growth),'transport_sha256':sha(transport)})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_PARENT_OUTER_AUDIT','source_commit':'35d1e2f8a3',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':72974,'recorded_outer_exit':0,
      'independent_parent_rerun_exits':[0,0],'runs':summaries,
      'scope':'Read-only paired artifact audit ; no Lean rerun, actual-zero extraction, rank phase, model converse, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
