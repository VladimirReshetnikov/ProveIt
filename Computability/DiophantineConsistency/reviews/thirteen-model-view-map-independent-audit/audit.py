#!/usr/bin/env python3
"""Audit both merged window/graph model-to-ring provider overlays."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-view-map'
OUT=Path('/tmp/ipra-thirteen-model-view-pair-01')
WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01')
DAG=Path('/tmp/ipra-thirteen69-dag-pair-01')
CUT=Path('/tmp/ipra-thirteen-graph-cut-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='4fa69061d11b4106a7d24dc70d8e655bc7426de673802c43bc42fa704a60d1e5'
SOURCE='ec0bd93b29f098008db3f501d77da258b3a9e6cd20a977516e740dc2f28b4479'
OBJECT='1ddd8d93d30eeee2a9abf667a0117f9cd5390dc2701209ac0bb1f7e4d7598fbf'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    for name in ('README.md','replay.py','Model69ViewMap.lean','failed-missing-model-import.lean','failed-separated-overlays.lean','replay-receipt.json','terminal-observation.json'):
        p=PKG/name;blob=subprocess.run(['git','show','5f9218062f:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session']==60952 and obs['actual_exit_code']==0 and obs['receipt_sha256']==RECEIPT and obs['stdout']=='PASS_PAIRED_THIRTEEN_MODEL_VIEW '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN_MODEL_VIEW' and len(r['runs'])==len(r['parent_audits'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    parents=[('thirteen-model-parent-window-pair-independent-audit','4a358f8fd09fa3be38d32aa2314ad063406ea2d363f74d1a13f41dedcc3e0ec9'),
             ('thirteen-model-graph-cut-independent-audit','b7feb6dd43d9edc42fdbc703fa99bcb14fcd9c011872ab9781d7d53f4388c404')]
    for (name,h),recorded in zip(parents,r['parent_audits']):
        d=BASE/'reviews'/name;need(sha(d/'CHECK.json')==h and recorded==json.loads((d/'CHECK.json').read_bytes()),'parent receipt '+name)
        p=subprocess.run([sys.executable,'-I','-S','-B',str(d/'audit.py')],capture_output=True,timeout=180)
        need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==recorded,'parent audit rerun '+name)
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;src=run/'src/Model69ViewMap.lean';obj=run/'Model69ViewMap.olean';merged=run/'lib';window=WINDOW/side/'lib';dag=DAG/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'child exits')
        need(sha(src)==sha(PKG/'Model69ViewMap.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        winfiles={p.relative_to(window) for p in window.rglob('*.olean')};mergedfiles={p.relative_to(merged) for p in merged.rglob('*.olean')}
        extra={Path('DiophantineConsistency')/x for x in ('ShortEquation.olean','ThirteenCarrier.olean','Thirteen69Nodes.olean','Thirteen69Cuts.olean')}
        need(mergedfiles==winfiles|extra and not (winfiles&extra),'merged project inventory')
        for rel in winfiles:
            q=merged/rel;p=window/rel;need(q.resolve()==p.resolve() and sha(q)==sha(p),'window overlay '+str(rel))
        dagnames={p.name for p in dag.glob('*.olean')};winnames={p.name for p in (window/'DiophantineConsistency').glob('*.olean')}
        matched=dagnames&winnames;added=dagnames-winnames
        need(len(matched)==64 and added=={x.name for x in extra} and set(row['matched_project_objects'])==matched and set(row['added_graph_objects'])==added,'overlap inventory')
        for name in matched:
            h=row['matched_project_objects'][name]
            need(sha(dag/name)==sha(window/'DiophantineConsistency'/name)==sha(merged/'DiophantineConsistency'/name)==h,'overlap '+name)
        for name in added:
            q=merged/'DiophantineConsistency'/name;need(q.is_symlink() and q.resolve()==(dag/name).resolve() and sha(q)==row['added_graph_objects'][name],'added '+name)
        deps={str(PACKAGE/'Init.olean'),str(CUT/side/'Model69GraphCut.olean'),str(merged/'DiophantineConsistency/ModelDifferenceRing.olean'),str(merged/'DiophantineConsistency/ArithmeticCarrierRadix2011.olean')}
        need(all(Path(x).is_file() for x in deps) and set(row['deps_stdout'].splitlines())==deps,'direct dependencies')
        reports=re.findall(r"^'Model69ViewMap\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['map_sub_of_le','map_rank','map_gap'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound']*3 and row['axiom_reports']==[a for _,a in reports] and
             not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'window_objects':len(winfiles),'matched_graph_objects':64,'added_graph_objects':4,'object_sha256':OBJECT,'recorded_compiler_exit':0,'recorded_deps_exit':0})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_MODEL_VIEW_AUDIT','source_commit':'5f9218062f',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':60952,'recorded_outer_exit':0,
      'parent_audit_rerun_exits':[0,0],'runs':summaries,
      'scope':'Read-only merged-provider artifact audit; no Lean rerun, complete axiom inventory, actual-zero bounds, full converse, calibration or iPRA proof.'},indent=2))
if __name__=='__main__':main()
