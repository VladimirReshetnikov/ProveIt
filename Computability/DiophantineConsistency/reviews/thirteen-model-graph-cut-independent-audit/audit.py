#!/usr/bin/env python3
"""Read-only audit with independent recreation of the historical row audit."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-graph-draft'
AUDIT=BASE/'reviews/thirteen69-dag-binding-independent-audit'
OUT=Path('/tmp/ipra-thirteen-graph-cut-pair-01')
PROVIDER=Path('/tmp/ipra-thirteen69-dag-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT=''
SOURCE='9091ab7612135d586e7518a1b61aa9c03d19fed91e961b47834df781b9d92941'
OBJECT='d7ef13fe85818b66499dec9cf10489bed3176f455c0232339bc47853f7c9a33d'
AUDITH='26a42d561a232e2a49dae61f3a1f6f4cd882e3d38b6616aa62ed2ffcb0c081e5'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(args,cwd=None):return subprocess.run(args,cwd=cwd,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)

def main():
    files=('README.md','actual-zero-join-plan.md','replay.py','failed-current-audit-replay.py','failed-missing-tactic.lean','Model69GraphCut.lean','replay-receipt.json','terminal-observation.json')
    for name in files:
        p=PKG/name;blob=run(['git','show','c92dffb5f2:'+p.relative_to(ROOT).as_posix()],ROOT).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes());digest=sha(PKG/'replay-receipt.json')
    need(obs['session']==58887 and obs['actual_exit_code']==0 and obs['receipt_sha256']==digest and
         obs['stdout']=='PASS_PAIRED_THIRTEEN_GRAPH_CUT '+digest and sha(OUT/'receipt.json')==digest,'wrapper observation')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN_GRAPH_CUT' and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    need(sha(AUDIT/'CHECK.json')==AUDITH and r['parent_audit']==json.loads((AUDIT/'CHECK.json').read_bytes()),'parent audit receipt')
    current=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=180)
    need(current.returncode!=0 and b'committed bytes' in current.stderr and b'README.md' in current.stderr,'current parent guard result')
    # Recreate the audited repository state independently, without changing the
    # live worktree, and run the exact audited script against retained objects.
    patterns=('/Computability/DiophantineConsistency/research/thirteen69-dag-binding/',
      '/Computability/DiophantineConsistency/research/thirteen-variable-independent/polynomial69.json',
      '/Computability/DiophantineConsistency/research/fresh-project-closure/compare.py',
      '/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ShortEquation.lean',
      '/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenCarrier.lean',
      '/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentMaskData2011.lean',
      '/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentKernelData2011.lean',
      '/Computability/DiophantineConsistency/candidates/one-page-phase-split-carrier65-2471/coefficients/beta.bin.gz')
    with tempfile.TemporaryDirectory(prefix='independent-graph-cut-historical-') as t:
        clone=Path(t)/'repo'
        run(['git','clone','--shared','--no-checkout',str(ROOT),str(clone)])
        run(['git','sparse-checkout','init','--no-cone'],clone)
        run(['git','sparse-checkout','set',*patterns],clone)
        run(['git','checkout','--detach','047484be73'],clone)
        child=clone/'Computability/DiophantineConsistency/reviews/thirteen69-dag-binding-independent-audit'
        child.mkdir(parents=True);shutil.copyfile(AUDIT/'audit.py',child/'audit.py')
        need(sha(child/'audit.py')==sha(AUDIT/'audit.py'),'unchanged historical audit code')
        p=run([sys.executable,'-I','-S','-B',str(child/'audit.py')],clone)
        need(not p.stderr and json.loads(p.stdout)==json.loads((AUDIT/'CHECK.json').read_bytes()),'historical parent rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        runpath=OUT/side;src=runpath/'src/Model69GraphCut.lean';obj=runpath/'Model69GraphCut.olean'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'child exits')
        need(sha(src)==sha(PKG/'Model69GraphCut.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        dep=PROVIDER/side/'lib/DiophantineConsistency/ThirteenCarrier.olean'
        need(sha(dep)=='54da7156e0795e6c91b225c12bd2f0965a3cad69752e6f0fa8eeb52337c2733e' and
             set(row['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(dep),str(PACKAGE/'Mathlib/Tactic/LinearCombination.olean')},'direct imports')
        need(row['stdout']=="'Model69GraphCutDraft.replace_zero69' depends on axioms: [propext, Quot.sound]\n" and
             row['axiom_reports']==['propext, Quot.sound'] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'report')
        summaries.append({'side':side,'recorded_compiler_exit':0,'recorded_deps_exit':0,'object_sha256':OBJECT,'carrier_sha256':sha(dep)})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_GRAPH_CUT_AUDIT','source_commit':'c92dffb5f2',
      'author_receipt_sha256':digest,'recorded_outer_session':58887,'recorded_outer_exit':0,'current_parent_audit_exit':current.returncode,
      'current_parent_guard_reason':'updated README differs from exact audited historical bytes',
      'unchanged_historical_parent_audit_exit':0,'parent_audit_sha256':AUDITH,'runs':summaries,
      'scope':'Read-only conditional ring-cut audit; no Lean rerun, actual-zero provider join, model converse, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
