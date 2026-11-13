#!/usr/bin/env python3
"""Read-only paired conditional rank phase artifact audit."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-parent-phase'
OUT=Path('/tmp/ipra-thirteen-parent-phase-replay-01')
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='27d4b04962f44768e70fcb4bd2faa74935e0044eb2965776c016c4b79b6d6d9f'
SOURCE='e0460dc67b4707e0bdf05df11a18a0abb23a786b1c0f918f874b76dd2abd8af4'
OBJECT='a1172a5b308cd2da9eef9cca5ae9dd33eefefd4a5cae22af8cc281e52f43f5c6'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    for name in ('README.md','replay.py','Model69Phase.lean','replay-receipt.json','terminal-observation.json'):
        p=PKG/name
        blob=subprocess.run(['git','show','d6105f61f0:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed source '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session_id']==74044 and obs['outer_exit_code']==0 and obs['receipt_sha256']==RECEIPT and
         obs['stdout']=='PASS_PAIRED_THIRTEEN_PARENT_PHASE '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN_PARENT_PHASE' and r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    comparator=BASE/'research/fresh-project-closure/compare.py'
    p=subprocess.run([sys.executable,'-I','-S',str(comparator),str(PAIR/'author/child-output/state.json'),str(PAIR/'peer/child-output/state.json')],capture_output=True,timeout=120)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==r['parent_comparison'],'parent comparator')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;prior=PAIR/side/'child-output';src=run/'src/Model69Phase.lean';obj=run/'Model69Phase.olean'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'child exits')
        need(sha(src)==sha(PKG/'Model69Phase.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        deps={str(PACKAGE/'Init.olean'),str(PACKAGE/'Foundation/FirstOrder/Arithmetic/Exponential/Log.olean'),str(PACKAGE/'Mathlib/Tactic/Ring.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct package imports')
        reports=re.findall(r"^'Model69Phase\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['pred_mod_four','rank_mod_four','rank_from_origin'] and
             [a for _,a in reports]==['propext, Classical.choice, Quot.sound']*3 and
             row['axiom_reports']==[a for _,a in reports] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'recorded_compiler_exit':0,'recorded_deps_exit':0,'object_sha256':OBJECT})
    samples=0
    for n in range(6):
     modulus=4*n
     for C in range(40):
      origin=C%modulus if modulus else C
      if origin!=1:continue
      need((C-1)%4==0,'predecessor residue')
      for q in range(0,13,4):
       for M in (3,7,11):
        for D,E,H in ((0,0,0),(1,2,3),(3,1,2)):
         R=(C-1)+M+q*D+q*q*E+q*q*q*H
         need(R%4==3,'rank residue');samples+=1
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_PARENT_PHASE_AUDIT','source_commit':'d6105f61f0',
      'author_receipt_sha256':RECEIPT,'recorded_outer_session':74044,'recorded_outer_exit':0,
      'parent_comparator_rerun_exit':0,'finite_valid_states':samples,'runs':summaries,
      'scope':'Read-only paired artifact audit and finite sanity check; no Lean rerun, actual-zero digit and block extraction, model converse, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
