#!/usr/bin/env python3
"""Read-only audit of exact-port specialization over the matched 69 parent."""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-exact-port'
OUT=Path('/tmp/ipra-thirteen-exact-port-pair-01')
PARENT=Path('/tmp/ipra-thirteen-fresh-graph-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDIT=BASE/'reviews/thirteen-model-fresh-graph-independent-audit'
RECEIPT='4dcbfb107e772876f239a6423c6f6dc3df228d79ca9a545a73a2db4ac265309a'
SOURCE='0b7db7e4d5d33435b76832dfca3ff2187187a024abce17960dd059a626e187a9'
OBJECT='248d8e3bfb7a62f9e2fe58281276506de6af4bb7ca6a78eba3b8c798fccd25a3'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    for name in ('README.md','Model69ExactPort.lean','failed-ambiguous-zero.lean','replay.py','replay-receipt.json','terminal-observation.json'):
        p=PKG/name;b=subprocess.run(['git','show','a832e29cec:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session']==57130 and obs['actual_exit_code']==0 and obs['receipt_sha256']==RECEIPT and obs['stdout']=='PASS_PAIRED_THIRTEEN_EXACT_PORT '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes());need(r['status']=='PASS_PAIRED_THIRTEEN_EXACT_PORT' and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    need(sha(AUDIT/'CHECK.json')=='c8c5dff42f52db59d847fb9105fb207ceb9700a4f108d1dd2e8e1010a1d5777e','parent receipt hash')
    parent=json.loads((AUDIT/'CHECK.json').read_bytes());need(r['parent_audit']==parent,'parent receipt')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=300)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==parent,'parent audit rerun')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;src=run/'src/Model69ExactPort.lean';obj=run/'Model69ExactPort.olean'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'recorded exits')
        need(sha(src)==sha(PKG/'Model69ExactPort.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        deps={str(PACKAGE/'Init.olean'),str(PARENT/side/'Model69FreshNorms.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct dependencies')
        expected="'Model69ExactPort.four_slots' depends on axioms: [propext]\n'Model69ExactPort.current_shifted_zero_exact' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        need(row['stdout']==expected and row['axiom_reports']==['propext','propext, Classical.choice, Quot.sound'],'reports')
        summaries.append({'side':side,'source_sha256':SOURCE,'object_sha256':OBJECT,'recorded_compiler_exit':0,'recorded_deps_exit':0})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_EXACT_PORT_AUDIT','source_commit':'a832e29cec','author_receipt_sha256':RECEIPT,'recorded_outer_session':57130,'recorded_outer_exit':0,'parent_audit_rerun_exit':p.returncode,'runs':summaries,'scope':'Actual positive current-2011 zero implies exact shifted-69 literal zero without a port-vector premise in every IΣ₁ model. No opposite implication, iPRA derivation, complete inherited axiom inventory or package-transitive/dynamic ancestry claim.'},indent=2))
if __name__=='__main__':main()
