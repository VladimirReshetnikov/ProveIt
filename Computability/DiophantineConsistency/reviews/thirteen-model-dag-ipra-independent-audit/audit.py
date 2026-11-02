#!/usr/bin/env python3
"""Read-only paired exact DAG iPRA client and audited parent verification."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/thirteen-model-dag-ipra-followup';OUT=Path('/tmp/ipra-thirteen-dag-ipra-pair-01');PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
RECEIPT='a04ec49b4635d8a879a262bd20620e65fbc3aec096334001f21e194d8f0fd3fc';SOURCE='235d81f3b1d399593e413587863a531277b9c41b989c8c9d6d663381242de792';OBJECT='4096f9048438c0974347087c5ecd4491a57f63457d2c10f6ad4f3686548c427c';NAMES=('sameNoZeroDag','bridgeDag','native_equivalenceDag','standard_equivalenceDag','reference_equivalenceDag','standard_translated_consistencyDag')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    for name in ('README.md','Model69DagIPRADraft.lean','author-axiom-inventory.txt','peer-axiom-inventory.txt','replay.py','replay-receipt.json','terminal-observation.json'):
        p=PKG/name;b=subprocess.run(['git','show','652071b812:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes());need(obs['session']==94327 and obs['actual_exit_code']==0 and obs['receipt_sha256']==RECEIPT and obs['stdout']=='PASS_PAIRED_THIRTEEN_DAG_IPRA '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes());need(r['status']=='PASS_PAIRED_THIRTEEN_DAG_IPRA' and len(r['runs'])==2,'status')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    need(sha(AUDIT/'CHECK.json')=='50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce','parent receipt hash')
    parent=json.loads((AUDIT/'CHECK.json').read_bytes());need(r['parent_audit']==parent,'parent receipt')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;src=run/'src/Model69DagIPRADraft.lean';obj=run/'Model69DagIPRADraft.olean';lib=PARENT/side/'lib'
        need(row['side']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'recorded exits')
        need(sha(src)==sha(PKG/'Model69DagIPRADraft.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        deps={str(PACKAGE/'Init.olean'),str(lib/'Model69EndpointBindingDraft.olean'),str(lib/'DiophantineConsistency/IPRABoundedRhoZFC.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct dependencies')
        parsed=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in parsed]==['Model69DagIPRADraft.'+n for n in NAMES] and [a for _,a in parsed]==['propext, Classical.choice, Quot.sound']*6 and row['axiom_reports']==[list(x) for x in parsed] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'named reports')
        need((PKG/(side+'-axiom-inventory.txt')).read_text()==row['stdout'],'recorded log')
        summaries.append({'side':side,'source_sha256':SOURCE,'object_sha256':OBJECT,'recorded_compiler_exit':0,'recorded_deps_exit':0,'named_axiom_reports':len(parsed)})
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=900)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==parent,'parent audit rerun')
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_DAG_IPRA_AUDIT','source_commit':'652071b812','author_receipt_sha256':RECEIPT,'recorded_outer_session':94327,'recorded_outer_exit':0,'parent_audit_rerun_exit':p.returncode,'names':list(NAMES),'runs':summaries,'scope':'Lean derivability for the exact positiveShift 2011 literal in the selected iPRA presentations and mapped/translated Foundation consistency encoding; the 69-operation count describes the shared positive-coordinate DAG. No global minimality, different-tuple calibration, package-transitive/dynamic or Foundation outer-wrapper claim.'},indent=2))
if __name__=='__main__':main()
