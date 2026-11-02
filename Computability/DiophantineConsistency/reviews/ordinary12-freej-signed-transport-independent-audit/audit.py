#!/usr/bin/env python3
"""Audit the paired free-J signed transport without running Lean again."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-signed-transport-prototype'
EVIDENCE=BASE/'reviews/free-j-signed-transport-replay'
PARENT=BASE/'reviews/ordinary12-coexistence-pair-independent-audit'
HERE=Path(__file__).resolve().parent
GRAPH=BASE/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json'
CORE=BASE/'research/ordinary12-ipra-bridge/free-j-prototype/Ordinary12FreeJ.lean'
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
ORIGINAL=Path('/tmp/ipra-freej-signed-transport-replay-01')
REPLAY=Path('/tmp/ipra-freej-signed-transport-replay-independent-20261101')
SOURCE='dd2608fd773126ebe37cb0bd921fcb4cc06467e36e4be61aff050fa40dc2a116'
OBJ='aac4683be9aabdd7362fa391322684e5443e4b0d11b66aa2b6d03edb6bb2d5b6'
ORIGINAL_RECEIPT='7cbcac3408b270b33d94b718028a5142df1419f093ceff389e8729da9750000d'
NEW_RECEIPT='a86cf4b0fb5b4a450b56f9445a53560c16d2e40da0ba69580fc613ee1293659a'
PARENT_RECEIPT='5f1fc7a6f519088588ed568e3266da6d109490d556d459a7949d257cbb1bc11d'
REPORTS=['FreeJOrdinaryTransport.graph_residual_shape','FreeJOrdinaryTransport.polarized_eval',
         'FreeJOrdinaryTransport.actual_unpolarized_zero']


def need(ok,msg):
    if not ok:raise ValueError(msg)


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    for path in (PKG,EVIDENCE):
        p=subprocess.run(['git','diff','--exit-code','d89529fa3a','--',path.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        need(p.returncode==0,'historical packet drift '+str(path))
    need(digest(PKG/'FreeJSignedTransport.lean')==SOURCE,'source pin')
    need(digest(GRAPH)=='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22','graph pin')
    graph=json.loads(GRAPH.read_bytes());source=(PKG/'FreeJSignedTransport.lean').read_text();core=CORE.read_text()
    need(len(graph['source'])==95 and len(graph['witnesses'])==12 and len(graph['fixed_numerals'])==4,'graph signature')
    def graph_matches(text):
        try:body=text.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('\n  -- END LITERAL GRAPH',1)[0]
        except IndexError:return False
        expected='\n'.join(f'  let {n} := {a} {op} {b}' for n,op,a,b in graph['source'])
        return body==expected
    need(graph_matches(source) and graph_matches(core),'exact 95 rows in transport and parent core')
    for i,name in enumerate(graph['witnesses']):
        need(source.count(f'  let {name} : Expr (Fin 12) := .var {i}\n')==1,'witness '+name)
    for i,name in enumerate(graph['fixed_numerals']):
        need(source.count(f'  let {name} : Expr (Fin 12) := .constant (p {i})\n')==1,'port '+name)
    need(source.count('  ⟨Q,den,V,n⟩')==1,'selected graph expressions')
    need(not graph_matches(source.replace('let qm := J * beta','let qm := J + beta',1)), 'changed graph mutation')
    need(source.replace('  ⟨Q,den,V,n⟩','  ⟨Q,den,n,V⟩',1).count('  ⟨Q,den,V,n⟩')==0,'selected tuple mutation')

    parent=json.loads((PARENT/'CHECK.json').read_bytes());pt=json.loads((PARENT/'terminal-observation.json').read_bytes())
    need(digest(PARENT/'CHECK.json')==PARENT_RECEIPT and pt['audit_observed_exit_code']==0 and pt['receipt_sha256']==PARENT_RECEIPT and
         parent['status']=='PASS_INDEPENDENT_70_SOURCE_COEXISTENCE_ARTIFACT_AUDIT','audited parent')
    obs=json.loads((EVIDENCE/'terminal-observation.json').read_bytes())
    need(obs['observed_exit_code']==0 and obs['session_id']==94351 and obs['receipt_sha256']==ORIGINAL_RECEIPT and
         digest(EVIDENCE/'receipt.json')==digest(ORIGINAL/'receipt.json')==ORIGINAL_RECEIPT,'original wrapper observation')
    need(digest(HERE/'replay-receipt.json')==digest(REPLAY/'receipt.json')==NEW_RECEIPT,'independent replay receipt')
    bad=(EVIDENCE/'attempt02.log').read_text();old=(EVIDENCE/'attempt03.log').read_text()
    need('error:' in bad and 'sorryAx' in bad and 'warning:' in old and 'sorryAx' not in old,'prior attempt qualifications')
    cases=[('original',EVIDENCE/'receipt.json',ORIGINAL),('independent',HERE/'replay-receipt.json',REPLAY)]
    results=[];allout=[]
    for label,receipt,out in cases:
        r=json.loads(receipt.read_bytes());need(r['status']=='PASS_PAIRED_FREEJ_SIGNED_TRANSPORT' and
             r['parent_comparison']['status']=='MATCHED_PASS' and r['parent_comparison']['rows']==70 and len(r['runs'])==2,'paired result '+label)
        for path,h in r['fixed_inputs_sha256'].items():need(digest(path)==h,'fixed input '+path)
        for item,side in zip(r['runs'],('author','peer')):
            src=out/side/'src/FreeJSignedTransport.lean';obj=out/side/'FreeJSignedTransport.olean'
            need(item['label']==side and item['exit']==item['deps_exit']==0 and not item['stderr'],'child exits '+label+' '+side)
            need(digest(src)==item['source_sha256']==SOURCE and digest(obj)==item['object_sha256']==OBJ,'object '+label+' '+side)
            need(item['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and item['command'][-1]==str(obj),'bounded command')
            lib=PAIR/side/'child-output/lib';deps={str(Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean')),
                 str(lib/'DiophantineConsistency/ModelDifferenceRing.olean'),str(lib/'DiophantineConsistency/FreeJNormZero.olean')}
            need(set(item['deps_stdout'].splitlines())==deps,'direct dependency set')
            parent_state=json.loads((PAIR/side/'child-output/state.json').read_bytes())
            for name in ('DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.FreeJNormZero'):
                row=next(x for x in parent_state['records'] if x['module']==name)
                need(digest(lib/Path(*name.split('.')).with_suffix('.olean'))==row['object_sha256'],'fresh parent '+name)
            reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",item['stdout'],re.M)
            need([n for n,_ in reports]==REPORTS and [x for _,x in reports]==item['axiom_reports'] and
                 all({x.strip() for x in a.split(',')}<={'propext','Classical.choice','Quot.sound'} for _,a in reports) and
                 not re.search(r'warning:|sorryAx|\bsorry\b|error:',item['stdout']),'recorded diagnostics')
            allout.append(item['stdout']);results.append({'replay':label,'side':side,'object_sha256':OBJ,'lean_exit':0,'deps_exit':0})
    need(len(set(allout))==1,'four matching axiom outputs')

    # Exact integer controls for the polarization at positive, zero and
    # negative cut values; the Lean theorem is universal, this loop is not.
    count=0
    for q in range(-3,4):
      for d in range(-3,4):
       for z in range(-3,4):
        for n in range(-3,4):
         w=z+n;p=1-q;cy=q*z*z-1;h=p*w*w+cy;b=2*p*w
         polarized=(d*h-q*p)**2+4*d*q*p*cy
         unpolarized=(d*h+q*p)**2-d*q*b*b
         need(polarized==unpolarized,'polarization identity sample');count+=1
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_SIGNED_TRANSPORT_AUDIT','source_commit':'d89529fa3a',
      'source_sha256':SOURCE,'graph_sha256':digest(GRAPH),'graph_rows':95,'witnesses':12,'ports':4,
      'original_receipt_sha256':ORIGINAL_RECEIPT,'original_wrapper_exit':obs['observed_exit_code'],
      'independent_receipt_sha256':NEW_RECEIPT,'independent_wrapper_exit':0,'independent_wrapper_session':9424,
      'parent_audit_receipt_sha256':PARENT_RECEIPT,'runs':results,'finite_signed_polarization_cases':count,
      'earlier_attempt02_failed_with_sorryAx':True,'earlier_attempt03_had_style_warnings':True,
      'scope':'Two matched-parent suffix pairs; no independent provider ancestry, denominator integrality, full graph-to-cleared identity, checker calibration or iPRA proof.'},indent=2))


if __name__=='__main__':main()
