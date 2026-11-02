#!/usr/bin/env python3
"""Review the paired model-divisor artifacts without rerunning Lean."""
import hashlib
import json
from math import gcd
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/model-square-divisor-prototype'
PARENT=BASE/'reviews/ordinary12-coexistence-pair-independent-audit'
OUT=Path('/tmp/ipra-model-square-divisor-replay-46be-02')
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
SOURCE='34fcc00c00408871b5bd98d6ebbff3a3d03bb68f56410d2441c3e056c2d0a2c6'
RECEIPT='b7ea669ad815d9012fbbcc2442488ee883e3197e9ca37b0dbd3cb6f366b548f7'
OBJECT='5c745c178aa64429340e217eb0ef3e2bffba98e747f7c0a29ff3c1ca25c95f97'
PARENT_RECEIPT='5f1fc7a6f519088588ed568e3266da6d109490d556d459a7949d257cbb1bc11d'
REPORTS=['ModelSquareDivisor.unit_certificate_square_right',
         'ModelSquareDivisor.square_divisor_of_reduced_norm',
         'ModelSquareDivisor.zero_right_edge']


def need(ok,msg):
    if not ok:raise ValueError(msg)


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def egcd(a,b):
    if b==0:return (a,1,0)
    g,x,y=egcd(b,a%b);return g,y,x-(a//b)*y


def main():
    rel=PKG.relative_to(ROOT).as_posix()
    changed=subprocess.run(['git','diff','--exit-code','bd56831045','--',rel],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    need(changed.returncode==0,'historical suffix packet drift')
    parent=json.loads((PARENT/'CHECK.json').read_bytes());parent_terminal=json.loads((PARENT/'terminal-observation.json').read_bytes())
    need(digest(PARENT/'CHECK.json')==PARENT_RECEIPT and parent_terminal['audit_observed_exit_code']==0 and parent_terminal['receipt_sha256']==PARENT_RECEIPT and
         parent['status']=='PASS_INDEPENDENT_70_SOURCE_COEXISTENCE_ARTIFACT_AUDIT', 'independently reviewed parent')
    obs=json.loads((PKG/'terminal-observation.json').read_bytes());receipt=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(obs['replay_exit_code']==0 and obs['replay_session']==18427 and obs['receipt_sha256']==RECEIPT and
         digest(PKG/'replay-receipt.json')==digest(OUT/'receipt.json')==RECEIPT,'actual wrapper receipt')
    need(obs['earlier_comment_only_revision']['exit_code']==0 and obs['earlier_comment_only_revision']['receipt_sha256']!=RECEIPT,'earlier source qualification')
    need(receipt['status']=='PASS_PAIRED_MODEL_SQUARE_DIVISOR' and receipt['parent_comparison']['status']=='MATCHED_PASS' and
         receipt['parent_comparison']['rows']==70 and len(receipt['runs'])==2, 'paired result')
    need(digest(PKG/'ModelSquareDivisor.lean')==SOURCE,'source pin')
    for name,h in receipt['fixed_inputs_sha256'].items():need(digest(name)==h,'fixed input '+name)
    run_summaries=[]
    for r,label in zip(receipt['runs'],('author','peer')):
        src=OUT/label/'src/ModelSquareDivisor.lean';obj=OUT/label/'ModelSquareDivisor.olean'
        need(r['label']==label and r['exit']==0 and r['deps_exit']==0 and not r['stderr'], 'run exits '+label)
        need(digest(src)==r['source_sha256']==SOURCE and digest(obj)==r['object_sha256']==OBJECT, 'source/object '+label)
        need(r['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and r['command'][-1]==str(obj), 'bounded command '+label)
        expected={str(Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean')),
                  str(PAIR/label/'child-output/lib/DiophantineConsistency/ArithmeticGcdNormalization.olean')}
        need(set(r['deps_stdout'].splitlines())==expected,'recorded direct imports '+label)
        parent_state=json.loads((PAIR/label/'child-output/state.json').read_bytes())
        row=next(x for x in parent_state['records'] if x['module']=='DiophantineConsistency.ArithmeticGcdNormalization')
        need(digest(PAIR/label/'child-output/lib/DiophantineConsistency/ArithmeticGcdNormalization.olean')==row['object_sha256'], 'direct project dependency '+label)
        reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",r['stdout'],re.M)
        need([n for n,_ in reports]==REPORTS and [v for _,v in reports]==r['axiom_reports'] and
             all({z.strip() for z in v.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,v in reports) and
             not re.search(r'warning:|sorryAx|\bsorry\b|error:',r['stdout']),'axiom reports '+label)
        run_summaries.append({'label':label,'object_sha256':digest(obj),'recorded_exit':r['exit'],'direct_project_dependency':row['object_sha256']})
    need(receipt['runs'][0]['stdout']==receipt['runs'][1]['stdout'],'matching stdout')

    # Bounded signed-certificate sanity check includes a=0, b=0 and r=0;
    # it supplements the checked Lean theorem and is not its proof.
    counts={'states':0,'a_zero':0,'b_zero':0,'r_zero':0,'b_gt_one':0}
    for a in range(13):
      for b in range(13):
       if gcd(a,b)!=1:continue
       _,x,y=egcd(a,b)
       u,w=max(-x,0),max(x,0);v,z=max(-y,0),max(y,0)
       need(1+a*u+b*v==a*w+b*z,'initial Bezout')
       U=a*(2*w*u)+2*b*(w*v+u*z)
       W=a*(w*w+u*u)+2*b*(w*z+u*v)
       Bneg=2*z*v;Bpos=z*z+v*v
       need(1+a*U+b*b*Bneg==a*W+b*b*Bpos,'squared Bezout')
       for r in range(13):
        for t in range(13):
         if t*b*b!=r*a*a+b*b:continue
         need((r==0 if b==0 else r%(b*b)==0),'square divisor')
         counts['states']+=1;counts['a_zero']+=a==0;counts['b_zero']+=b==0;counts['r_zero']+=r==0;counts['b_gt_one']+=b>1
    need(all(counts[k]>0 for k in counts),'edge coverage')
    print(json.dumps({'status':'PASS_INDEPENDENT_MODEL_SQUARE_DIVISOR_ARTIFACT_AUDIT','reviewed_commit':'bd56831045',
      'source_sha256':SOURCE,'author_receipt_sha256':RECEIPT,'parent_audit_receipt_sha256':PARENT_RECEIPT,
      'recorded_wrapper_exit':obs['replay_exit_code'],'runs':run_summaries,'matched_stdout':True,
      'recorded_axiom_reports':REPORTS,'bounded_survey_bounds':'0 <= a,b,r,t <= 12','bounded_survey':counts,
      'scope':'Read-only suffix artifact audit and finite sanity checks; no independent Lean replay, no constructed gcd or norm, no descent, graph transport, calibration, or iPRA proof.'},indent=2))


if __name__=='__main__':main()
