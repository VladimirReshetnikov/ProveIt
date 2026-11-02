#!/usr/bin/env python3
"""Read-only review of historical and independently replayed denominator."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-denominator-prototype'
HERE=Path(__file__).resolve().parent
SOURCE='898b9fa159ba784cc32b71e639a159d785d14e67096aee18a8df07740e23b8a3'
OBJECT='ede9df1c0bc17b01ad20e5d9717d4425f61f01f70610bb3012f4a8e2ed28b1ca'
SEED='2785949197112d2544646598e6637b29a4dee0fc7d8b41dbca2711febb7e9ec8'
PARENT='31e4f1f541b437b28d37b55e03ea6194d27bf4c4c4009ed3f1bbffefdc453897'
SELF='f0422f93287536aecccea34c298741cc96644551d3357400d31863ab1d31e1f4'
PINS={'FreeJDenominator.lean':SOURCE,'replay.py':'cc634d1285b9a0e6648e5b77c91a0d69ea6d0981423160f83b00b6e16403c923',
      'replay-01-receipt.json':'b3d2cc8b6126897678cd9ac8a21ac0584dfaf20f79ef00e0300f3d06349d6e20',
      'replay-02-receipt.json':'5b4b9b122a2e26e26d8797b379e37d3b6c924c3ad7940d15a63f7504299c4fc8'}
REPORTS=['FreeJDenominator.Q_eval','FreeJDenominator.Q_gt_one','FreeJDenominator.neg_times_pos',
         'FreeJDenominator.scale_negative','FreeJDenominator.one_sub_eval','FreeJDenominator.var_add_eval',
         'FreeJDenominator.denominator_negative']


def need(ok,msg):
    if not ok:raise ValueError(msg)


def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    for name,h in PINS.items():
        p=PKG/name;data=subprocess.run(['git','show','62a8e07a9b:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(data).hexdigest()==digest(p)==h,'source or receipt pin '+name)
    pre=BASE/'research/ordinary12-ipra-bridge/free-j-graph-vbound-prototype/replay-receipt.json'
    need(digest(pre)==PARENT,'historical V-bound receipt')
    seed=Path('/tmp/ipra-ordinary12-freej-vbound-replay-01/FreeJGraphVBound.olean')
    need(digest(seed)==SEED,'shared V-bound object')
    need(digest(HERE/'replay-receipt.json')==SELF and digest('/tmp/ipra-freej-denominator-independent-20261101.json')==SELF,'independent receipt')
    cases=[('author01',PKG/'replay-01-receipt.json',Path('/tmp/ipra-freej-denominator-replay-01')),
           ('author02',PKG/'replay-02-receipt.json',Path('/tmp/ipra-freej-denominator-replay-02')),
           ('independent',HERE/'replay-receipt.json',Path('/tmp/ipra-freej-denominator-independent-20261101'))]
    reference=None;summaries=[]
    for label,receipt,out in cases:
        r=json.loads(receipt.read_bytes());obj=out/'FreeJDenominator.olean';src=out/'src/DiophantineConsistency/FreeJDenominator.lean'
        copy=out/'lib/DiophantineConsistency/FreeJGraphVBound.olean'
        need(r['status']=='PASS_BOUNDED_FREEJ_DENOMINATOR' and r['lean_exit_code']==0 and r['deps_exit_code']==0, 'recorded inner exits '+label)
        need(digest(obj)==r['object_sha256']==OBJECT and digest(src)==SOURCE and digest(copy)==SEED and
             r['parent_vbound_object_sha256']==SEED and r['parent_vbound_receipt_sha256']==PARENT, 'artifact and shared parent '+label)
        need(r['lean_command'][1:4]==['-M3000','-j1','-DElab.async=false'] and r['lean_command'][-1]==str(obj),'bounded compiler command '+label)
        expected={'/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean',str(copy)}
        need(set(r['deps_stdout'].splitlines())==expected and not r['lean_stderr'], 'direct dependencies '+label)
        reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",r['lean_stdout'],re.M)
        need([n for n,_ in reports]==REPORTS and all({x.strip() for x in vals.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,vals in reports) and
             not re.search(r'warning:|sorryAx|\bsorry\b|error:',r['lean_stdout']), 'axioms '+label)
        inputs=r['checked_earlier_parent_inputs'];need(len(inputs)==83,'historical parent input count')
        for path,h in inputs.items():need(digest(path)==h,'earlier parent input '+path)
        if reference is None:reference=(r['lean_stdout'],inputs)
        need(reference==(r['lean_stdout'],inputs),'shared historical ancestry '+label)
        summaries.append({'label':label,'object_sha256':OBJECT,'inner_lean_exit':0,'dependency_exit':0,'checked_earlier_parent_inputs':len(inputs)})
    # Finite sanity checks for the strict sign, including its zero edges.
    checks=0
    for a in range(9):
      for t in range(1,5):
       Q=(3+4*a+a*a)*((1+t)**2-1)
       need(Q>1,'Q positivity')
       for c in range(1,6):
        for V in range(1,6):
         for n in range(6):
          D=c**4*2*(1-Q)*(n+V);need(D<0,'denominator sign');checks+=1
    need(2*(1-1)*(1+1)==0 and 2*(1-2)*(1-1)==0 and 0**4*2*(1-2)*(1+1)==0,'zero-edge controls')
    print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_DENOMINATOR_AUDIT','reviewed_commit':'62a8e07a9b',
      'source_sha256':SOURCE,'independent_replay_sha256':SELF,'independent_replay_observed_exit':0,
      'independent_replay_tool_session':55667,'original_second_wrapper_exit_observed':False,
      'shared_parent_receipt_sha256':PARENT,'shared_parent_object_sha256':SEED,'runs':summaries,
      'finite_sign_cases':checks,'q_one_w_zero_c_zero_controls':True,
      'scope':'Three bounded compilations share one historical parent/provider. No current-source pair, signed residual bridge, descent, calibration or iPRA proof.'},indent=2))


if __name__=='__main__':main()
