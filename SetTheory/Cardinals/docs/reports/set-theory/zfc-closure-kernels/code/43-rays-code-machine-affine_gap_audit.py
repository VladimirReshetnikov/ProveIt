#!/usr/bin/env python3
"""Measure exact sufficient header gaps using the attributed affine checker.

Jeff's upstream Python checker supplies the executor and the four register
box summaries. This script enumerates literal Prog254.v leaves and varies
the single affine gap parameter. It is diagnostic, not a kernel proof.
"""
from pathlib import Path
import argparse, collections, json, time
from inspect_runtime252 import PROGRAM, HERE, load_runtime

SRC=HERE/'upstream/ZF/m254/tools/tm/symexec.py'
BODY=SRC.read_text().split("SKIP =",1)[1].split('\npaths = json.load',1)[0]
BODY='SKIP ='+BODY

def leaves():
    out=[]
    def visit(node,path):
        for b,e in enumerate(PROGRAM[node]):
            p=path+str(b);kind,arg=e
            if kind=='CN':visit(arg,p)
            else:out.append((p,kind,arg))
    visit(0,'');assert len(out)==6460;return out

def run_audit(gaps):
    rows={(str(q),b):(w,'R' if d==1 else 'L',str(n)) for (q,b),(w,d,n) in load_runtime().items()}
    ns={'T':rows,'D0':40};exec(compile(BODY,str(SRC),'exec'),ns)
    phy={0:6,1:7,2:0,3:2,4:1,5:8,6:4,7:3,8:5}
    sites=leaves();cases=[]
    for i,(path,op,arg) in enumerate(sites):
        branches=['z','p'] if op=='CD' else ['-']
        for branch in branches:
            if op=='CI' or (op=='CD' and branch=='p'):dest=ns['inc'](path)
            elif op=='CD':dest=ns['inc'](ns['strip']('0',1,path))
            elif op=='CC':dest=ns['strip']('1',arg,path)
            elif op=='CB':dest=ns['inc'](ns['strip']('0',arg,path))
            else:dest=''
            effect=(('inc',phy[arg]),) if op=='CI' else ((('dec0' if branch=='z' else 'dec'),phy[arg]),) if op=='CD' else ()
            cases.append((i,path,op,arg,branch,dest,effect))
    assert len(cases)==8391
    result={'scope':'sufficient affine checker bounds; unchanged attributed box summaries; no minimality or formal proof',
            'runtime':'old5 to old64 fold of public253; 252 working states; no initializer calibration',
            'program_sites':len(sites),'instruction_cases':len(cases),'gaps':[]}
    for gap in gaps:
        start=time.monotonic();ns['D0']=gap;passed=0;fail=[];hist=collections.Counter()
        for i,(leaf,path,op,arg,branch,dest,effect) in enumerate(cases):
            if len(path)>gap:
                fail.append(dict(case=i,leaf=leaf,path=path,op=op,arg=arg,branch=branch,reason='negative input padding'))
                hist['negative input padding']+=1;continue
            if dest is None:
                expect=ns['canon']([('b',1)],[('r',0,1,gap+1),('b',1),('box',('plain',)+effect)])
            else:expect=ns['canon']([('b',1)],ns['tape_R'](dest,0,effect))
            try:
                z=ns['run']('96',[('b',1)],ns['tape_R'](path,0,()),branch,expect,fuel=1000)
                if z[0]!=('halt' if op=='CH' else 'ok'):raise ValueError('unexpected '+z[0])
                passed+=1
            except (ns['Fail'],KeyError,ValueError) as ex:
                reason=str(ex);hist[reason]+=1
                fail.append(dict(case=i,leaf=leaf,path=path,op=op,arg=arg,branch=branch,reason=reason))
        row=dict(gap=gap,passed=passed,failed=len(fail),failures=dict(hist),cases=fail,elapsed=time.monotonic()-start)
        result['gaps'].append(row)
        print(json.dumps({k:v for k,v in row.items() if k!='cases'}),flush=True)
    assert next(x for x in result['gaps'] if x['gap']==40)['passed']==8391
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--gaps',default='32,33,34,35,36,37,38,40')
    p.add_argument('--output',type=Path,default=HERE/'runtime252_gaps.json');a=p.parse_args()
    a.output.write_text(json.dumps(run_audit(list(map(int,a.gaps.split(',')))),indent=2)+'\n')
