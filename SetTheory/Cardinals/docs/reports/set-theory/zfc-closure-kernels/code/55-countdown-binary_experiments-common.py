from pathlib import Path
import hashlib, re, sys
from types import SimpleNamespace
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
ZFC=ROOT/'upstream/Computability/BusyBeaver/Research/ZFC'
sys.modules['cost_search']=SimpleNamespace()
import strict_affine as strict
PHYS=(6,2,0,4,3,7,8,5,1)
T={}
TABLE_BYTES=(ZFC/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
assert hashlib.sha256(TABLE_BYTES).hexdigest()=='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
PROG_BYTES=(HERE/'Prog254.v').read_bytes()
assert hashlib.sha256(PROG_BYTES).hexdigest()=='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
assert hashlib.sha256((HERE/'strict_affine.py').read_bytes()).hexdigest()=='da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce'
for line in TABLE_BYTES.decode().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split();T[q,int(b)]=(int(w),d,t)
body=PROG_BYTES.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
NODES=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)
SITES=[]
def visit(q,p):
    for bit,e in enumerate(NODES[q]):
        path=p+str(bit);kind,*arg=e.split()
        if kind=='CN':visit(int(arg[0]),path)
        else:SITES.append((path,kind,int(arg[0]) if arg else None))
visit(0,'')
def inc(p):
    return p[:p.rindex('0')]+'1' if '0' in p else None
def strip(p,b,k):
    while k and p:k-=p[-1]==b;p=p[:-1]
    return p
CASES=[]
for p,op,r in SITES:
    for z in ((True,False) if op=='CD' else (None,)):
        physical=PHYS[r] if op in ('CI','CD') else r
        branch=(physical,z) if op=='CD' else None
        if op=='CI' or op=='CD' and not z:nxt=inc(p)
        elif op=='CD':nxt=inc(strip(p,'0',1))
        elif op=='CB':nxt=inc(strip(p,'0',r))
        elif op=='CC':nxt=strip(p,'1',r)
        else:nxt=''
        eff=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not z else None
        right=([('r',0,1,41),('b',1),('box',('plain',eff))] if nxt is None else
               [('b',int(b)) for b in nxt]+[('r',0,1,40-len(nxt)),('b',1),('box',('plain',eff))])
        CASES.append((p,op,r,z,branch,strict.canon([('b',1)],right)))
def check(t,ids=None):
    ok=0
    for i in range(len(CASES)) if ids is None else ids:
        p,op,r,z,b,target=CASES[i]
        try:strict.run(t,p,b,target,halt=op=='CH',fuel=1000)
        except (AssertionError,KeyError) as e:return {'passed':False,'case':i,'path':p,'op':op,'register':r,'zero':z,'reason':str(e),'preceding_passes':ok}
        ok+=1
    return {'passed':True,'cases':ok}
def fold(t,q,r):
    return {k:(w,d,r if target==q else target) for k,(w,d,target) in t.items() if k[0]!=q}

if __name__=='__main__':
    print(len(NODES),len(SITES),len(CASES))
    print(check(T))
    print(check(fold(T,'74','84')))
