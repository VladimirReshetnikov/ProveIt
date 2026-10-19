"""Conjugated-register experiment on three frozen rebracketings.

Universal symbolic case success uses the inherited prefix-affine macro
semantics. Failure means this sufficient compiler contract was not proved;
it is not by itself a mathematical counterexample.
"""
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from state_paths import output_directory
from itertools import permutations
from collections import Counter
import sys,json,random,importlib.util,time
ROOT=Path(__file__).resolve().parents[2]
R=output_directory()
INPUTS=ROOT/'experiments/state/inputs'
VENDOR=ROOT/'vendor/context246'
def module(path):
    spec=importlib.util.spec_from_file_location(path.stem,path)
    obj=importlib.util.module_from_spec(spec);sys.modules[path.stem]=obj
    spec.loader.exec_module(obj);return obj
review=module(VENDOR/'code/review_affine_source.py')
affine=module(VENDOR/'sources/prior/prefix_affine.py')
SKIP=(60,44,31,56,38,40,28,64,69)
INV={str(q):i for i,q in enumerate(SKIP)}
PHYSICAL=(6,2,0,4,3,7,8,5,1)

def read(path):
    t={}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,s=line.split();t[q,int(b)]=int(w),d,s
    return t

def sites(path):
    data=json.loads(path.read_text());n={int(k):tuple(map(tuple,v)) for k,v in data['nodes'].items()}
    work=[(('N',data['root']),'')];out=[]
    while work:
        edge,path=work.pop()
        if edge[0]=='N':work.extend(((n[edge[1]][1],path+'1'),(n[edge[1]][0],path+'0')))
        else:out.append((path,'C'+edge[0],None if len(edge)==1 else edge[1]))
    return out

def conjugate(t,p):
    return {k:(w,d,str(SKIP[p[INV[s]]])) if k[0] not in INV and s in INV else (w,d,s)
            for k,(w,d,s) in t.items()}

def run(t,site,zero,p):
    pc,op,r=site
    v=p[PHYSICAL[r]] if op in ('CI','CD') else r
    branch=(v,zero) if op=='CD' else None
    extra=0;effect=None;overflow=False
    if op=='CI':nxt,overflow=review.full_inc(pc);effect=('inc',v)
    elif op=='CD' and not zero:nxt,overflow=review.full_inc(pc);effect=('dec',v);extra=1
    elif op=='CD':nxt,overflow=review.full_inc(review.full_strip(pc,'0',1))
    elif op=='CB':nxt,overflow=review.full_inc(review.full_strip(pc,'0',v))
    elif op=='CC':nxt=review.full_strip(pc,'1',v)
    else:nxt=''
    right=[('b',int(c)) for c in nxt]+[('r',0,1,40+extra+int(overflow)-len(nxt)),('b',1),('box',('plain',effect))]
    rules,literal=affine.run(t,pc,branch,affine.canon([('b',1)],right),halt=op=='CH',fuel=1500)
    assert literal>0

def main():
    begun=time.monotonic()
    selected=[]
    for other in range(9):
        p=list(range(9));p[0],p[other]=p[other],p[0];selected.append(p)
    rng=random.Random(98713)
    for _ in range(100):
        p=list(range(9));rng.shuffle(p)
        if p not in selected:selected.append(p)
    families=[('raw202',INPUTS/'rebracket245_first.tm',INPUTS/'rebracket202_minimal.json'),
              ('raw201',INPUTS/'rebracket201_first.tm',INPUTS/'rebracket201_minimal.json'),
              ('repaired201',INPUTS/'repaired201.tm',INPUTS/'rebracket201_minimal.json')]
    results=[]
    for name,tf,sf in families:
        t=read(tf);ss=sites(sf);cases=[(s,z) for s in ss for z in ((True,False) if s[1]=='CD' else (None,))]
        priority=[];rows=[]
        for p in selected:
            u=conjugate(t,p);failure=None;completed=0
            for i in list(dict.fromkeys(priority+list(range(len(cases))))):
                s,z=cases[i]
                try:run(u,s,z,p)
                except (AssertionError,KeyError) as e:
                    failure=dict(index=i,site=s,zero=z,error=repr(e));priority.insert(0,i);break
                completed+=1
            row=dict(permutation=p,first_failure=failure,passed=completed)
            rows.append(row)
            if failure is None:
                print('PASS',name,p,flush=True)
                (R/f'{name}_permuted.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {s}\n' for (q,b),(w,d,s) in sorted(u.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
        record=dict(name=name,states=len(t)//2,cases=len(cases),priority_failure_cases=sorted(set(priority)),results=rows)
        results.append(record)
        print(name,'permutations',len(rows),'successes',sum(x['first_failure'] is None for x in rows),'failure indices',sorted(set(priority)),flush=True)
    out=dict(scope='Declared 109 conjugated physical selector permutations; all guarded cases for a success, sufficient-affine failure otherwise.',families=results,elapsed=time.monotonic()-begun)
    (R/'permutation_rebracket_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print('elapsed',out['elapsed'])

if __name__=='__main__':main()
