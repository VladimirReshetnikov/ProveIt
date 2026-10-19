#!/usr/bin/env python3
"""Exact variable-anchor bisimulation fold of the separate 19-state copier."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import sys,json,hashlib,itertools,random
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(OUT.parent/'native_copier'))
import biased_reference_copy19 as C
import marked_unary_copy as M

def compile_copy():
    T,s,r,ids=C.compile_copy(variable_anchor=True)
    dead,keep=ids['after_anchor'],ids['find_ones']
    def f(q):return keep if q==dead else q
    for b in (0,1):
        a=T[dead,b];z=T[keep,b]
        assert (a[0],a[1],f(a[2]))==(z[0],z[1],f(z[2]))
    order=sorted(set(q for q,b in T)-{dead});ren={q:i for i,q in enumerate(order)};ren[r]=len(order)
    result={(ren[q],b):(w,d,ren[f(t)])for(q,b),(w,d,t)in T.items()if q!=dead}
    return result,ren[f(s)],ren[r],{name:ren[f(q)]for name,q in ids.items()}

def main():
    T,s,ret,ids=compile_copy();count=0;maxsteps=0;rng=random.Random(1824618)
    # Header is either one positive run or the two positive runs of the
    # seven-cell four-mode header; both preserve isolated separator invariant.
    headers=['1'*n+'0'for n in range(1,8)]+['1'*k+'0'+'1'*(5-k)+'0'for k in range(1,5)]
    for value,idx,header,extra in itertools.product(range(15),range(4),headers,(2,3,8)):
        vals=[1,5,2,4];vals[idx]=value+3;gap=value+extra;c=-3;anchor=c+gap+1
        one={c}|{anchor+j for j,b in enumerate(header)if b=='1'};p=anchor+len(header);starts=[]
        for length in vals:starts.append(p);one.update(range(p,p+length));p+=length+1
        src=starts[idx];one.remove(src);one|={c-3,c-1,p,p+3}
        expected=one|set(range(c,c+value+1))|{src}
        actual,h,steps,window=M.run(T,s,ret,one,src)
        assert actual==expected and h==c+value and window[0]>=c and window[1]<=src+value+3
        count+=1;maxsteps=max(maxsteps,steps)
    text=f'#! start {s}\n'+''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(T.items()))
    (OUT/'biased_reference_copy_18.tm').write_text(text)
    result={'status':'PASS','states':ret,'operational_states':ret-1,'rows':len(T),'ports':{'RETURN':ret},'start':s,'names':ids,'exact_fold':['after_anchor','find_ones'],'tests':count,'maximum_steps':maxsteps,'table_sha256':hashlib.sha256(text.encode()).hexdigest(),'scope':'Exact bisimulation of variable-anchor19 plus positive-run-header induction; prepared frames only.'}
    (OUT/'biased_reference_copy18_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
