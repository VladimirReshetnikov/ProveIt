#!/usr/bin/env python3
"""Finite controls for literal uniform folds of the ten new loader states.

This is a bounded rejection experiment, not a proof or an executable smaller
consistency machine. Existing runtime rows are never changed.
"""
from pathlib import Path
import sys, json, time
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'machine/code'))
import gap_loader as gl

def check(table,g,values,entry,bound):
    ones=gl.paint(g,values,0,pc='1')
    expected=gl.paint(g+2,[g+1]+values[1:],-g-3)
    q,h=96,0
    seen=set()
    for n in range(bound):
        if q==96 and n:
            return (h,ones)==(-g-3,expected),n
        if q==254:return False,n
        if n<200:
            snap=q,h,frozenset(ones)
            if snap in seen:return False,n
            seen.add(snap)
        action=table.get((q,int(h in ones)))
        if action is None:return False,n
        w,d,q=action
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    return False,bound

def main():
    base=gl.read_table();base.update(gl.loader_rows());base[96,1]=(0,'L',300)
    states=sorted({q for q,b in base})
    tried=0;survivors=[];best=[];t0=time.time()
    samples=[(1,[0,2,0,7,1,0,3,4]),(3,[0]+[0]*7),(9,[0,2,1,0,1,0,0,2,9])]
    for dead in range(300,310):
        for keep in states:
            if dead==keep:continue
            table={(q,b):(w,d,keep if t==dead else t)
                   for (q,b),(w,d,t) in base.items() if q!=dead}
            tried+=1;passed=0
            for g,values in samples:
                ok,n=check(table,g,values,300,10*(2*g*g+19*g+59))
                if not ok:break
                passed+=1
            if passed:best.append({'dead':dead,'keep':keep,'samples_passed':passed})
            if passed==len(samples):survivors.append({'dead':dead,'keep':keep})
    data={'status':'complete','scope':__doc__,'recipes':tried,'samples':samples,
          'survivors':survivors,'partial_survivors':best,'seconds':time.time()-t0}
    path=Path(__file__).with_name('loader_fold_results.json')
    path.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:data[k] for k in ['recipes','survivors','partial_survivors','seconds']}))

if __name__=='__main__':main()
