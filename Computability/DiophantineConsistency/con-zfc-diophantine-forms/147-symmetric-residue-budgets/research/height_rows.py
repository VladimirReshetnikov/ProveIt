#!/usr/bin/env python3
"""Finite elementary residual transformations, exact height/support objective."""
import argparse,json
from pathlib import Path
from reduce_rows import dot, add_scaled, expand, metrics

PLATEAU = False
SUPPORT_CAP = None

def score(p):
    coeffs=sorted(map(abs,p.values()),reverse=True)
    return (tuple(coeffs[:8]) if PLATEAU else coeffs[0]),len(p),sum(coeffs)

def reduce(rows):
    rs=[dict(r) for r in rows]
    sq=[expand([r]) for r in rs]
    total=expand(rs)
    oldscore=score(total)
    ops=[]
    for iteration in range(40):
        best=None
        targets=[i for i,r in enumerate(rs) if max(map(abs,r.values()))>=30]
        for i in targets:
            for j,rj in enumerate(rs):
                if i==j:continue
                norm=dot(rj,rj);d=dot(rs[i],rj)
                if not norm or not d:continue
                q=(2*abs(d)+norm)//(2*norm)*(1 if d>=0 else -1)
                for k in {q-1,q,q+1}:
                    if not k:continue
                    nr=add_scaled(rs[i],rj,-k)
                    if len(nr)>len(rs[i])+8:continue
                    ns=expand([nr]);nt=add_scaled(add_scaled(total,sq[i],-1),ns,1)
                    if SUPPORT_CAP is not None and len(nt)>SUPPORT_CAP:continue
                    s=score(nt)
                    if s<oldscore and (best is None or s<best[0]):
                        best=(s,i,j,-k,nr,ns,nt)
        if best is None:break
        oldscore,i,j,k,nr,ns,total=best
        rs[i],sq[i]=nr,ns;ops.append([i,j,k])
        print(iteration,oldscore,[i,j,k],flush=True)
    return rs,ops

def main():
    global PLATEAU,SUPPORT_CAP
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('dest',type=Path)
    ap.add_argument('--plateau',action='store_true');ap.add_argument('--support-cap',type=int)
    a=ap.parse_args();PLATEAU=a.plateau;SUPPORT_CAP=a.support_cap
    d=json.loads(a.source.read_text());rows=[{tuple(m):int(c) for c,m in r['terms']} for r in d['residuals']]
    rs,ops=reduce(rows);rev=[dict(r) for r in rs]
    for i,j,q in reversed(ops):rev[i]=add_scaled(rev[i],rev[j],-q)
    if rev!=rows:raise ValueError('inverse mismatch')
    info={'before':metrics(rows),'after':metrics(rs),'operations':len(ops)}
    print(json.dumps(info,indent=2))
    a.dest.mkdir(parents=True,exist_ok=True)
    (a.dest/'row_operations.json').write_text(json.dumps(ops,indent=2)+'\n')
    (a.dest/'metrics.json').write_text(json.dumps(info,indent=2)+'\n')
    d['residuals']=[{'label':f'height row {i}','terms':[[c,list(m)] for m,c in sorted(r.items())]} for i,r in enumerate(rs)]
    d['variant']='elementary residual-height reduction'
    (a.dest/'equation.json').write_text(json.dumps(d,indent=2)+'\n')

if __name__=='__main__':main()
