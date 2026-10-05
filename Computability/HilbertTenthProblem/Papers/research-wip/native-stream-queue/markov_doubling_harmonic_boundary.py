import argparse, hashlib, json
from fractions import Fraction as F
from pathlib import Path

def require(ok,msg):
    if not ok:raise ValueError(msg)

def transfer(mask,m):
    out={}
    for k,v in mask.items():
        for n,c in [(m,F(1)),(-m,F(-1))]:
            if (k+n)%2==0:
                j=(k+n)//2;out[j]=out.get(j,F(0))+v*c
    return {k:v for k,v in out.items() if v}

def rref(rows,n):
    rows=[list(x) for x in rows];pivots=[];row=0
    for col in range(n):
        pivot=next((i for i in range(row,len(rows)) if rows[i][col]),None)
        if pivot is None:continue
        rows[row],rows[pivot]=rows[pivot],rows[row]
        scale=rows[row][col];rows[row]=[x/scale for x in rows[row]]
        for i in range(len(rows)):
            if i!=row and rows[i][col]:
                scale=rows[i][col];rows[i]=[x-scale*y for x,y in zip(rows[i],rows[row])]
        pivots.append(col);row+=1
    inconsistent=any(not any(r[:n]) and r[n] for r in rows)
    return rows,pivots,inconsistent

def run(wip):
    examples=[]
    for m in [1,3,5,7,9]:
        for lam in [F(-2,5),F(-1,3),F(0),F(1,3),F(2,5)]:
            mask={0:F(1),m:lam,-m:lam}
            want={} if not lam else {m:lam,-m:-lam}
            require(transfer(mask,m)==want,'fresh eigenmask')
            for n in range(1,7):
                require(transfer(mask,2*n)=={n:F(1),-n:F(-1)},'even harmonic normalization')
            examples.append({'m':m,'lambda':str(lam),'strict_minimum':str(1-2*abs(lam))})
    systems=[]
    for D in range(10):
        frequencies=list(range(1,D+1,2))
        for m in range(1,12):
            constant=transfer({0:F(1)},m)
            columns=[transfer({j:F(1),-j:F(1)},m) for j in frequencies]+[{m:F(-1),-m:F(1)}]
            indices=sorted(set(constant).union(*(set(c) for c in columns)))
            rows=[[c.get(k,F(0)) for c in columns]+[-constant.get(k,F(0))] for k in indices]
            reduced,pivots,bad=rref(rows,len(columns))
            if m%2==0:require(bad,'even system inconsistent')
            else:
                require(not bad,'odd system consistent')
                dim=len(columns)-len(pivots)
                require(dim==int(m<=D),'one allowed coefficient or constant mask')
                candidate=[F(int(j==m)) for j in frequencies]+[F(1)] if m<=D else [F(0)]*len(columns)
                require(all(sum(x*y for x,y in zip(r[:-1],candidate))==r[-1] for r in rows),'classified kernel')
            systems.append({'D':D,'m':m,'inconsistent':bad,'rank':len(pivots),'unknowns':len(columns)})
    names=['markov_sine_lift.md','markov_mask_matrix_lift.md','markov_positive_guard_savings.md']
    return {'status':'PASS','scope':'Fresh explicitly constructed Fourier objects and exact linear constraints only; no frozen programs or source arrays run. The continuous theorem is a separate functional proof.','helper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'dependencies':{n:hashlib.sha256((wip/n).read_bytes()).hexdigest() for n in names},'examples':examples,'even_image_checks':150,'linear_systems':systems}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',required=True,type=Path);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args()
    data=run(a.root);encoded=json.dumps(data,sort_keys=True,indent=2)+'\n'
    if a.output:
        with a.output.open('x') as f:f.write(encoded)
    else:require(a.expect.read_text()==encoded,'exact receipt')
    print(json.dumps({'status':'PASS','examples':len(data['examples']),'even_images':data['even_image_checks'],'linear_systems':len(data['linear_systems'])}))
