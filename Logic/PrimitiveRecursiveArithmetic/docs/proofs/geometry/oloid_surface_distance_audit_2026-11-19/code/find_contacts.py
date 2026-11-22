"""Optional witness generator. The proof checker independently validates the output."""
import csv
import json
from pathlib import Path
import mpmath as mp
from geometry import POINTS

mp.mp.dps = 75
r3 = mp.sqrt(3)
T = 2*mp.pi/3
W = 2*r3*mp.pi/9
K = r3*(6+mp.log(4))/9
H = K+r3
base = Path(__file__).resolve().parents[1]/'data'

def real(q):
    return mp.mpf(q.numerator)/q.denominator

def from_h(h):
    v=h/r3
    w=mp.sqrt(1-v*v)
    d=1+3*v*v
    a=(2*r3/9*(mp.asin(v)+mp.atan2(2*v,w)+6*v*w/d),
       r3/9*(mp.log(d)+8*(1-1/d)))
    e=(-2*v*(1+v*v)*w/d,(1+v*v+2*v**4)/d)
    tangent=(w**3/d,v*(3+v*v)/d)
    return a,e,tangent

def point(p):
    h,s,*_=POINTS[p]
    a,e,_=from_h(real(h))
    return tuple(x+r3*real(s)*y for x,y in zip(a,e))

def gate(g,f):
    if g in 'LR':
        return ((0,r3*f) if g=='L' else (W,K+r3*f)), (0,r3)
    a,_,v = from_h(mp.tan(T*f/2))
    return (a,tuple(T*x for x in v)) if g=='A' else ((W-a[0],H-a[1]),tuple(-T*x for x in v))

def grad(p,q,w,ts):
    gates=[gate(g,t) for g,t in zip(w,ts)]
    stops=[p,*[a for a,_ in gates],q]
    units=[]
    for a,b in zip(stops,stops[1:]):
        x,y=(v-u for u,v in zip(a,b))
        r=mp.hypot(x,y)
        units.append((x/r,y/r))
    return [sum((a-b)*x for a,b,x in zip(left,right,tan)) for left,right,(_,tan) in zip(units,units[1:],gates)]

def main():
    from fractions import Fraction
    out={}
    with (base/'distances.csv').open() as f:
        for row in csv.DictReader(f):
            w=row['upper_route']
            if not set('AB').intersection(w):
                continue
            p,q=point(row['from']),point(row['to'])
            ts=tuple(real(Fraction(x)) for x in row['upper_gate_parameters'].split())
            z=mp.findroot(lambda *x:tuple(grad(p,q,w,x)),ts,tol=mp.mpf('1e-65'))
            out[row['from']+'-'+row['to']]=[mp.nstr(t,36) for t in z]
    (base/'contacts.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':
    main()
