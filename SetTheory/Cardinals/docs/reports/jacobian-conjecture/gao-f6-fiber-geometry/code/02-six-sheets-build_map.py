"""Exact sparse construction of Gao's F_6; no numerical arithmetic."""
from sympy.polys.rings import ring
from sympy import QQ
from pathlib import Path
import json, time

def build_map():
    T,g,a,b,c = ring('g,a,b,c', QQ)
    w=g*a; v=g**3*b; k=g**4*c
    G2=v+w*k+w*w-w**3
    G3=2*w*G2+v
    G4=k-G2**2+2*w**4-2*w**5
    X1=-k+2*v-2*w+2*w*k+5*w*w-2*w**3+8*w**4-10*w**5
    S=[X1+g, G2+w*(X1+g), G3+w*w*(X1+g), G4+v*(X1+g)]
    E=[]
    for i,f in enumerate(S,1):
        assert min(m[0] for m in f)>=i
        E.append(T.from_dict({(m[0]-i,)+m[1:]:c0 for m,c0 in f.items()}))
    R,x,y,z1,z2,z3=ring('x,y,z1,z2,z3', QQ)
    v1=x*y; v2=x*x*z1; v3=x**3*z2; v4=x**4*z3
    stage=[1-29*v1+999*v1**2+355*v1*v2-41553*v1**3+v4,
           1+27*v1-5*v2,
           v1-12*v2+QQ(2128,5)*v1**2+v3,
           -4*v1-10*v2]
    powers=[{0:R.one} for _ in stage]
    for j in range(4):
        for n in range(1,max(max(m[j] for m in f) for f in E)+1):
            powers[j][n]=powers[j][n-1]*stage[j]
    out=[x*stage[0]]
    for i,e in enumerate(E,1):
        p=R.zero
        for m,co in e.items():
            term=R.ground_new(co)
            for j in range(4):term*=powers[j][m[j]]
            p+=term
        assert min(m[0] for m in p)>=i, ('divisibility failed',i)
        out.append(R.from_dict({(m[0]-i,)+m[1:]:co for m,co in p.items()}))
    return R,out

if __name__=='__main__':
    t=time.perf_counter();R,F=build_map()
    print('Construction seconds:',round(time.perf_counter()-t,3))
    for i,f in enumerate(F):
        print('Coordinate',i,'terms',len(f),'degree',max(map(sum,f)))
        section=R.from_dict({m:c for m,c in f.items() if m[0]==0})
        print(' x=0:',section)
    base=Path(__file__).resolve().parents[1] / 'data'
    base.mkdir(exist_ok=True)
    data=[[[list(m),str(c)] for m,c in sorted(f.items())] for f in F]
    (base/'map_coefficients.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    (base/'zero_section.txt').write_text('\n'.join(str(R.from_dict({m:c for m,c in f.items() if m[0]==0})) for f in F)+'\n')
