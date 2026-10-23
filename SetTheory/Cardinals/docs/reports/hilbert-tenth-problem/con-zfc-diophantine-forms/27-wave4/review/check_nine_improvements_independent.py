#!/usr/bin/env python3
"""Finite checks of Jones circuit optimization, shifts, and new root majorants."""
from pathlib import Path
import importlib.util,json,random,math
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/'nine/source/nine/nine_compressor.py'
spec=importlib.util.spec_from_file_location('upstream_nine',SRC);nc=importlib.util.module_from_spec(spec);spec.loader.exec_module(nc)

def run(body,fixed,variables,p):
    vals=[]
    for j,node in enumerate(body['nodes']):
        kind=node['kind']
        if kind=='literal':v=node['value']
        elif kind=='fixed':v=fixed[node['name']]
        elif kind=='variable':v=variables[node['name']]
        else:
            assert 0<=node['left']<j and 0<=node['right']<j
            a,b=vals[node['left']],vals[node['right']]
            v=a+b if kind=='add' else a-b if kind=='sub' else a*b
        vals.append(v%p)
    return vals[body['output']],{n:vals[j] for n,j in body['named_nodes'].items()}

def main():
    constants=json.loads((ROOT/'nine/source/nine/generated/constants.json').read_text())
    keys=[(tuple(c['alpha']),c['name']) for c in constants['coefficient_records']]
    rng=random.Random(927403);names=['epsilon','g0','h0','s0','w0','phi','i0','j0','n']
    posnames=['epsilon_plus','g','h','s','w','phi_plus','i','j','n_plus']
    out={'scope':'Finite algebra checks, not an unbounded compiler theorem.','same_polynomial':{},'positive_shifts':{},'majorant_fixtures':0,'finalizer_fixtures':0}
    for weight in ['literal','majorant','natural-majorant']:
        new=json.loads((ROOT/f'nine/generated/nine_{weight}_dag.json').read_text())
        positive=json.loads((ROOT/f'nine/generated/nine_{weight}_positive_dag.json').read_text())
        old=nc.make_body(32,keys,weight) if weight!='natural-majorant' else None
        for case in range(32):
            p=[1000000007,1000000009][case%2]
            fixed={n:rng.randrange(-p,p) for n in ['z_index','y_index']+[name for a,name in keys]}
            values={n:rng.randrange(-100,101) for n in names}
            if case<3:fixed['y_index']=-1-values['epsilon']+case # include B=0,1,32.
            a,an=run(new,fixed,values,p)
            if old:
                b,bn=run(old,fixed,values,p)
                assert a==b and an==bn
            b,bn=run(positive,fixed,{pos:values[nat]+1 for nat,pos in zip(names,posnames)},p)
            assert a==b and an==bn
        if old:out['same_polynomial'][weight]={'modular_fixtures':32,'old_operations':sum(n['kind'] in ['add','sub','mul'] for n in old['nodes']),'new_operations':sum(n['kind'] in ['add','sub','mul'] for n in new['nodes'])}
        out['positive_shifts'][weight]=32
    aliases=json.loads((ROOT/'nine/generated/COEFFICIENT_ALIASES.json').read_text())
    recipes={row['name']:{tuple(t['powers']):t['coefficient'] for t in row['coefficient_polynomial_in_fixed_ports']} for row in constants['coefficient_records']}
    assert len(aliases)==len(recipes)==346
    literal_records=0
    for name,alias in aliases.items():
        target={(0,0,0,0):alias['literal']} if 'literal' in alias else recipes[alias['fixed']]
        assert recipes[name]==target
        literal_records+=('literal' in alias)
    signatures={tuple(sorted(recipe.items())) for recipe in recipes.values()}
    assert literal_records==260 and len(signatures)==98
    out['exact_coefficient_aliases']={'records':346,'literal_records':260,'distinct_recipes':98,'all_equalities_checked_as_integer_polynomials':True}
    out['specialized_variants']={}
    for weight in ['literal','majorant','natural-majorant']:
      for positive in [False,True]:
        suffix='_positive' if positive else ''
        generic=json.loads((ROOT/f'nine/generated/nine_{weight}{suffix}_dag.json').read_text())
        folded=json.loads((ROOT/f'nine/generated/nine_{weight}_specialized{suffix}_dag.json').read_text())
        variables=[n['name'] for n in folded['nodes'] if n['kind']=='variable']
        assert len(set(variables))==len(variables)==9 and set(folded['variables'])==set(variables)
        assert sum(n['kind']=='fixed' for n in folded['nodes'])==66
        for case in range(32):
            prime=[1000000007,1000000009][case%2]
            ports=[rng.randrange(-50,51) for _ in range(4)]
            fixed={name:sum(coef*math.prod(pow(x,e,prime) for x,e in zip(ports,powers)) for powers,coef in recipe.items())%prime for name,recipe in recipes.items()}
            fixed.update(z_index=rng.randrange(prime),y_index=rng.randrange(prime))
            values={name:rng.randrange(-100,101) for name in variables}
            a,an=run(generic,fixed,values,prime);b,bn=run(folded,fixed,values,prime)
            assert a==b and an==bn
        count=sum(n['kind'] in ['add','sub','mul'] for n in folded['nodes'])
        out['specialized_variants'][weight+suffix]={'operations':count,'fixed_leaves':66,'modular_recipe_bound_comparisons':32}
    # Primitive semantic audit allows every packed-core nonnegative input,
    # not merely actual huge index values. The proof covers all such inputs.
    for case in range(256):
        b,B,q,ell,lam,e,N,z=[rng.randrange(0,6) for _ in range(8)]
        g,h,s,w,i,j=[rng.randrange(1,5) for _ in range(6)];phi=rng.randrange(5)
        left=g+e*q**3+ell*q**5+(2*(e-z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7
        right=q**3-b*ell+ell+(B-2*z)*lam*q**3+(B-2)*q**8
        R=left*(N*N-N)+right*(N*N-1)
        leftbar=g+e*q**3+ell*q**5+(2*(e+z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7
        rightbar=q**3+b*ell+ell+(B+2*z)*lam*q**3+(B+2)*q**8
        Rbar=leftbar*(N*N+N)+rightbar*(N*N+1)
        assert abs(R)<=Rbar
        U,Y=N*N*w,N*N*s;M,Mb=R*Y,Rbar*Y
        P,Pb=2*M*M*U,2*Mb*Mb*U
        K,Kb=R+1+h*(P-1),Rbar+1+h*(Pb+1)
        A,Ab=M*(U+1),Mb*(U+1)
        C,Cb=2*R+1+b*w+phi,2*Rbar+1+b*w+phi
        J,Jb=4*A-5,4*Ab+5
        D,Db=(A*A-1)*C*C+1,(Ab*Ab+1)*Cb*Cb+1
        E,Eb=i*J*D*C*C,i*Jb*Db*Cb*Cb
        F,Fb=(A*A-1)*E*E+1,(Ab*Ab+1)*Eb*Eb+1
        G,Gb=A+F*(C*D+1-A),Ab+Fb*(Cb*Db+1+Ab)
        H,Hb=2*R+1+j*C,2*Rbar+1+j*Cb
        for a,abar in [(P,Pb),(K,Kb),(A,Ab),(C,Cb),(D,Db),(E,Eb),(F,Fb),(G,Gb),(H,Hb)]:assert abar>=abs(a)
        I=(G*G-1)*H*H+1;a0=(P*P-1)*K*K+1;a1=D*F*I
        V0=(Pb+1)*Kb+2;V1=2*((Ab+1)*Cb+1)*((Ab+1)*Eb+1)*((Gb+1)*Hb+1)+1
        assert V0>=2 and V1>=2 and abs(a0)<=(V0-1)**2 and abs(a1)<=(V1-1)**2
        assert J!=0 and F!=0
        out['majorant_fixtures']+=1
    for _ in range(1000):
        r0,r1=rng.randrange(-8,9),rng.randrange(-8,9)
        a0,a1=r0*r0,r1*r1;V0=abs(r0)+2;V1=abs(r1)+2
        d=rng.randrange(1,9);c=d*rng.randrange(8);m=rng.randrange(1,9)
        Z=c+V0*V1+r0+V0*r1;n=(2*m-1)*Z-c//d
        assert n>=1
        Om=d*(2*m-1);Th=d*n+c-Om*(c+V0*V1)
        val=(Th*Th-Om*Om*(a0+V0*V0*a1))**2-4*Om**4*V0*V0*a0*a1
        assert val==0;out['finalizer_fixtures']+=1
    (ROOT/'review/NINE_IMPROVEMENTS_INDEPENDENT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
