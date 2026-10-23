#!/usr/bin/env python3
"""Finite exact and modular checks; does not certify the imported semantic chain."""
from pathlib import Path
from collections import defaultdict
from random import Random
from math import isqrt
from hashlib import sha256,sha1
import json,sys
import build_improved as imp
nc=imp.nc;check=imp.check;ROOT=Path(__file__).resolve().parent

def exact_digit_identity(nu,keys):
    d=nc.DAG();B=d.var('B');z=d.fixed('z_index')
    q,ell,lam,e,top=imp.coding_blocks(d,B,nu,keys,z)
    nodes,root,names=d.prune(e)
    # Sparse univariate B-polynomial with symbolic fixed coefficient monomials.
    vals=[]
    for node in nodes:
        k=node['kind']
        if k=='literal':r={(0,()):node['value']} if node['value'] else {}
        elif k=='variable':r={(1,()):1}
        elif k=='fixed':r={(0,(node['name'],)):1}
        else:
            a,b=vals[node['left']],vals[node['right']];r=defaultdict(int)
            if k=='mul':
                for (e,s),v in a.items():
                    for (f,t),w in b.items():r[(e+f,tuple(sorted(s+t)))]+=v*w
            else:
                for key,v in a.items():r[key]+=v
                for key,v in b.items():r[key]+=v*(1 if k=='add' else -1)
            r={k:v for k,v in r.items() if v}
        vals.append(r)
    L=5**(nu+1)
    expected={(L-nc.expo(a),('z_index',)):1 for a in nc.all_alphas(nu)}
    for a,name in keys:
        if isinstance(name,int):expected[(L-nc.expo(a),())]=name
        else:expected[(L-nc.expo(a),(name,))]=1
    assert vals[root]==expected
    return {'nu':nu,'baseline_positions':len(list(nc.all_alphas(nu))),'symbolic_sparse_terms':len(expected),'status':'pass'}

def modular_equivalence(keys):
    rng=Random(94320261023);count=0;positive_count=0
    for weight in ['literal','majorant']:
        old=nc.make_body(32,keys,weight);new=imp.make_body(32,keys,weight)
        for p in [101,1009,1000003,1073741789]:
            for _ in range(20):
                fixed={n['name']:rng.randrange(p) for n in old['nodes'] if n['kind']=='fixed'}
                v={name:rng.randrange(p) for name in old['variables']}
                a,na=nc.evaluate_dag(old,fixed,v,p);b,nb=nc.evaluate_dag(new,fixed,v,p)
                assert a==b
                assert all(nb[name]==value for name,value in na.items())
                count+=1
    for weight in ['literal','majorant','natural-majorant']:
        natural=imp.make_body(32,keys,weight);positive=imp.make_body(32,keys,weight,True)
        for p in [101,1009,1000003]:
            for _ in range(20):
                fixed={n['name']:rng.randrange(p) for n in natural['nodes'] if n['kind']=='fixed'}
                v=[rng.randrange(p) for _ in range(9)]
                got,_=nc.evaluate_dag(natural,fixed,dict(zip(natural['variables'],v)),p)
                want,_=nc.evaluate_dag(positive,fixed,dict(zip(positive['variables'],[x+1 for x in v])),p)
                assert got==want;positive_count+=1
    return count,positive_count

def sign_erasure_checks():
    rng=Random(215943);count=0
    for _ in range(1000):
        # Independent positive inputs to the packed R formula; not restricted to digit values.
        e,z,lam,B,b,g,h,s,w,phi,i,j,q,N=[rng.randrange(1,8) for _ in range(14)]
        ell=rng.randrange(8)
        R=(g+e*q**3+ell*q**5+(2*(e-z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7)*(N*N-N)+(q**3-b*ell+ell+(B-2*z)*lam*q**3+(B-2)*q**8)*(N*N-1)
        Rb=(g+e*q**3+ell*q**5+(2*(e+z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7)*(N*N+N)+(q**3+b*ell+ell+(B+2*z)*lam*q**3+(B+2)*q**8)*(N*N+1)
        assert Rb>=abs(R)
        U,Y=N*N*w,N*N*s
        M=R*Y;Mb=Rb*Y;P=2*M*M*U;Pb=2*Mb*Mb*U
        K=R+1+h*(P-1);Kb=Rb+1+h*(Pb+1)
        A=M*(U+1);Ab=Mb*(U+1)
        Bp=2*R+1;Bpb=2*Rb+1
        C=Bp+b*w+phi;Cb=Bpb+b*w+phi
        J=4*A-5;Jb=4*Ab+5
        D=(A*A-1)*C*C+1;Db=(Ab*Ab+1)*Cb*Cb+1
        E=i*J*D*C*C;Eb=i*Jb*Db*Cb*Cb
        F=(A*A-1)*E*E+1;Fb=(Ab*Ab+1)*Eb*Eb+1
        Gp=A+F*(C*D+1-A);Gb=Ab+Fb*(Cb*Db+1+Ab)
        H=Bp+j*C;Hb=Bpb+j*Cb
        assert all(bar>=abs(x) for x,bar in [(M,Mb),(P,Pb),(K,Kb),(A,Ab),(C,Cb),(D,Db),(E,Eb),(F,Fb),(Gp,Gb),(H,Hb)])
        a0=(P*P-1)*K*K+1;a1=D*F*((Gp*Gp-1)*H*H+1)
        V0=(Pb+1)*Kb+2;V1=2*((Ab+1)*Cb+1)*((Ab+1)*Eb+1)*((Gb+1)*Hb+1)+1
        assert V0>=2 and V1>=2 and (V0-1)**2>=abs(a0) and (V1-1)**2>=abs(a1)
        count+=1
    # The elementary new inequality checked exactly as a polynomial identity.
    c,x,pow,scale,minus=check.sparse_ring(2);a,b=x(0),x(1)
    candidate=nc.add(nc.mul(nc.add(a,c(1)),b),c(1))
    bound=nc.add(nc.mul(nc.add(pow(a,2),c(1)),pow(b,2)),c(1))
    diff=minus(pow(candidate,2),bound)
    expected=nc.add(scale(nc.mul(a,pow(b,2)),2),scale(nc.mul(nc.add(a,c(1)),b),2))
    assert diff==expected and all(v>=0 for v in diff.values())
    return count,len(diff)

def finalizer_checks():
    count=0
    for u in range(6):
        for v in range(6):
            for d in [1,2,7]:
                for quotient in [0,1,3]:
                    for margin in [1,2,5]:
                        a0,a1=u*u,v*v;V0=u+2;V1=2*v+2;c=d*quotient
                        Z=c+V0*V1-u-V0*v
                        n=(2*margin-1)*Z-quotient
                        assert n>=0
                        W=d*(2*margin-1);T=d*n+c-W*(c+V0*V1)
                        assert (T*T-W*W*(a0+V0*V0*a1))**2-4*W**4*V0*V0*a0*a1==0
                        count+=1
    return count

def main():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for row in pins['sources']:
        data=(ROOT/row['local']).read_bytes()
        assert sha256(data).hexdigest()==row['sha256']
        assert sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob_sha']
    constants=json.loads((ROOT/'source/nine/generated/constants.json').read_text())
    parent_path=ROOT/'source/base/quartic32.upstream.json'
    assert sha256(parent_path.read_bytes()).hexdigest()==constants['parent_sha256']
    parent=json.loads(parent_path.read_text())
    weighted=nc.build_parent(parent)[4]
    recipes={tuple(row['alpha']):{tuple(r['powers']):r['coefficient'] for r in row['coefficient_polynomial_in_fixed_ports']} for row in constants['coefficient_records']}
    assert weighted==recipes
    keys=[(tuple(c['alpha']),c['name']) for c in constants['coefficient_records']]
    exact=exact_digit_identity(32,keys)
    specialized_keys,aliases=imp.canonical_coefficients(constants)
    exact_specialized=exact_digit_identity(32,specialized_keys)
    recipes={row['name']:row['coefficient_polynomial_in_fixed_ports'] for row in constants['coefficient_records']}
    for name,alias in aliases.items():
        if 'literal' in alias:assert recipes[name]==[{'powers':[0]*4,'coefficient':alias['literal']}]
        else:assert recipes[name]==recipes[alias['fixed']]
    modular,positive=modular_equivalence(keys)
    majorants,identityterms=sign_erasure_checks()
    ledger=json.loads((ROOT/'generated/ledger.json').read_text())
    assert ledger['natural-majorant']['degree']==120764*5**33+368
    assert ledger['natural-majorant']['leading_coefficient']==9*2**252
    for key,expected in [('literal',1609),('majorant',1616),('natural-majorant',1673),('literal_positive',1604),('majorant_positive',1611),('natural-majorant_positive',1668)]:assert ledger[key]['operations']==expected
    report={'status':'pass','authenticated_pinned_sources':len(pins['sources']),'exact_symbolic_digit_identity':exact,'exact_specialized_digit_identity':exact_specialized,'coefficient_alias_identities':len(aliases),'regenerated_weighted_coefficient_records':len(weighted),'old_new_modular_full_DAG_comparisons':modular,
            'positive_shift_modular_comparisons':positive,'sign_erased_majorant_test_assignments':majorants,
            'exact_new_majorant_identity_terms':identityterms,'constructed_finalizer_witnesses':finalizer_checks(),
            'exact_norm_identity_terms':check.norm_identity(),
            'scope':'Exact finite algebraic and degree checks plus modular implementation tests. No solvability or consistency test; no new Lean/Rocq compilation.',
            'inputs':{p.name:sha256(p.read_bytes()).hexdigest() for p in [ROOT/'build_improved.py',ROOT/'source/nine/nine_compressor.py',ROOT/'source/nine/check_nine.py',ROOT/'source/nine/generated/constants.json']}}
    (ROOT/'generated/VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
