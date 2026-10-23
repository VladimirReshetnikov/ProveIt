#!/usr/bin/env python3
"""Finite exact audits; no proof-assistant endpoint or solvability test.
Degree-head and exact sparse digit checks adapted from pinned package27.
"""
from pathlib import Path
from collections import defaultdict
from random import Random
from math import isqrt
from hashlib import sha256
import importlib.util,json
import build_nine as b
ROOT=Path(__file__).resolve().parent
def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def coefficient_add(p, q, factor=1):
    r = dict(p)
    for a, c in q.items():
        r[a] = r.get(a, 0) + factor*c
        if not r[a]: del r[a]
    return r


def coefficient_mul(p, q):
    r = {}
    for a, c in p.items():
        for b, d in q.items():
            ex = dict(a)
            for k, v in b: ex[k] = ex.get(k, 0)+v
            key = tuple(sorted(ex.items()))
            r[key] = r.get(key, 0)+c*d
            if not r[key]: del r[key]
    return r


def diagonal_heads(body):
    """Exact leading coefficients over Z[the fixed-leaf symbols].

    A positive-degree cancellation would require more terms and is rejected.
    None occurs in the supplied circuits. Thus the final scalar leader proves
    the stated degree for every specialization of their fixed constants.
    """
    heads = []
    for idx, node in enumerate(body['nodes']):
        k = node['kind']
        if k == 'literal':
            value = node['value']
            out = (0, {(): value}) if value else (-1, {})
        elif k == 'fixed': out = (0, {((node['name'], 1),): 1})
        elif k == 'variable': out = (1, {(): 1})
        else:
            a, b = heads[node['left']], heads[node['right']]
            if k == 'mul':
                out = (-1, {}) if a[0] < 0 or b[0] < 0 else (a[0]+b[0], coefficient_mul(a[1], b[1]))
            else:
                factor = -1 if k == 'sub' else 1
                if a[0] > b[0]: out = a
                elif b[0] > a[0]: out = (b[0], {key: factor*v for key, v in b[1].items()})
                else:
                    coeff = coefficient_add(a[1], b[1], factor)
                    if not coeff:
                        require(a[0] <= 0 or (k == 'sub' and node['left'] == node['right']),
                                f'Unresolved leading cancellation at gate {idx}')
                        out = (-1, {})
                    else: out = (a[0], coeff)
        heads.append(out)
    output = heads[body['output']]
    require(set(output[1]) == {()}, 'Output leader is not coefficient independent')
    named = {}
    for name, idx in body['named_nodes'].items():
        degree, lc = heads[idx]
        named[name] = {'degree': degree,
                       'leading_coefficient': lc.get(()) if set(lc) == {()} else 'symbolic'}
    return output, named

def exact_digit_identity(nu,keys):
    d=b.DAG();B=d.var('B');z=d.fixed('z_index')
    q,ell,lam,e,top=b.coding_blocks(d,B,nu,keys,z)
    nodes,root,names=d.prune(e)
    # Sparse univariate B-polynomial with symbolic fixed coefficient monomials.
    vals=[]
    for node in nodes:
        k=node['kind']
        if k=='literal':r={(0,()):node['value']} if node['value'] else {}
        elif k=='variable':r={(1,()):1}
        elif k=='fixed':r={(0,(node['name'],)):1}
        else:
            a,right=vals[node['left']],vals[node['right']];r=defaultdict(int)
            if k=='mul':
                for (e,s),v in a.items():
                    for (f,t),w in right.items():r[(e+f,tuple(sorted(s+t)))]+=v*w
            else:
                for key,v in a.items():r[key]+=v
                for key,v in right.items():r[key]+=v*(1 if k=='add' else -1)
            r={k:v for k,v in r.items() if v}
        vals.append(r)
    L=5**(nu+1)
    expected={(L-b.expo(a),('z_index',)):1 for a in b.all_alphas(nu)}
    for a,name in keys:
        if isinstance(name,int):expected[(L-b.expo(a),())]=name
        else:expected[(L-b.expo(a),(name,))]=1
    assert vals[root]==expected
    return {'nu':nu,'baseline_positions':len(list(b.all_alphas(nu))),'symbolic_sparse_terms':len(expected),'status':'pass'}

def majorant_tests():
    count=0
    for R in range(-8,9):
      if not R:continue
      for U,Y in [(1,1),(1,3),(3,1),(4,2)]:
       for h,i,j in [(1,1,1),(2,3,1),(1,2,3)]:
        for r in range(13):
         sigma=Y*(U+1);A=R*sigma;C=2*R+1+r;H=(j+1)*C-r
         P=2*(R*Y)**2*U;K=R+1+h*(P-1);J=4*A-5
         D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1
         G=A+F*(C*D+1-A);I=(G*G-1)*H*H+1
         md=A*C+sigma*(r+1)**2+1;mf=A*E+1;ch=C*H+r*r
         mi=F*(D*ch+2*H*H+A*A)-A*A+1
         assert md>=abs(A*C)+1 and ch>=abs(C*H)
         assert md>=1 and mf>=1 and mi>=abs(G*H)+abs(H)+1
         assert md*md>=D and mf*mf>=F and mi*mi>=abs(I)
         a0=(P*P-1)*K*K+1;a1=D*F*I;V0=P*K+1;V1=md*mf*mi+1
         assert V0>=2 and V1>=2 and (V0-1)**2>=abs(a0) and (V1-1)**2>=abs(a1)
         count+=1
    return count

def norm(t,w,a0,a1,V0):
    return (t*t-w*w*(a0+V0*V0*a1))**2-4*w**4*V0*V0*a0*a1

def finalizer_tests():
    constructed=0;bounded=0
    for r0 in range(-3,4):
     for r1 in range(-3,4):
      a0,a1=r0*r0,r1*r1;V0,V1=abs(r0)+2,abs(r1)+2
      for u in [-7,-2,1,5]:
       for quotient in [-4,0,3]:
        for m in [1,2,4]:
         M=abs(quotient)+1;v=u*quotient;Z=2*M+V0*V1+r0+V0*r1
         n=(2*m-1)*Z-M-quotient;W=u*(2*m-1)
         T=u*(n+M)+v-W*(2*M+V0*V1)
         assert n>=0 and norm(T,W,a0,a1,V0)==0;constructed+=1
    for a0 in range(-2,6):
     for a1 in range(-2,6):
      for u in [-2,-1,1,2]:
       for v in range(-3,4):
        for m in [-1,0,1,2]:
         M=abs(v)+1;V0=abs(a0)+2;V1=abs(a1)+2;W=u*(2*m-1)
         for n in range(16):
          T=u*(n+M)+v-W*(2*M+V0*V1)
          if norm(T,W,a0,a1,V0)==0:
           assert a0>=0 and isqrt(a0)**2==a0 and a1>=0 and isqrt(a1)**2==a1 and v%u==0 and m>0
          bounded+=1
    return dict(constructed=constructed,bounded_soundness_cases=bounded)

def load_module(path,name):
    spec=importlib.util.spec_from_file_location(name,path);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def run():
    for row in json.loads((ROOT/'SOURCE_PINS.json').read_text())['sources']:
      assert sha256((ROOT/row['local']).read_bytes()).hexdigest()==row['sha256']
    constants=json.loads((ROOT/'source/30-quartic31/nine/nu31/COMPACT_CONSTANTS.json').read_text())
    parentpath=ROOT/'source/30-quartic31/arithmetic/quartic31.json'
    assert sha256(parentpath.read_bytes()).hexdigest()==constants['parent_sha256']
    parent=json.loads(parentpath.read_text());res,shift,total,grouped,weighted=b.build_parent(parent)
    recipes={tuple(row['alpha']):{tuple(t['powers']):t['coefficient'] for t in row['coefficient_polynomial_in_fixed_ports']} for row in constants['coefficient_records']}
    assert weighted==recipes and len(recipes)==402 and len(total)==675 and len(res)==22
    assert b.polynomial_value(res[4],[1]*31+[3,5,7,11])==1
    keys,aliases=b.canonical_coefficients(constants)
    byname={r['name']:r['coefficient_polynomial_in_fixed_ports'] for r in constants['coefficient_records']}
    for name,a in aliases.items():
      assert byname[name]==([dict(powers=[0]*4,coefficient=a['literal'])] if 'literal' in a else byname[a['fixed']])
    exact=exact_digit_identity(31,keys)
    bodies={name:json.loads((ROOT/'generated'/('nine_'+name+'.json')).read_text()) for name in ['structured_natural','structured_positive','sharp_natural','sharp_positive','sharp_degree_certificate']}
    certhead,named=diagonal_heads(bodies['sharp_degree_certificate']);assert certhead==(92324*5**32+296,{():2**196})
    structurehead,_=diagonal_heads(bodies['structured_natural']);assert structurehead==(93264*5**32+288,{():441*2**192})
    (ROOT/'generated/DEGREE_CERTIFICATE.json').write_text(json.dumps(dict(degree=certhead[0],leading_coefficient=certhead[1][()],named=named),indent=2)+'\n')
    ledger=json.loads((ROOT/'generated/ledger.json').read_text())
    for name,body in bodies.items():
      assert len([n for n in body['nodes'] if n['kind']=='variable'])==9
      for idx,n in enumerate(body['nodes']):
       if n['kind'] in ['add','sub','mul']:assert n['left']<idx and n['right']<idx
       else:assert n['kind'] in ['literal','variable','fixed']
      if name in ledger:assert sum(n['kind'] in ['add','sub','mul'] for n in body['nodes'])==ledger[name]['operations']
    manifest=json.loads((ROOT.parent/'coefficients/COMPACT_COEFFICIENT_BINDING.json').read_text())
    ports={}
    for row in manifest['files']:
      data=(ROOT.parent/'coefficients'/row['path']).read_bytes();assert sha256(data).hexdigest()==row['sha256'];value=int.from_bytes(data,'little');assert value.bit_length()==row['bit_length'];ports[row['name']]=value
    bb=[ports[k].bit_length() for k in ['beta','K','MC','MF_source']]
    for row in constants['coefficient_records']:
      bound=sum(abs(t['coefficient'])<<sum(a*c for a,c in zip(t['powers'],bb)) for t in row['coefficient_polynomial_in_fixed_ports'])
      assert bound+1<(1<<constants['index_exponent'])
    assert constants['index_exponent']==45933757
    rng=Random(9432151982);comparisons=0;shifts=0;namedchecks=0
    upstream=load_module(ROOT/'source/28-compact-norms/code/nine_structured.py','source28')
    generic=upstream.make_body(31,[(tuple(r['alpha']),r['name']) for r in constants['coefficient_records']],'structured')
    for p in [101,1009,1000003,1073741789]:
      vals=[ports[k]%p for k in ['beta','K','MC','MF_source']]
      fixed={name:b.polynomial_value({tuple(t['powers']):t['coefficient'] for t in recipe},vals,p) for name,recipe in byname.items()}
      z=pow(2,constants['index_exponent'],p)
      d=b.DAG();B=d.var('B');zz=d.fixed('z_index');q,ell,lam,e,top=b.coding_blocks(d,B,31,keys,zz);nodes,output,names=d.prune(e)
      coding={'nodes':nodes,'output':output,'named_nodes':names}
      fixed['z_index']=z
      y=b.evaluate_dag(coding,fixed,{'B':2*z},p)[0];fixed['y_index']=y
      literal=sum((z+fixed.get(r['name'],0))*pow(2*z,constants['L']-r['expo'],p) for r in constants['coefficient_records'])%p
      # Independent full index sum, including zero coefficient positions.
      coef={tuple(r['alpha']):fixed[r['name']] for r in constants['coefficient_records']}
      expected=sum((z+coef.get(a,0))*pow(2*z,constants['L']-b.expo(a),p) for a in b.all_alphas(31))%p
      assert y==expected
      for _ in range(16):
       v=[rng.randrange(p) for j in range(9)];natural=dict(zip(bodies['sharp_natural']['variables'],v))
       a,na=b.evaluate_dag(bodies['sharp_natural'],fixed,natural,p)
       c,nc=b.evaluate_dag(bodies['sharp_degree_certificate'],fixed,natural,p);assert a==c;comparisons+=1
       old,no=upstream.evaluate_dag(generic,fixed,natural,p);new,nn=b.evaluate_dag(bodies['structured_natural'],fixed,natural,p);assert old==new
       namedchecks+=len(no);assert all(nn[k]==x for k,x in no.items())
       for weight in ['structured','sharp']:
        nat=bodies[weight+'_natural'];pos=bodies[weight+'_positive']
        aa,_=b.evaluate_dag(nat,fixed,dict(zip(nat['variables'],v)),p)
        pp,_=b.evaluate_dag(pos,fixed,dict(zip(pos['variables'],[x+1 for x in v])),p)
        assert aa==pp;shifts+=1
    report=dict(status='PASS',weighted_coefficient_records=402,quartic_terms=675,aliases=len(aliases),exact_digit_identity=exact,index_bound_records=402,base_port_hashes=4,degree=certhead[0],leading_coefficient=certhead[1][()],actual_instance_certificate_comparisons=comparisons,actual_instance_source28_named_comparisons=namedchecks,positive_shift_comparisons=shifts,majorant_fixtures=majorant_tests(),finalizer=finalizer_tests(),scope='Finite algebra, count, degree and fixed-binding checks; not a solvability test or a new proof-assistant theorem.')
    (ROOT/'generated/VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':run()
