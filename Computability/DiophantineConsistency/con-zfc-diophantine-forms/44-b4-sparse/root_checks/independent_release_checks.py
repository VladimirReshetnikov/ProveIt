#!/usr/bin/env python3
"""Read-only independent release audit; writes only its own root_checks ledger.
This is finite data/circuit auditing, not a proof of universal equivalence.
"""
from pathlib import Path
from itertools import combinations_with_replacement, product
from collections import Counter
from math import comb, factorial, isqrt
import gzip, hashlib, json
ROOT=Path(__file__).resolve().parents[1]
checks={}

# Reconstruct the shifted sum of 22 squared quadratic residuals independently.
pfile=ROOT/'sun/sources/data/parent_quartic31.json'
parent=json.loads(pfile.read_text()); n=len(parent['variables']); whole={}
for equation in parent['equations']:
    residual={}
    for term in equation['terms']:
        ex=term['powers']
        active=[j for j in range(n) if ex[j]]
        for choices in product(*(range(ex[j]+1) for j in active)):
            key=list(ex); coeff=term['coefficient']
            for j,q in zip(active,choices):
                key[j]=q; coeff*=comb(ex[j],q)
            key=tuple(key); residual[key]=residual.get(key,0)+coeff
    residual={e:c for e,c in residual.items() if c}
    for e,c in residual.items():
        for f,d in residual.items():
            h=tuple(x+y for x,y in zip(e,f));whole[h]=whole.get(h,0)+c*d
whole={e:c for e,c in whole.items() if c}
weighted={}
for e,c in whole.items():
    alpha=(0,)+e[:n]
    mult=factorial(4-sum(alpha))
    for k in alpha:mult*=factorial(k)
    weighted.setdefault(alpha,{})[e[n:]]=c*mult
constants=json.loads((ROOT/'sun/sources/data/constants.json').read_text())
actual={tuple(r['alpha']):{tuple(q['powers']):q['coefficient'] for q in r['coefficient_polynomial_in_fixed_ports']} for r in constants['coefficient_records']}
assert weighted==actual and len(actual)==402
assert hashlib.sha256(pfile.read_bytes()).hexdigest()==constants['parent_sha256']
fifth=parent['equations'][4]
assert not any(any(t['powers'][n:]) for t in fifth['terms'])
assert sum(t['coefficient'] for t in fifth['terms'])==1
checks['parent']={'sha256':hashlib.sha256(pfile.read_bytes()).hexdigest(),'variables':n,'residuals':len(parent['equations']),'weighted_recipes':len(actual),'fifth_residual_at_ones':1}

# Authenticate the actual four-port tuple and prove the stated coefficient bound.
binding_path=ROOT/'sun/sources/data/coefficients_binding.json'
binding=json.loads(binding_path.read_text());bits={};portrows=[]
for row in binding['files']:
    p=binding_path.parent/(row['name']+'.bin.gz');compressed=p.read_bytes();raw=gzip.decompress(compressed)
    assert hashlib.sha256(compressed).hexdigest()==row['gzip_sha256']
    assert hashlib.sha256(raw).hexdigest()==row['sha256']
    assert len(raw)==row['bytes']
    bit=int.from_bytes(raw,'little').bit_length();assert bit==row['bit_length']
    bits[{'K':'K0','MF_source':'MF'}.get(row['name'],row['name'])]=bit
    portrows.append({'name':row['name'],'bit_length':bit,'sha256':row['sha256']})
bitlist=[bits[k] for k in constants['fixed_port_order']]
z=1<<4269855
for recipe in actual.values():
    upper=sum(abs(c)*(1<<sum(e*b for e,b in zip(ex,bitlist))) for ex,c in recipe.items())
    assert upper+1<z
assert (1<<4269877)>max(2*z*32**4,2048*z,8)
checks['fixed_ports']={'variant':binding['variant'],'ports':portrows,'all_402_bounds':True,'radix_scale_exponent':4269877,'signed_base_exponents':'1+2r, r>=0'}

# Exhaustively establish both integer and modular B4 separation.
wdata=json.loads((ROOT/'root_checks/bose_chowla_31_optimized.json').read_text());ws=wdata['weights_with_zero'];M=wdata['modulus']
sums=[sum(ws[i] for i in idx) for idx in combinations_with_replacement(range(len(ws)),4)]
assert len(sums)==len(set(sums))==len({s%M for s in sums})==52360
checks['B4']={'integer_sums':len(set(sums)),'modular_sums':len({s%M for s in sums}),'maximum_weight':max(ws)}

# Independently traverse saved circuits rather than trusting operation ledgers.
paths=['sun/generated/sun_b4.json','signed_audit/generated/signed13_b4.json','signed_audit/generated/signed14_b4.json','nine/generated/nine_b4_natural.json','nine/generated/nine_b4_positive.json']
expected={
 'sun/generated/sun_b4.json':(10,1407,113856*610895+27064),
 'signed_audit/generated/signed13_b4.json':(13,1409,370496*610895+84272),
 'signed_audit/generated/signed14_b4.json':(14,1420,370432*610895+84456),
 'nine/generated/nine_b4_natural.json':(9,1383,38176*610895+8744),
 'nine/generated/nine_b4_positive.json':(9,1378,38176*610895+8744)}
rows=[]
for path in paths:
    body=json.loads((ROOT/path).read_text());nodes=body['nodes'];seen=set();todo=[body['output']]
    while todo:
        i=todo.pop()
        if i in seen:continue
        assert 0<=i<len(nodes);seen.add(i);node=nodes[i]
        if node['kind'] in ('add','sub','mul'):
            assert 0<=node['left']<i and 0<=node['right']<i
            todo.extend((node['left'],node['right']))
        else:assert node['kind'] in ('variable','fixed','literal')
    assert len(seen)==len(nodes)
    counts=Counter(nodes[i]['kind'] for i in seen)
    assert [x['name'] for x in nodes if x['kind']=='variable']==body['variables']
    assert {k:counts[k] for k in ('add','sub','mul')}==body['operation_counts']
    assert (counts['variable'],sum(counts[k] for k in ('add','sub','mul')),body['exact_degree'])==expected[path]
    rows.append({'file':path,'variables':counts['variable'],'operations':sum(counts[k] for k in ('add','sub','mul')),'claimed_degree':body['exact_degree'],'sha256':hashlib.sha256((ROOT/path).read_bytes()).hexdigest()})
checks['circuits']=rows

# Explicitly inspect signed degenerate branches for the merger denominator.
count=0
for A,C,i in product(range(-8,9),repeat=3):
    J=4*A-5;D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1
    assert J*F!=0;count+=1
checks['signed_denominator_regression_assignments']=count

# Exhaustively check the two-square finalizer implication in a bounded signed domain.
count=zeros=0
for a0,a1 in product(range(-4,10),repeat=2):
    V0=isqrt(abs(a0))+1;V1=isqrt(abs(a1))+1
    V0=max(V0,2);V1=max(V1,2)
    for u,v,mu,nn in product(range(1,4),range(1,5),range(-2,3),range(0,8)):
        major=(v+u-1)//u;omega=u*(2*mu-1)
        theta=u*nn+v-omega*(major+V0*V1)
        f=(theta*theta-omega*omega*(a0+V0*V0*a1))**2-4*omega**4*V0*V0*a0*a1
        if f==0:
            zeros+=1
            assert a0>=0 and isqrt(a0)**2==a0 and a1>=0 and isqrt(a1)**2==a1
            assert v%u==0 and mu>0
        count+=1
checks['nine_finalizer_regression']={'assignments':count,'zeros_checked':zeros,'includes_zero_and_negative_radicands':True}

# Exact scaled-radix carry regression, independent of the released builder.
weights=(1,5);t=5;L=20;m=41;scale=1<<21
coeff={(0,0):5,(1,0):-2,(0,1):-4,(2,0):1,(0,2):1}
cs={ex:c*factorial(4-sum(ex))*factorial(ex[0])*factorial(ex[1]) for ex,c in coeff.items()}
assert scale>max(2*256*3**4,2048*256,8)
cases=0
for b in (2,4,8,16):
    B=scale*b**4;q0=B**(t+1);N=2*B**(9*t+2)
    dc=sum(c*B**(L-sum(a*w for a,w in zip(ex,weights))) for ex,c in cs.items())
    mask=q0-1-(b-1)*sum(B**w for w in weights)
    tc=(B-2)*B**L;offset=B*sum(B**j for j in range(m))
    for x,y in product(range(min(b,5)),repeat=2):
        g=x*B+y*B**5;jc=2*(1+g)**4*dc+offset
        assert 0<=g<q0 and 0<jc<2*B**m
        assert (g&mask)==0
        assert ((jc&tc)==0)==((x-1)**2+(y-2)**2==0)
        S=g+q0*jc;T=mask+q0*tc
        R=S*(N*N-N)+(T+1)*(N*N-1)
        assert 0<=S<N and 0<=T<N
        assert ((S&T)==0)==(R.bit_count()>=2*(N.bit_length()-1))
        cases+=1
checks['scaled_radix_exact_carry_cases']=cases

# Pinned source hashes remain intact; check the inherited proof link separately.
pinrows=[]
for manifest in ('sun/SOURCE_PINS.json','nine/SOURCE_PINS.json'):
    data=json.loads((ROOT/manifest).read_text())
    for row in data['files']:
        file=ROOT/row['package_relative_path'] if 'package_relative_path' in row else (ROOT/manifest).parent/row['file']
        assert file.is_file() and hashlib.sha256(file.read_bytes()).hexdigest()==row['sha256']
    pinrows.append({'manifest':manifest,'files':len(data['files']),'all_hashes_match':True})
checks['source_pins']=pinrows
ref=(binding_path.parent/binding['complete_interface_proof']).resolve()
checks['inherited_interface_reference']={'field':binding['complete_interface_proof'],'exists':ref.is_file(),'status':'Resolved by a local copied interface proof or explicit release dependency map; not a mathematical counterexample.'}
checks['status']='PASS finite data/degeneracy checks; scaled-radix freeze snapshot' if ref.is_file() else 'PASS finite checks; inherited reference requires release mapping'
checks['scope']='Independent finite data, topology and bounded degeneracy checks. Universal mathematics is reviewed separately. No consistency computation or end-to-end proof-assistant rebuild.'
output=ROOT/'root_checks/INDEPENDENT_RELEASE_CHECKS.json';output.write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks,indent=2))
