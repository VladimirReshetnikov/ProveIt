#!/usr/bin/env python3
"""Literal natural-selector source; Python standard library only.

This emits a LOCAL degree-14 relation, not a fixed Con(ZFC) equation.
All coefficients and source rows are supplied, no external code is imported.
"""
from pathlib import Path
from itertools import product
from collections import defaultdict
import json, hashlib, math

HERE=Path(__file__).resolve().parent
def require(b, msg):
    if not b: raise RuntimeError(msg)
def norm(p): return {m:c for m,c in p.items() if c}
def plus(a,b):
    d=dict(a)
    for m,c in b.items(): d[m]=d.get(m,0)+c
    return norm(d)
def neg(a): return {m:-c for m,c in a.items()}
def minus(a,b): return plus(a,neg(b))
def mul(a,b):
    d=defaultdict(int)
    for ma,ca in a.items():
        for mb,cb in b.items(): d[tuple(sorted(ma+mb))]+=ca*cb
    return norm(d)
def var(x): return {(x,):1}
def const(c): return {():c} if c else {}
def power(a,n):
    b=const(1)
    for _ in range(n): b=mul(b,a)
    return b
def prod(xs):
    r=const(1)
    for x in xs:r=mul(r,x)
    return r
def read_poly(rows):
    r={}
    for row in rows:r=plus(r,{tuple(sorted(row['monomial'])):int(row['coefficient'])})
    return r
def rows(p):return [{'monomial':list(m),'coefficient':str(c)} for m,c in sorted(p.items())]
def ev(p,v):return sum(c*math.prod(v[x] for x in m) for m,c in p.items())
def degree(p):return max((len(m) for m in p),default=0)
def save(n,v):(HERE/n).write_text(json.dumps(v,indent=2)+'\n')

src_path=HERE/'horn_shared_source.json'
src=json.loads(src_path.read_text())
source_hash=hashlib.sha256(src_path.read_bytes()).hexdigest()
require(source_hash=='bef85fcf1fbd70fc109162b5b518fe7c4803a54864c867c64f3e6ea7e3be71cf','Unexpected source bytes')
hs=[]
for i,b in enumerate(src['branches']):
    h={}
    for rr in b['quadratic_residuals']: h=plus(h,power(read_poly(rr),2))
    require(h==read_poly(b['sum_of_squares']),f'SOS expansion mismatch {i}')
    require(degree(h)==b['degree'],f'Degree mismatch {i}')
    hs.append(h)
require(hs[0]==plus(plus(power(var('p'),2),power(var('q'),2)),power(var('v'),2)),'Truth is not the zero triple')

# Eleven non-stuttering branches, six groups of degree exactly eight.
groups=[[9],[1,2],[3,4],[5,6],[7,8],[10,11]]
gs=[prod(hs[j] for j in group) for group in groups]
require([degree(g) for g in gs]==[8]*6,'Unexpected group degree')
k=6
r=var('r')
g=prod(minus(r,const(j)) for j in range(k))
ws=[]
for i in range(k):
    w=prod(minus(r,const(j)) for j in range(k) if j!=i)
    if (k-1-i)%2:w=mul(w,minus(r,const(k)))
    ws.append(w)
require([degree(w) for w in ws]==[6,5,6,5,6,5],'Weight degrees')
horn=dict(g)
for gi,wi in zip(gs,ws):horn=plus(horn,mul(gi,wi))

S,Sp,R,Rp,M0,p,q,v=[var(x) for x in ['S','Sp','R','Rp','M0','p','q','v']]
M=plus(M0,const(1))
E=minus(mul(Sp,plus(const(1),mul(v,M))),prod([S,plus(const(1),mul(p,M)),plus(const(1),mul(q,M))]))
F=minus(Rp,mul(R,plus(mul(plus(const(1),p),plus(const(1),q)),v)))
local=plus(horn,plus(power(E,2),power(F,2)))
require(degree(horn)==degree(local)==14,'Exact degree14 failed')
vars20=['p','q','v','a','b','c','d']+['q'+str(j) for j in range(13)]
all_vars=['S','Sp','R','Rp','M0']+vars20+['r']
require(set(x for m in local for x in m)==set(all_vars),'Unexpected support')

# A direct sparse coefficient certificate for the exact degree.
highest={m:c for m,c in local.items() if len(m)==14}
point={x:1 for x in all_vars}
leading_at_ones=ev(highest,point)
require(leading_at_ones>0,'Degree witness at all ones is not positive')
save('height_selector14.json',{
 'status':'complete local polynomial, uncompiled global bounded closure',
 'domain':'all variables are nonnegative integers; subtraction is integer subtraction',
 'exposed_coordinates':all_vars[:5], 'witnesses':vars20+['r'],
 'witness_count':21,'total_variables':26,'exact_degree':14,
 'source_sha256':source_hash,'source_file':'horn_shared_source.json',
 'branch_groups':groups,'omitted_branch':{'index':0,'name':'truth','justification':'p=q=v=0 makes both accumulator updates identities; delete these steps from a finite certificate'},
 'selector_domain_polynomial':rows(g),'selector_weights':[rows(w) for w in ws],
 'formula':'g(r)+sum_i W_i(r)*product_{j in groups[i]} h_j+E^2+F^2',
 'E':rows(E),'F':rows(F),
 'exact_degree_certificate':{'leading_homogeneous_value_at_all_variables_one':str(leading_at_ones),'leading_term_count':len(highest)},
 'expanded_monomials':len(local)
})
save('height_selector14_expanded.json',{'variables':all_vars,'degree':14,'terms':rows(local)})

# A second Pareto point: two ternary selectors, 22 witnesses, degree12.
# Three degree-eight groups are placed at low-degree corner weights;
# the six remaining groups are individual degree-four Horn factors.
u,w=var('u'),var('w')
def ternary_weights(x):
    return [mul(minus(x,const(1)),minus(x,const(2))),
            prod([x,minus(x,const(2)),minus(x,const(3))]),
            mul(x,minus(x,const(1)))]
us,vs=ternary_weights(u),ternary_weights(w)
grid=[[[9],[5],[1,2]],[[6],[7],[8]],[[3,4],[10],[11]]]
ggu=prod(minus(u,const(j)) for j in range(3))
ggv=prod(minus(w,const(j)) for j in range(3))
horn12=plus(ggu,ggv)
for ii in range(3):
    for jj in range(3):
        gi=prod(hs[j] for j in grid[ii][jj])
        horn12=plus(horn12,prod([gi,us[ii],vs[jj]]))
local12=plus(horn12,plus(power(E,2),power(F,2)))
variables12=all_vars[:5]+vars20+['u','w']
require(degree(local12)==12,'Exact degree12 failed')
require(set(x for m in local12 for x in m)==set(variables12),'Degree12 support')
top12={m:c for m,c in local12.items() if len(m)==12}
lead12=ev(top12,{x:1 for x in variables12})
require(lead12>0,'Degree12 positive certificate')
save('height_selector12.json',{
 'status':'complete local polynomial, uncompiled global bounded closure',
 'domain':'all variables are nonnegative integers; subtraction is integer subtraction',
 'exposed_coordinates':variables12[:5],'witnesses':vars20+['u','w'],
 'witness_count':22,'total_variables':27,'exact_degree':12,
 'source_sha256':source_hash,'source_file':'horn_shared_source.json',
 'branch_grid':grid,'omitted_branch':0,
 'selector_domain_polynomials':[rows(ggu),rows(ggv)],
 'u_weights':[rows(x) for x in us],'w_weights':[rows(x) for x in vs],
 'formula':'g3(u)+g3(w)+sum_i sum_j U_i(u)*U_j(w)*product_{h in grid[i][j]} h + E^2+F^2',
 'E':rows(E),'F':rows(F),'expanded_monomials':len(local12),
 'exact_degree_certificate':{'leading_homogeneous_value_at_all_variables_one':str(lead12),'leading_term_count':len(top12)}
})
save('height_selector12_expanded.json',{'variables':variables12,'degree':12,'terms':rows(local12)})

# Finite controls accompany the proof; they are not its replacement.
controls=0
for kk in range(1,15):
    for rr in range(50):
        gg=math.prod(rr-j for j in range(kk))
        require(gg>=0,'selector domain sign')
        require((gg==0)==(rr<kk),'selector domain roots')
        for ii in range(kk):
            ww=math.prod(rr-j for j in range(kk) if j!=ii)
            if (kk-1-ii)%2:ww*=rr-kk
            require(ww>=0,'selector weight sign')
            if rr<kk: require((ww>0)==(rr==ii),'selector delta')
            controls+=1
for values in product(range(3),repeat=k):
    found=False
    for rr in range(11):
        value=ev(g,{'r':rr})+sum(z*ev(w,{'r':rr}) for z,w in zip(values,ws))
        require(value>=0,'selector aggregation sign')
        if value==0:
            require(rr<k and values[rr]==0,'selector soundness')
            found=True
        controls+=1
    require(found==(0 in values),'selector completeness')

grid_controls=0
for zero_cell in range(10):
    gg=[0 if j==zero_cell else j+1 for j in range(9)]
    found=False
    for uu,ww in product(range(9),repeat=2):
        assignment={'u':uu,'w':ww}
        out=ev(ggu,assignment)+ev(ggv,assignment)
        out+=sum(gg[3*ii+jj]*ev(us[ii],assignment)*ev(vs[jj],assignment) for ii in range(3) for jj in range(3))
        require(out>=0,'grid positivity')
        if out==0:
            require(uu<3 and ww<3 and gg[3*uu+ww]==0,'grid soundness')
            found=True
        grid_controls+=1
    require(found==(zero_cell<9),'grid completeness')

# Arbitrary stuttering update: all unused Horn wires may vary.
for ss,rr,mm in product(range(1,8),range(1,8),range(8)):
    values={x:0 for x in all_vars}
    values.update(S=ss,Sp=ss,R=rr,Rp=rr,M0=mm)
    require(ev(E,values)==ev(F,values)==0,'truth stutter update')
    controls+=1

# Negative control: parity adjustment really matters.
bad_raw=math.prod(0-j for j in range(6) if j!=0)
require(bad_raw<0,'raw Lagrange counterexample')
save('CHECKS.json',{'status':'PASS','scope':'exact sparse polynomial/SOS/degree checks and finite selector controls; no global Con(ZFC) polynomial counted',
 'source_sha256':source_hash,'all_12_source_sos_expansions_verified':True,
 'selector_numeric_controls':controls,'new_local_witnesses':21,'old_local_witnesses':23,
 'new_local_degree':14,'old_local_degree':14,'expanded_monomials':len(local),
 'degree14_leading_value_at_ones':str(leading_at_ones),
 'degree12_variant':{'local_witnesses':22,'degree':12,'monomials':len(local12),'degree_certificate':str(lead12),'grid_controls':grid_controls},
 'conditional_index_free_closure_coordinate_saving':'4+2*b, where b is the internal-witness count of the exact binomial graph; excludes changes caused by source polynomial complexity',
 'negative_control_raw_weight_at_zero':bad_raw})
print(json.dumps({'status':'PASS','variants':[{'degree':14,'witnesses':21,'monomials':len(local),'leading_coefficient_at_ones':str(leading_at_ones)},{'degree':12,'witnesses':22,'monomials':len(local12),'leading_coefficient_at_ones':str(lead12)}],'controls':controls+grid_controls},indent=2))
