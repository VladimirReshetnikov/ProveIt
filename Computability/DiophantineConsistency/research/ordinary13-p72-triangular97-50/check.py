#!/usr/bin/env python3
"""Check a P13 triangular residual transform, graph, and actual-port degree ray."""
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
P72 = ROOT / 'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
def read_pinned(path, digest):
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == digest, path
    return raw
original = json.loads(read_pinned(P72/'p13_degree28.json','1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49'))
binding = json.loads(read_pinned(P72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
read_pinned(P72/'PROOF13.md','8fedebfd59e18d25bb7e08f607e5e57be2386a3492fd8da31b6f25a1e6caf2c5')
graph_sha = '16bfa31fbc1ed5dee7d30fe79b8c91d123dba8195934bd01d1231356c1114198'
g = json.loads(read_pinned(HERE/'polynomial.json',graph_sha))
new_tail = [['g85','*','Delta','g25'],['ysum','+','yhat','Vhat'],['g87','*','g81','ysum'],['g88','*','g85','g87'],['g89','-','yhat2','g88'],['Aa','-','g89','L2']]
assert g['source'] == original['source'][:84]+new_tail+original['source'][91:]
assert g['witnesses'] == original['witnesses'] and len(g['witnesses']) == 13
assert g['fixed_ports'] == original['fixed_ports'] and g['residuals'] == original['residuals']
assert g['derived_fixed_leaves'] == dict(original['derived_fixed_leaves'], L2=['*','L','L'])
assert g['parent_sha256'] == '1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49'
rows=g['source']; assert len(rows)==97
by_name={row[0]:row for row in rows}; assert len(by_name)==97
for row in [['g24','*','I','I'],['g25','*','Delta','g24'],['g26','*','b2','g25'],['As','-','f2m','g26'],['g81','*','L','u'],['yhat','+','Vhat','g81'],['yhat2','*','yhat','yhat']]:
    assert by_name[row[0]]==row
# Ordered construction, and all 97 rows and 13 witnesses live at the output.
available=set(g['witnesses']+g['fixed_ports']+list(g['derived_fixed_leaves']))
for n,op,a,b in rows:
    assert n not in available and op in ('+','-','*')
    assert all(isinstance(x,int) or x in available for x in (a,b))
    available.add(n)
needed={g['output']}
for n,op,a,b in reversed(rows):
    if n in needed: needed.update((a,b))
assert all(n in needed for n,_,_,_ in rows)
assert all(x in needed for x in g['witnesses']+g['fixed_ports'])
counts=dict(sorted(Counter(r[1] for r in rows).items()))

# Exact sparse-polynomial identity using independent cuts (not random testing).
def var(x): return {(x,):1}
def plus(a,b):
    z=dict(a)
    for m,c in b.items(): z[m]=z.get(m,0)+c
    return {m:c for m,c in z.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def sub(a,b):return plus(a,neg(b))
def mul(a,b):
    z={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            m=tuple(sorted(ma+mb));z[m]=z.get(m,0)+ca*cb
    return {m:c for m,c in z.items() if c}
d,fm,b2,ii,y,v,L,t=map(var,['delta','f2m','b2','I2','yhat','Vhat','L','t'])
gap=sub(mul(y,y),mul(v,v))
As=sub(fm,mul(mul(b2,d),ii))
Aa=sub(sub(mul(b2,mul(y,y)),mul(mul(d,fm),gap)),mul(b2,mul(L,L)))
Anew=sub(sub(mul(y,y),mul(mul(mul(d,d),ii),gap)),mul(L,L))
assert mul(b2,Anew)==plus(Aa,mul(mul(d,gap),As))
# With yhat=Vhat+t, the factored gap is identically yhat²−Vhat².
yv=plus(v,t)
assert sub(mul(yv,yv),mul(v,v)) == mul(t,plus(yv,v))

# Independently propagate an upper bound through every proposed operation.
deg={x:1 for x in g['witnesses']}
deg.update({x:0 for x in g['fixed_ports']+list(g['derived_fixed_leaves'])})
def degree(x):return 0 if isinstance(x,int) else deg[x]
for n,op,a,b in rows:
    deg[n]=degree(a)+degree(b) if op=='*' else max(degree(a),degree(b))
assert {x:deg[x] for x in ['g87','Aa','As',g['output']]} == {'g87':7,'Aa':25,'As':14,g['output']:50}

# Load exact, hash-authenticated little-endian port bytes; beta identity is checked.
prime=1000000007
port_mod={}
for name,meta in binding['ports'].items():
    packed=read_pinned(P72/meta['path'],meta['sha256_gzip'])
    raw=gzip.decompress(packed)
    assert len(raw)==meta['raw_bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256_raw']
    value=int.from_bytes(raw,'little')
    assert value>0 and value.bit_length()==meta['bits']
    if name=='beta': assert value==(1<<590069)-1
    port_mod[name]=value%prime
beta=port_mod['beta']; b=3*beta%prime;b2v=b*b%prime;Lval=beta*b2v%prime
fixed={**port_mod,'B':(beta+1)%prime,'b':b,'b2':b2v,'L':Lval,'L2':Lval*Lval%prime,'Kfinal':b2v*Lval*Lval%prime,'four_beta':4*beta%prime}
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b,sgn):return trim([((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mult(a,b):
    z=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y0 in enumerate(b):z[i+j]=(z[i+j]+x*y0)%prime
    return trim(z)
vals={x:[0,1] for x in g['witnesses']};vals.update({x:[v0] for x,v0 in fixed.items()})
def value(x):return [x%prime] if isinstance(x,int) else vals[x]
for n,op,a,b0 in rows:
    vals[n]=mult(value(a),value(b0)) if op=='*' else add(value(a),value(b0),1 if op=='+' else -1)
lead=vals[g['output']][-1]
assert len(vals[g['output']])-1 == 50 and lead == 148237445
assert len(vals['Aa'])-1 == 25 and vals['Aa'][-1] == 370278151
assert vals['Aa'][-1] == (1728*beta*Lval*(b+3)**2)%prime
# The 96-gate variant moves Delta*c² earlier and scales the strong residual.
sha96='957d0a60112a67222a8ae576d3304e400ce20493b54a159918c6a947a814d758'
g96=json.loads(read_pinned(HERE/'polynomial96.json',sha96))
pre=[['g71','*','Delta','c2'],['j','*','i','g71'],['g85','*','j','j'],['sf','*','Delta','f2m'],['sg','*','b2','g85'],['As','-','sf','sg']]
rows96=rows[:23]+pre+[row for row in rows[28:] if row[0] not in ('g71','g85')]
assert g96['source']==rows96 and len(rows96)==96
assert g96['witnesses']==g['witnesses'] and g96['fixed_ports']==g['fixed_ports']
assert g96['derived_fixed_leaves']==g['derived_fixed_leaves'] and g96['output']==g['output']
ready=set(g96['witnesses']+g96['fixed_ports']+list(g96['derived_fixed_leaves']))
deg96={x:1 for x in g96['witnesses']};deg96.update({x:0 for x in g96['fixed_ports']+list(g96['derived_fixed_leaves'])})
for n,op,x,y0 in rows96:
    assert n not in ready and op in ('+','-','*')
    assert all(isinstance(z,int) or z in ready for z in (x,y0))
    f=lambda z:0 if isinstance(z,int) else deg96[z]
    deg96[n]=f(x)+f(y0) if op=='*' else max(f(x),f(y0));ready.add(n)
needed96={g96['output']}
for n,op,x,y0 in reversed(rows96):
    if n in needed96:needed96.update((x,y0))
assert all(n in needed96 for n,_,_,_ in rows96)
assert all(x in needed96 for x in g96['witnesses']+g96['fixed_ports'])
assert {x:deg96[x] for x in ['g87','Aa','As',g96['output']]}=={'g87':7,'Aa':25,'As':18,g96['output']:50}
# Check As_new = Delta*As_old exactly in an independent polynomial ring.
ci,mi=var('c2'),var('i')
old_strong=sub(fm,mul(mul(b2,d),mul(mul(mi,ci),mul(mi,ci))))
j=mul(mul(mi,d),ci)
new_strong=sub(mul(d,fm),mul(b2,mul(j,j)))
assert new_strong==mul(d,old_strong)
# The 96-gate univariate ray evaluates all actual port bytes again.
vals={x:[0,1] for x in g96['witnesses']};vals.update({x:[v0] for x,v0 in fixed.items()})
for n,op,a,b0 in rows96:
    vals[n]=mult(value(a),value(b0)) if op=='*' else add(value(a),value(b0),1 if op=='+' else -1)
assert len(vals[g96['output']])-1==50 and vals[g96['output']][-1]==148237445
assert len(vals['Aa'])-1==25 and vals['Aa'][-1]==370278151
counts96=dict(sorted(Counter(r[1] for r in rows96).items()))
print(json.dumps({'status':'PASS','parent_sha256':g['parent_sha256'],'graph_sha256':graph_sha,'operations':len(rows),'operation_counts':counts,'live_gates':len(rows),'witnesses':len(g['witnesses']),'new_fixed_leaf':'L2 = L*L, precomputed from source ports','triangular_identity':'b2*Aa_new = Aa_old + Delta*(yhat^2-Vhat^2)*As','degree_upper':deg[g['output']],'ray_modulus':prime,'ray_degree':len(vals[g['output']])-1,'ray_leading_coefficient':lead,'aux_ray_leading_coefficient':vals['Aa'][-1],'variant96':{'graph_sha256':sha96,'operations':len(rows96),'operation_counts':counts96,'live_gates':len(rows96),'degree_upper':deg96[g96['output']],'ray_degree':len(vals[g96['output']])-1,'ray_leading_coefficient':vals[g96['output']][-1],'strong_identity':'As_96 = Delta*As_97'},'scope':'source-only exact ring identity and exact degree at pinned bytes; no Lean, PDF or complete ancestry claim'},indent=2,sort_keys=True))
