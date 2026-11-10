#!/usr/bin/env python3
"""Independent structural and leading-coefficient audit of sign19 candidate.

Operates on pinned JSON and byte records, not the candidate's builder/checker.
This is external evidence; it does not prove a Lean or arithmetic endpoint.
"""
import gzip
import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parents[2]
old_path = D / 'research/nine-sharing-sign20-degree20-e-candidate/seed.json'
new_path = D / 'research/nine-sharing-sign19-degree44-y-candidate/seed.json'
sha = lambda b: hashlib.sha256(b).hexdigest()
old_bytes, new_bytes = old_path.read_bytes(), new_path.read_bytes()
assert sha(old_bytes) == '2593aca2ac701ff9312fe5aff1719bbf4fd29a97e2c3e14642bf137d6ef8bf7d'
assert sha(new_bytes) == '01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1'
old, new = json.loads(old_bytes), json.loads(new_bytes)
assert old['witness_count'] == 20 and new['witness_count'] == 19
assert old['total_coordinates'] == 21 and new['total_coordinates'] == 20
assert old['distinguished_input_coordinate'] == new['distinguished_input_coordinate'] == 0
assert old['fixed_ports'] == new['fixed_ports']
assert old['coefficient_binding'] == new['coefficient_binding']
beta_x = ['add', ['mul', ['port','beta'], ['add', ['var',1], ['num',1]]], ['num',1]]
y = ['mul', ['add',['var',8],['num',1]], ['mul',['mul',beta_x,beta_x],beta_x]]
assert new['lift_expression'] == y
old_y = [row for row in old['residuals'] if row['gate']=='Y']
assert len(old_y)==1 and old_y[0]['kind']=='positive' and old_y[0]['expr']==['sub',['var',15],y]
assert len(old['residuals']) == 11 and len(new['residuals']) == 10

def transform(node):
    tag = node[0]
    if tag == 'var':
        i = node[1]
        assert 0 <= i < 21
        return y if i == 15 else ['var', i - int(i > 15)]
    if tag in ('num','port'):
        assert len(node)==2
        return node[:]
    assert tag in ('add','sub','mul') and len(node)==3
    return [tag, transform(node[1]), transform(node[2])]

remaining = [row for row in old['residuals'] if row['gate'] != 'Y']
for a, b in zip(remaining, new['residuals']):
    assert {k:v for k,v in a.items() if k!='expr'} == {k:v for k,v in b.items() if k!='expr'}
    assert transform(a['expr']) == b['expr']

def degree(node):
    tag = node[0]
    if tag == 'var':
        assert 0 <= node[1] < 20
        return 1
    if tag in ('num','port'): return 0
    assert tag in ('add','sub','mul')
    x,z = degree(node[1]), degree(node[2])
    return x+z if tag=='mul' else max(x,z)

degrees = {r['gate']:degree(r['expr']) for r in new['residuals']}
assert len(degrees)==10 and max(degrees.values())==22

# Polynomials are coefficient dictionaries beta exponent -> integer, nested
# in coefficient lists indexed by t exponent; all operations are independent
# of the author's tuple-key polynomial implementation.
def padd(a,b,sgn=1):
    c=a.copy()
    for k,v in b.items(): c[k]=c.get(k,0)+sgn*v
    return {k:v for k,v in c.items() if v}
def pmul(a,b):
    c={}
    for i,x in a.items():
        for j,z in b.items(): c[i+j]=c.get(i+j,0)+x*z
    return {k:v for k,v in c.items() if v}
def s_add(a,b,sgn=1):
    return [padd(a[i] if i<len(a) else {},b[i] if i<len(b) else {},sgn)
            for i in range(max(len(a),len(b)))]
def s_mul(a,b):
    c=[{} for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,z in enumerate(b):c[i+j]=padd(c[i+j],pmul(x,z))
    return c
def specialized(node):
    tag=node[0]
    if tag=='num':return [{0:node[1]}] if node[1] else [{}]
    if tag=='var':return [{},{0:1}] if node[1] in (1,8,9,11) else [{}]
    if tag=='port':
        assert node[1]=='beta'
        return [{1:1}]
    a,b=specialized(node[1]),specialized(node[2])
    return s_add(a,b) if tag=='add' else s_add(a,b,-1) if tag=='sub' else s_mul(a,b)
n0=[row for row in new['residuals'] if row['gate']=='N0']
assert len(n0)==1
series=specialized(n0[0]['expr'])
assert all(not x for x in series[23:]) and len(series)>22 and series[22]=={14:-1}

# Verify both compressed and uncompressed data against the inherited records,
# including actual bit lengths and strict positivity of beta.
binding=new['coefficient_binding']; records={}
for name,rec in binding['ports'].items():
    file=new_path.parent / binding['path'] / rec['file']
    packed=file.read_bytes(); raw=gzip.decompress(packed)
    number=int.from_bytes(raw,'big',signed=False)
    assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256']
    assert len(raw)==rec['raw_bytes'] and number.bit_length()==rec['bits']
    if name=='beta':assert number>0
    records[name]={'gzip_sha256':sha(packed),'raw_sha256':sha(raw),'bytes':len(raw),'bits':number.bit_length()}
for kind in ('certificate','ordinary_proof'):
    assert sha((new_path.parent/binding[kind]).read_bytes())==binding[kind+'_sha256']
print(json.dumps({'status':'PASS_EXTERNAL_INDEPENDENT','source_sha256':sha(old_bytes),
    'candidate_sha256':sha(new_bytes),'residual_degrees':degrees,'axis':[1,8,9,11],
    'N0_coefficient_t22':{'beta^14':-1},'square_sum_t44_nonzero_for_beta_positive':True,
    'verified_ports':records,'scope':'external AST transformation and degree evidence; no Lean binding, model bridge, or iPRA endpoint'},indent=2,sort_keys=True))
