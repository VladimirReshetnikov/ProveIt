#!/usr/bin/env python3
"""Independent literal-parent, coherent-payload and source-bound audit.

No builder/verifier modules are imported. All symbolic coefficient arithmetic
below is reconstructed from the 22 literal sparse residuals.
"""
from collections import defaultdict
from hashlib import sha256
from itertools import product
from math import comb, factorial
from pathlib import Path
import gzip
import json
import sys


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def shifted_residual(equation):
    out = defaultdict(int)
    for term in equation['terms']:
        powers = term['powers']
        active = [i for i, p in enumerate(powers[:31]) if p]
        for choices in product(*(range(powers[i]+1) for i in active)):
            exponent = [0]*31 + powers[31:]
            value = term['coefficient']
            for i, k in zip(active, choices):
                exponent[i] = k
                value *= comb(powers[i], k)
            out[tuple(exponent)] += value
    return {e: c for e, c in out.items() if c}


def audit(directory):
    data = directory / 'data'
    instance = json.loads((data/'INSTANCE.json').read_text())
    parent_path = data/instance['parent']
    parent = json.loads(parent_path.read_text())
    require(digest(parent_path) == '1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287', 'literal parent changed')
    require(digest(parent_path) == instance['parent_sha256'], 'parent digest metadata')
    require(len(parent['variables'])==31 and len(parent['equations'])==22, 'parent dimensions')
    require(parent['constants']==['beta','K0','MC','MF'], 'parent fixed port order')
    weighted_path = data/instance['weighted_coefficients']
    weighted = json.loads(weighted_path.read_text())
    require(weighted['parent_sha256']==digest(parent_path), 'weighted parent identity')
    source = defaultdict(int)
    shifted = [shifted_residual(eq) for eq in parent['equations']]
    for residual in shifted:
        for a, ca in residual.items():
            for b, cb in residual.items():
                source[tuple(x+y for x,y in zip(a,b))] += ca*cb
    source = {e:c for e,c in source.items() if c}
    reconstructed = defaultdict(dict)
    for exponent, coefficient in source.items():
        alpha = (0,)+exponent[:31]
        multiplier = factorial(4-sum(alpha))
        for power in alpha:
            multiplier *= factorial(power)
        reconstructed[alpha][exponent[31:]] = coefficient*multiplier
    supplied = {}
    for record in weighted['coefficient_records']:
        alpha=tuple(record['alpha'])
        require(alpha not in supplied, 'duplicate coefficient record')
        supplied[alpha] = {tuple(t['powers']):t['coefficient'] for t in record['coefficient_polynomial_in_fixed_ports']}
    require(dict(reconstructed)==supplied, 'weighted coefficient reconstruction')
    require(len(supplied)==402, 'coefficient count')
    require(max(sum(e[:31]) for e in source)==4, 'quartic degree')
    tau_index=parent['variables'].index('tau')
    tau_monomial=[0]*35
    tau_monomial[tau_index]=4
    require(source.get(tuple(tau_monomial))==1, 'tau fourth-power coefficient')
    require(shifted[4].get((0,)*35)==1, 'zero-input nonvanishing residual')

    raw_hashes = {
        'beta':'f0f5b438174bbf08506e1be527063dc11aa9cf36826db98c9cad845ca4bddaf4',
        'K0':'fd97c0651a5999b4792aa27536241e417da5a22a1a22bd6306e58e4b68b2dd39',
        'MC':'4a0c8ba7c9b5bdbe7fdd418e0f7b8658e3081272480f5da75971736caf2f5aec',
        'MF':'d21870940eca107fa58556ecbf968c833e51b43b0a07696f96576db39153b3c8'}
    payloads={}
    bits=[]
    for name in ('beta','K0','MC','MF'):
        raw=gzip.decompress((data/instance['four_ports'][name]).read_bytes())
        require(sha256(raw).hexdigest()==raw_hashes[name], 'wrong new backend port: '+name)
        filename={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}[name]+'.bin'
        require(raw==(directory.parent/'coefficient_backend'/'coefficients'/filename).read_bytes(), 'backend composition mismatch: '+name)
        value=int.from_bytes(raw,'little')
        require(value>0, 'nonpositive port')
        bits.append(value.bit_length())
        payloads[name]={'sha256':sha256(raw).hexdigest(),'bit_length':value.bit_length(),'raw_bytes':len(raw)}
    require(bits==[683195,688546,683195,683196], 'new port sizes')
    bounds=json.loads((data/instance['coefficient_bound']).read_text())
    require(bounds['port_bit_lengths']==bits, 'stale bound port lengths')
    s=bounds['index_exponent']
    require(s==2743487, 'new bound exponent')
    record_bounds={r['name']:r['strict_power_of_two_bound'] for r in bounds['records']}
    require(len(record_bounds)==402, 'incomplete bound ledger')
    upper_bits=[]
    for record in weighted['coefficient_records']:
        # Every positive fixed port is strictly below 2^its_bit_length.
        # Triangle inequality gives |c_alpha|+1 <= this exact integer bound.
        upper=1
        for term in record['coefficient_polynomial_in_fixed_ports']:
            exponent=sum(a*b for a,b in zip(bits,term['powers']))
            upper += abs(term['coefficient']) << exponent
        require(upper < (1 << record_bounds[record['name']]), 'invalid individual coefficient bound: '+record['name'])
        require(upper < (1 << s), 'invalid common coefficient bound')
        upper_bits.append(upper.bit_length())
    beta=instance['beta_sun']
    raw=gzip.decompress((data/beta['file']).read_bytes())
    exponent=beta['power_of_two_exponent']
    require(exponent==2743514 and exponent%2==0, 'new source-base exponent')
    require(int.from_bytes(raw,'little')==(1 << exponent), 'source base literal power')
    require(sha256(raw).hexdigest()==beta['sha256'], 'source-base digest')
    require(48*33**4 < (1 << (exponent-s)), 'source coefficient margin')
    return {'status':'PASS','instance':instance['instance'],
            'parent_sha256':digest(parent_path),'weighted_coefficients_sha256':digest(weighted_path),
            'parent_variables':31,'parent_equations':22,'source_degree':4,
            'tau_fourth_power_coefficient':1,'fifth_residual_at_zero':1,
            'weighted_coefficient_records_reconstructed':len(supplied),
            'coherent_backend_ports':payloads,
            'coefficient_bound_exponent':s,'individual_bound_records_checked':402,
            'source_base_exponent':exponent,'source_base_sha256':sha256(raw).hexdigest(),
            'source_base_is_even_power_of_two':True,
            'coefficient_margin_factor':48*33**4,
            'coefficient_margin_power_of_two':exponent-s,
            'scope':'Exact symbolic parent reconstruction, coherent literal payload identity, and coefficient-size bounds. Semantic backend transfer is reviewed in COMPOSED_B4_INDEPENDENT_REVIEW.md.'}


if __name__=='__main__':
    directory=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'ten_integer_composed'
    result=audit(directory)
    output=Path(sys.argv[2]) if len(sys.argv)>2 else Path(__file__).with_name('COMPOSED_BINDING_INDEPENDENT_AUDIT.json')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
