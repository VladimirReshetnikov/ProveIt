#!/usr/bin/env python3
"""Explicit sixteen-integer specialization of the pinned Jones source.

Standard library only. No search for a machine computation or for a solution.
The final output is a division-free arithmetic DAG with sixteen inputs.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parent
UP = ROOT / 'upstream'
sys.path.insert(0, str(UP / 'nine'))
import nine_compressor as nc
import verify_fixed_instance as vf
import optimized_source as opt

GUARDS = ['epsilon', 'g0', 's0', 'w0', 'phi']

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def verify_source_pins():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    additions=json.loads((ROOT/'SOURCE_ADDITIONS.json').read_text())
    records=pins['files']+additions['files']
    for record in records:
        data=(ROOT/record['path']).read_bytes()
        require(hashlib.sha256(data).hexdigest()==record['sha256'],
                'Source SHA-256 mismatch: '+record['path'])
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(blob==record['git_blob_sha1'],'Source Git blob mismatch: '+record['path'])
    return len(records)

def source_body():
    constants = json.loads((UP/'nine/generated/constants.json').read_text())
    keys, aliases = opt.canonical_coefficients(constants)
    return opt.make_body(32, keys, 'majorant')

def extend_dag(body):
    d = nc.DAG()
    d.nodes = [dict(n) for n in body['nodes']]
    d.cache = {json.dumps(n, sort_keys=True, separators=(',', ':')):i
               for i,n in enumerate(d.nodes)}
    d.known = {i:n['value'] for i,n in enumerate(d.nodes) if n['kind']=='literal'}
    d.names = dict(body['named_nodes'])
    return d

def construct():
    d = extend_dag(source_body())
    c, add, sub, mul, power = d.const, d.plus, d.minus, d.times, d.power
    get = lambda s:d.names[s]
    x = {s:d.var(s) for s in GUARDS}
    zz = [d.var('z'+str(j)) for j in range(1,7)]
    residue, normroot = d.var('residue'), d.var('normroot')
    i = add(d.var('i0'),c(1))
    stack = c(1)
    for j,name in enumerate(GUARDS):
        discriminant = add(mul(c(3), x[name]),c(2))
        factor = add(c(1),mul(c(4),discriminant,power(stack,2),power(zz[j],2)))
        stack = d.save('Cguard'+str(j+1),mul(stack,factor))
    discriminant = sub(mul(c(3),get('margin')),c(1))
    factor = add(c(1),mul(c(4),discriminant,power(stack,2),power(zz[5],2)))
    stack = d.save('Cguard6',mul(stack,factor))
    divisor = d.save('Ddiv',mul(get('J'),get('F')))
    dividend = d.save('Tdiv',add(mul(get('Q'),get('F')),
                              mul(get('J'),sub(get('H'),get('C')))))
    nonzero = d.save('Znonzero',mul(i,*zz))
    denom = d.save('Smerge',mul(nonzero,power(divisor,5)))
    rr = add(dividend,mul(divisor,residue))
    div2 = power(divisor,2)
    homogeneous = d.save('Tmerge',mul(
        sub(sub(power(rr,3),mul(div2,rr)),mul(div2,divisor)),
        add(power(rr,2),mul(c(23),div2))))
    weight1 = d.save('weight1',add(c(1),stack))
    weight2 = d.save('weight2',mul(weight1,
                          add(power(get('P'),2),power(get('K'),2),c(2))))
    X = d.save('Xnorm',sub(mul(denom,normroot),homogeneous))
    S2 = power(denom,2)
    B0 = d.save('B0norm',mul(S2,stack))
    B1 = d.save('B1norm',mul(S2,power(weight1,2),get('a0')))
    B2 = d.save('B2norm',mul(S2,power(weight2,2),get('a1')))
    X2 = power(X,2)
    aa = d.save('Anorm',sub(sub(add(X2,B2),B0),B1))
    aa2 = power(aa,2)
    fourXB = mul(c(4),X2,B2)
    dd = d.save('Enorm',sub(add(aa2,fourXB),mul(c(4),B0,B1)))
    out = d.save('signed16',sub(power(dd,2),mul(c(4),aa2,fourXB)))
    nodes,root,names = d.prune(out)
    variables = [n['name'] for n in nodes if n['kind']=='variable']
    require(len(variables)==16 and len(set(variables))==16,'Incorrect variable count')
    require('n' not in variables,'Original nonnegative final witness remains')
    return {'schema':'proveit-jones-signed16-v1','variables':variables,
            'domain':'unrestricted integers','nodes':nodes,'output':root,
            'named_nodes':names,'nu':32,'L':5**33,
            'operation_counts':{k:sum(n['kind']==k for n in nodes) for k in ['add','sub','mul']},
            'exact_degree':406528*5**33+10008,
            'exact_degree_formula':'406528*5^33+10008',
            'coefficient_binding':'upstream/COEFFICIENT_BINDINGS.json; full original T4 tuple',
            'fixed_leaf_recipes':'upstream/nine/generated/constants.json',
            'proof':'SIGNED15_16_PROOF.md'}

def dag_degrees(body, fixed_modulus=1000003):
    """Formal degree upper bound, with diagonal leading coefficient modulo p.

    A nonzero diagonal coefficient reaching the structural bound proves exact
    degree. Every nonliteral fixed leaf is given residue zero: whenever its
    degree could affect the certificate we reject rather than assume its value.
    Degree-zero fixed leaves have symbolic-unknown provenance, tracked below.
    """
    p=fixed_modulus
    values=[]
    for n in body['nodes']:
        k=n['kind']
        if k=='literal': row=(0,n['value']%p,False)
        elif k=='fixed': row=(0,0,True)
        elif k=='variable': row=(1,1,False)
        else:
            a,b=values[n['left']],values[n['right']]
            if k=='mul': row=(a[0]+b[0],a[1]*b[1]%p,a[2] or b[2])
            else:
                deg=max(a[0],b[0]);sign=1 if k=='add' else -1
                lc=((a[1] if a[0]==deg else 0)+sign*(b[1] if b[0]==deg else 0))%p
                unknown=(a[2] if a[0]==deg else False) or (b[2] if b[0]==deg else False)
                row=(deg,lc,unknown)
        values.append(row)
    out=values[body['output']]
    require(out[0]==body['exact_degree'],'Structural degree bound differs')
    require(out[1]!=0 and not out[2],'Exact degree coefficient not certified independently of constants')
    return {'degree':out[0],'diagonal_leading_coefficient_modulus':p,
            'diagonal_leading_coefficient':out[1],
            'leading_coefficient_independent_of_fixed_ports':not out[2],
            'selected':{name:values[idx] for name,idx in body['named_nodes'].items()
                        if name in ['R','P','K','a0','a1','margin','Cguard5','Cguard6',
                                    'Smerge','Tmerge','weight1','weight2','B2norm','signed16']}}

def actual_fixed_leaves(p):
    fixed=vf.load_module(UP/'code/fixed_coefficients.py')
    constants=json.loads((UP/'nine/generated/constants.json').read_text())
    bnd=json.loads((UP/'nine/generated/index_bound_s.json').read_text())
    ports=fixed.t4_ports(p)
    expports=fixed.t4_ports(p-1)
    order=constants['fixed_port_order']
    s=vf.evaluate(vf.record_polynomial(bnd['terms']),[expports[x] for x in order],p-1)
    z=pow(2,s,p)
    coefficients={tuple(r['alpha']):vf.evaluate(
                  vf.record_polynomial(r['coefficient_polynomial_in_fixed_ports']),
                  [ports[x] for x in order],p)
                  for r in constants['coefficient_records']}
    y=vf.fast_digit_value(2*z%p,z,coefficients,32,p)
    leaves={'z_index':z,'y_index':y}
    leaves.update({r['name']:coefficients[tuple(r['alpha'])] for r in constants['coefficient_records']})
    return leaves,{'prime':p,'fixed_ports':ports,'z_index':z,'y_index':y}

def direct_extension(base,x,p):
    stack=1
    for j,name in enumerate(GUARDS,1):
        stack=stack*(1+4*(3*x[name]+2)*stack*stack*x['z'+str(j)]**2)%p
    stack=stack*(1+4*(3*base['margin']-1)*stack*stack*x['z6']**2)%p
    divisor=base['J']*base['F']%p
    dividend=(base['Q']*base['F']+base['J']*(base['H']-base['C']))%p
    nonzero=x['i0']+1
    for j in range(1,7):nonzero=nonzero*x['z'+str(j)]%p
    S=nonzero*pow(divisor,5,p)%p
    r=(dividend+divisor*x['residue'])%p
    T=((r**3-divisor**2*r-divisor**3)*(r*r+23*divisor*divisor))%p
    w1=(1+stack)%p
    w2=w1*(base['P']**2+base['K']**2+2)%p
    X=(S*x['normroot']-T)%p
    B0=S*S*stack%p;B1=S*S*w1*w1*base['a0']%p;B2=S*S*w2*w2*base['a1']%p
    A=(X*X+B2-B0-B1)%p
    E=(A*A+4*X*X*B2-4*B0*B1)%p
    return (E*E-16*A*A*X*X*B2)%p

def verify(body):
    source=source_body()
    constants=json.loads((UP/'nine/generated/constants.json').read_text())
    rawkeys=[(tuple(rec['alpha']),rec['name']) for rec in constants['coefficient_records']]
    literal_source=nc.make_body(32,rawkeys,'majorant')
    body_comparisons=0
    rng=random.Random(17020261022)
    rows=[]
    comparisons=0
    for prime in [101,1009,1000003]:
        fixed,receipt=actual_fixed_leaves(prime)
        for _ in range(8):
            x={s:rng.randrange(-8,9) for s in body['variables']}
            xs={s:x.get(s,0) for s in source['variables']}
            _,base=nc.evaluate_dag(source,fixed,xs,prime)
            literal_inputs={name:xs.get(name,0) for name in literal_source['variables']}
            _,literal_nodes=nc.evaluate_dag(literal_source,fixed,literal_inputs,prime)
            for name in ['b','B','q','ell','lambda','e','R','U','Y','P','K','A','C','J','Q','D','E','F','Gp','H','I','a0','a1','margin']:
                require(base[name]==literal_nodes[name],'Horner/literal source mismatch: '+name)
                body_comparisons+=1
            out,named=nc.evaluate_dag(body,fixed,x,prime)
            require(out==direct_extension(base,x,prime),'Direct/DAG mismatch')
            xs['i0']=-xs['i0']-2
            _,other=nc.evaluate_dag(source,fixed,xs,prime)
            for s in ['a0','a1','divisor','dividend','margin']:
                require(base[s]==other[s],'Signed i normalization mismatch')
            comparisons+=1
        rows.append(receipt)
    # Check the norm identity independently as an eight-factor product where
    # the three formal radicals are arbitrary explicit integer roots.
    norm_checks=0
    for _ in range(150):
        X,r0,r1,r2=[rng.randrange(-25,26) for _ in range(4)]
        B0,B1,B2=r0*r0,r1*r1,r2*r2
        A=X*X+B2-B0-B1;E=A*A+4*X*X*B2-4*B0*B1
        direct=1
        for e0 in [-1,1]:
            for e1 in [-1,1]:
                for e2 in [-1,1]:direct*=X-e0*r0-e1*r1-e2*r2
        require(E*E-16*A*A*X*X*B2==direct,'Norm identity failure')
        norm_checks+=1
    # These finite diagnostics supplement the unbounded proof, never replace it.
    intersective_checks=0
    for m in range(1,1201):
        require(any(((y**3-y-1)*(y*y+23))%m==0 for y in range(m)),
                'Intersective modulus failure')
        intersective_checks+=1
    gap_checks=0
    for R in range(2,35):
        for P in range(R+3,R+20):
            for K in range(2,R+2):
                require((P*K-1)**2 < (P*P-1)*K*K+1 < (P*K)**2,'Pell gap failed')
                gap_checks+=1
    return {'status':'PASS','scope':'Finite circuit/arithmetic diagnostics; not a consistency proof or kernel certificate.',
            'variables':len(body['variables']),'operations':body['operation_counts'],
            'total_operations':sum(body['operation_counts'].values()),
            'degree_certificate':dag_degrees(body),
            'actual_instance_modular_comparisons':comparisons,
            'literal_horner_named_node_comparisons':body_comparisons,
            'norm_identity_checks':norm_checks,'intersective_moduli_checked':intersective_checks,
            'consecutive_square_gap_checks':gap_checks,'fixed_fingerprints':rows}

def main():
    pinned_files=verify_source_pins()
    body=construct()
    out=ROOT/'generated';out.mkdir(exist_ok=True)
    (out/'signed16.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
    receipt=verify(body)
    receipt['authenticated_source_files']=pinned_files
    (out/'signed16_checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['degree_certificate','fixed_fingerprints']},indent=2))
    print('Exact degree:',receipt['degree_certificate']['degree'])
    print('DAG bytes:',(out/'signed16.json').stat().st_size)

if __name__=='__main__':main()

