#!/usr/bin/env python3
"""Offline reproduction and finite verification, standard library only."""
import gzip
import hashlib
import itertools
import json
import subprocess
import sys
from pathlib import Path
from audit_parent_packing import add, mul

ROOT=Path(__file__).resolve().parents[1]

def run(relative,args=()):
    p=subprocess.run([sys.executable,str(ROOT/relative),*map(str,args)],
                     cwd=ROOT,text=True,capture_output=True,check=True)
    return json.loads(p.stdout)

def norm_identity():
    # Expand eight linear factors in X,r0,r1,r2 and then replace ri^2 by ai.
    zero=(0,0,0,0)
    one={zero:1}
    v=[]
    for j in range(4):
        e=list(zero);e[j]=1;v.append({tuple(e):1})
    product=one
    for signs in itertools.product((-1,1),repeat=3):
        factor=dict(v[0])
        for j,s in enumerate(signs,1):factor=add(factor,v[j],s)
        product=mul(product,factor)
    reduced={}
    for mon,c in product.items():
        assert all(e%2==0 for e in mon[1:])
        reduced[(mon[0],*(e//2 for e in mon[1:]))]=c
    X,a0,a1,a2=v
    x2=mul(X,X)
    V=add(add(add(x2,a2),a0,-1),a1,-1)
    V2=mul(V,V)
    four=lambda p:{m:4*c for m,c in p.items()}
    W=add(add(V2,four(mul(x2,a2))),four(mul(a0,a1)),-1)
    compact=add(mul(W,W),{m:16*c for m,c in mul(mul(V2,x2),a2).items()},-1)
    assert compact==reduced
    return {'status':'PASS','expanded_norm_terms':len(compact),'identity':'Exact integer polynomial expansion of all eight signed factors.'}

def verify_binding():
    baseline=json.loads((ROOT/'upstream/COEFFICIENT_BINDING_AT_PIN.json').read_text())
    for row in baseline['files']:
        raw=gzip.decompress((ROOT/'coefficients'/row['file']).read_bytes())
        assert hashlib.sha256(raw).hexdigest()==row['sha256']
    machine=ROOT/'upstream/k215.tm'
    assert hashlib.sha256(machine.read_bytes()).hexdigest()=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
    # Check the copied transition JSON against the literal machine table.
    rows=[]
    for line in machine.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split()
        rows.append([int(q),int(b),int(w),1 if d=='R' else -1,215 if t in ('H','halt','-1') else int(t)])
    js=json.loads((ROOT/'coefficients/upstream/k215_transitions.json').read_text())['transitions']
    assert rows==js
    exponent=json.loads((ROOT/'data/coefficient_recipes.json').read_text())['beta_source_exponent']
    v=1<<exponent;raw=v.to_bytes((v.bit_length()+7)//8,'little')
    path=ROOT/'data/beta_source.bin.gz'
    path.write_bytes(gzip.compress(raw,mtime=0))
    return {'status':'PASS','native_ports_identical_to_package31':True,'machine_rows':len(rows),
            'beta_source_exponent':exponent,'beta_source_raw_bytes':len(raw),
            'beta_source_sha256':hashlib.sha256(raw).hexdigest()}

def main():
    if not __debug__:raise SystemExit('Run without -O: audit assertions are required.')
    coeff=run('coefficients/build_coefficients.py')
    built=run('code/build.py')
    parent=run('code/audit_parent_packing.py',('--circuit',ROOT/'upstream/parent_system.json',
        '--sparse',ROOT/'upstream/parent_sparse.json','--weights',ROOT/'data/weights.json',
        '--output',ROOT/'certificates/parent_packing.json'))
    full=run('code/audit_full_circuit.py',(ROOT,))
    toy=run('code/check_multitarget_toy.py')
    binding=verify_binding()
    norm=norm_identity()
    for name,data in [('full_circuit',full),('toy_controls',toy),('binding',binding),('norm_identity',norm)]:
        (ROOT/'certificates'/f'{name}.json').write_text(json.dumps(data,indent=2)+'\n')
    result={'status':'PASS','metrics':built,'parent_symbolic_audit':parent['status'],
            'independent_circuit_audit':full['status'],'toy_controls':toy,'binding':binding,
            'norm_identity':norm,'native_geometry_checks':coeff['geometry']['native_basis_checks'],
            'scope':'Finite checks and exact algebraic identities. The mathematical proof is in report.tex; no Lean/Rocq build or decision of consistency is claimed.'}
    (ROOT/'certificates/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
