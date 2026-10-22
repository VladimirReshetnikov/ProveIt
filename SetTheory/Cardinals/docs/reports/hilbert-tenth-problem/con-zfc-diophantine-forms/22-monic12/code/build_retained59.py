#!/usr/bin/env python3
"""Combine the retained auxiliary ports with the positive transport shift.

Builds 16 positive unknowns, seven equations of maximum degree 24,
with 59 binary arithmetic operations.  No compiler or Pell proof is
claimed by these exact polynomial checks.
"""
from pathlib import Path
import json
import hashlib
import random
from fractions import Fraction
from sparse_polynomial import Ring

HERE=Path(__file__).resolve().parent
UP=HERE.parent/'data'
OUT=UP

def require(v,msg):
    if not v: raise ValueError(msg)

def evaluate(source,supply):
    v=dict(supply)
    def get(x): return x if isinstance(x,int) else v[x]
    for name,op,x,y in source:
        a,b=get(x),get(y)
        v[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return v

def main():
    old=json.loads((UP/'retained16_system60.json').read_text())
    new={k:old[k] for k in ('witness_domain','witnesses','fixed_numerals')}
    source=[]
    for row in old['source']:
        if row[0]=='trans_part': continue
        if row[0]=='Nt': source.append(['transport_rhs','+','F','zrep'])
        else: source.append(row)
    comparisons=[(['innerC','transport_rhs'] if p==['Nt',1] else p) for p in old['comparisons']]
    new.update(name='retained16_system59',source=source,comparisons=comparisons,
        repository_pin='f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
        coefficient_binding='COEFFICIENT_BINDING.json',
        transport_shift='z_new = z_old - 1; positive on all canonical accepting witnesses.',
        proof='../proofs/RETAINED59_PROOF.md',formal_status='Ordinary mathematical composition; no new proof-assistant theorem.')
    ring=Ring(new['witnesses']+new['fixed_numerals'])
    vals=dict(ring.variables)
    def get(x): return ring.coerce(x) if isinstance(x,int) else vals[x]
    known=set(vals)
    for name,op,x,y in source:
        require(name not in known,'duplicate gate')
        known.add(name)
        a,b=get(x),get(y)
        vals[name]=a+b if op=='+' else a-b if op=='-' else a*b
    residuals=[get(a)-get(b) for a,b in comparisons]
    degrees=[v.degree(len(new['witnesses'])) for v in residuals]
    live={x for pair in comparisons for x in pair if isinstance(x,str)}
    for name,op,x,y in reversed(source):
        require(name in live,'dead gate '+name)
        for t in (x,y):
            if isinstance(t,str):live.add(t)
    require(all(x in live for x in new['witnesses']+new['fixed_numerals']),'dead input')
    counts={op:sum(r[1]==op for r in source) for op in '+-*'}
    require(len(source)==59,'operation count')
    require(degrees==[22,18,24,7,2,22,6],'degree list')
    new.update(ledger=dict(operations=59,multiplications=counts['*'],
        additions_subtractions=counts['+']+counts['-'],all_gates_live=True,all_ports_live=True),
        residual_exact_degrees=degrees,exact_maximum_degree=24)
    new['source_sha256']=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest()
    rng=random.Random(1659)
    for n in range(200):
        v={x:rng.randrange(-9,12) for x in new['witnesses']+new['fixed_numerals']}
        if n>=100: v={x:Fraction(a,rng.randrange(1,5)) for x,a in v.items()}
        vo=dict(v); vo['z']+=1
        oldvals=evaluate(old['source'],vo); newvals=evaluate(source,v)
        def residuals_at(packet,values):
            def get(x): return x if isinstance(x,int) else values[x]
            return [get(a)-get(b) for a,b in packet['comparisons']]
        require(residuals_at(old,oldvals)==residuals_at(new,newvals),'shift identity')
    sos_source=list(source)
    for n,(a,b) in enumerate(comparisons):
        sos_source.extend([[f'residual{n}','-',a,b],[f'square{n}','*',f'residual{n}',f'residual{n}']])
    prior='square0'
    for n in range(1,7):
        out=f'sum{n}'; sos_source.append([out,'+',prior,f'square{n}']); prior=out
    new['sum_of_squares']=dict(source=sos_source,output=prior,operations=len(sos_source),exact_degree=48,
        note='This 79-operation equation is a tradeoff; the main new frontier point is the 59-operation system.')
    (OUT/'retained16_system59.json').write_text(json.dumps(new,indent=2)+'\n')
    report=dict(status='PASS',variables=16,equations=7,operations=59,
        multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],
        residual_degrees=degrees,maximum_degree=24,algebra_cases=200,
        sum_of_squares_operations=79,sum_of_squares_degree=48,
        statement='Symbolic polynomial counts and exact signed/rational identity checks; inherited compiler/Pell theorems remain mathematical proof dependencies.')
    (OUT/'retained59_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
