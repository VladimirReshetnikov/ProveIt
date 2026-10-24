#!/usr/bin/env python3
"""Independent exact finite-field univariate replays of the literal DAG.

All ten inputs are independently chosen nonzero multiples of t. The actual
coefficient payloads, reduced modulo two primes, are used. This establishes
attainment of degree 912 for the supplied graph, and checks the claimed
leading form under multiple specializations. The universal degree upper
bound is the formal Laurent argument in PROOF.md, not these finite tests.
"""
from pathlib import Path
from collections import Counter
import gzip,json,hashlib,random
R=Path(__file__).resolve().parent

def check(x,m):
    if not x: raise ValueError(m)

def trim(a):
    while len(a)>1 and not a[-1]:a.pop()
    return a

def plus(a,b,p,sign=1):
    c=[0]*max(len(a),len(b))
    for i,v in enumerate(a):c[i]=v
    for i,v in enumerate(b):c[i]=(c[i]+sign*v)%p
    return trim(c)

def times(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        if v:
            for j,w in enumerate(b):
                if w:c[i+j]+=v*w
    return trim([v%p for v in c])

def replay(packet,constants,slopes,p):
    values={v:[0,slopes[v]%p] for v in packet['variables']}
    values.update({v:[constants[v]%p] for v in packet['fixed_numerals']})
    def val(v):return [v%p] if isinstance(v,int) else values[v]
    for name,op,a,b in packet['source']:
        av,bv=val(a),val(b)
        values[name]=times(av,bv,p) if op=='*' else plus(av,bv,p,1 if op=='+' else -1)
    return values[packet['output']]

def main():
    packet=json.loads((R/'generated/p10_positive.json').read_text())
    binding=json.loads((R/'coefficients/BINDING.json').read_text())
    constants={}
    for name,entry in binding['ports'].items():
        raw=gzip.decompress((R/'coefficients'/entry['gzip_payload']).read_bytes())
        check(hashlib.sha256(raw).hexdigest()==entry['sha256'],'Coefficient hash')
        constants[name]=int.from_bytes(raw,'little')
    results=[];rng=random.Random(20261024)
    for p in (1000003,1000033):
        for run in range(3):
            slopes={v:(1 if run==0 else rng.randrange(1,30)) for v in packet['variables']}
            poly=replay(packet,constants,slopes,p)
            x=slopes
            expected=(pow(2,44,p)*pow(3*(constants['beta']%p)*x['j'],558,p)
                      *pow(x['i'],38,p)*pow(x['eta']+x['zeta'],86,p)
                      *pow(x['X'],68,p)*pow(x['s'],154,p)
                      *pow(x['T']+x['F']+x['alpha'],8,p))%p
            check(expected!=0,'Bad specialization')
            check(len(poly)-1==912,'Actual graph degree is not 912')
            check(poly[-1]==expected,'Leading coefficient mismatch')
            results.append({'prime':p,'slopes':slopes,'degree':len(poly)-1,'leading_coefficient':poly[-1]})
    result={'status':'PASS','method':'Exact univariate polynomial arithmetic over finite fields; actual coefficient bytes','cases':results,'scope':'Attainment and consistency checks. Universal upper bound proved in PROOF.md.'}
    (R/'generated/DEGREE_SPECIALIZATIONS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
