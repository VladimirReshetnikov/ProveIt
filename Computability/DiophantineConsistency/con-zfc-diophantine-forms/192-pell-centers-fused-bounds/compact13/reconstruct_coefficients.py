#!/usr/bin/env python3
"""Reconstruct all fixed numerals and check the retained action identity.

The inherited pure recipe is frozen byte-for-byte. It is not a new native
calibration proof; this checks the actual mathematical integer values.
"""
from pathlib import Path
import hashlib,importlib.util,json,re

HERE=Path(__file__).resolve().parent

def check():
    spec=importlib.util.spec_from_file_location('frozen_recipe',HERE/'inherited/coefficient_recipe.py')
    r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
    seed=(HERE/'SEED.txt').read_text().strip()
    if len(seed)!=399:raise ValueError('Seed length')
    old=''.join(re.findall(r'^([A-Za-z0-9]+)\\par$',(HERE/'inherited/CURRENT_P66.tex').read_text(),re.M))
    actions=r.new_decode(seed)
    if len(old)!=436 or actions!=r.old_decode(old):raise ValueError('Retained 430-action identity')
    tiles=r.tiles(actions);values=r.constants(tiles)
    records={}
    for name,value in values.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'big')
        if raw!=(HERE/'coefficients'/(name+'.bin')).read_bytes():raise ValueError('Reconstructed coefficient differs '+name)
        digest=hashlib.sha256(raw).hexdigest()
        if digest!=r.EXPECTED[name]:raise ValueError('Frozen coefficient identity '+name)
        records[name]={'bytes':len(raw),'sha256':digest}
    # The finite controller's arithmetic conditions are rechecked on the actual K.
    B=values['beta']+1;K=values['K'];d=47*4027
    def prime(n):return n>=2 and all(n%t for t in range(2,__import__('math').isqrt(n)+1))
    for p,order,divisors in [(47,23,[23]),(4027,1342,[2,11,61])]:
        if not prime(p) or pow(2,order,p)!=1 or any(pow(2,order//t,p)==1 for t in divisors):raise ValueError('Exact base2 order')
        if pow(B,order,p)!=1 or any(pow(B,order//t,p)==1 for t in divisors):raise ValueError('Exact actual radix order')
        if (B*B-1)%p==0 or (1+B*K+B*B)%p==0:raise ValueError('Fixed controller nonvanishing')
    p=246929;kappa=p-1
    if not prime(p) or p<=d or kappa%30866:raise ValueError('Controller prime')
    if (B*B-1)%p==0 or (1+B*K+B*B)%p==0:raise ValueError('Controller nonvanishing')
    lift=pow(B,kappa,p*p)
    if lift%p!=1 or lift==1:raise ValueError('Controller valuation exactly one')
    return {'status':'PASS','actions':len(actions),'tiles':len(tiles),'seed_characters':len(seed),'raw_coefficient_bytes':sum(x['bytes'] for x in records.values()),'coefficients':records,'controller_prime':p,'controller_checks':'Exact trial primality, exact orders, actual-K nonvanishing and one valuation lift; the unbounded native proof remains inherited.'}

if __name__=='__main__':print(json.dumps(check(),indent=2,sort_keys=True))
