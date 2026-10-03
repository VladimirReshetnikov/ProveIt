#!/usr/bin/env python3
"""Rigorous integer-only interval for the literal universal tree's natural-code bits.
A node's exact code is retained only until its bit length first exceeds 4096;
then only bounds are propagated. No large universal scalar is materialized.
"""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent
raw=(HERE/'literal_universal_tree.json').read_bytes();dag=json.loads(raw)
bounds=[];exact=[]
for node in dag['nodes']:
    if node[0]=='L':v=0;lo=hi=0
    elif node[0]=='S':
        a=exact[node[1]];l,h=bounds[node[1]]
        v=None if a is None else 2*a+1
        lo,hi=l+1,h+1
    else:
        a,b=(exact[j] for j in node[1:])
        ls,hs=zip(*(bounds[j] for j in node[1:]))
        v=None if a is None or b is None else (a+b)*(a+b+1)+2*b+2
        lo,hi=max(2,2*max(ls)-1),2*max(hs)+3
    if v is not None:lo=hi=v.bit_length()
    if hi>4096:v=None
    bounds.append((lo,hi));exact.append(v)
# Justification: if max child code has B bits and B>=1, it lies in
# [2^(B-1),2^B), so F >= max(a,b)^2 and F < 2^(2B+3).
# Hence 2B-1 <= bits(F) <= 2B+3. The all-zero fork has exactly 2 bits.
lo,hi=bounds[dag['root']]
result={'input_sha256':hashlib.sha256(raw).hexdigest(),'root':dag['root'],'minimum_code_bits':lo,'maximum_code_bits':hi,'minimum_packed_bytes':(lo+7)//8,'maximum_packed_bytes':(hi+7)//8,'bound_method':'Exact codes until 4096 bits, then integer bitlength interval propagation; no full U scalar.'}
(HERE/'constant_bit_bound.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
