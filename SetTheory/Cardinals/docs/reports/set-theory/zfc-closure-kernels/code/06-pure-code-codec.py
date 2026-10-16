"""Transparent prefix coding and fair bounded search for numerical certificates.

nat n: 0 1^n 0; list [a_1,...,a_k]: 1 1^k 0 code(a_1)...code(a_k).
Enumerating all finite bitstrings therefore includes every finite certificate.
This is a reference format, not a state-minimized encoding.
"""
from __future__ import annotations
from typing import Any

def encode(obj: Any) -> str:
    if type(obj) is int and obj>=0: return '0'+'1'*obj+'0'
    if isinstance(obj,(list,tuple)):
        return '1'+'1'*len(obj)+'0'+''.join(encode(x) for x in obj)
    raise ValueError('only nonnegative integers and lists are encodable')

def decode(bits: str) -> Any:
    if any(b not in '01' for b in bits): raise ValueError('not a bitstring')
    pos=0
    def parse() -> Any:
        nonlocal pos
        if pos>=len(bits): raise ValueError('truncated tag')
        tag=bits[pos];pos+=1;n=0
        while pos<len(bits) and bits[pos]=='1': pos+=1;n+=1
        if pos==len(bits): raise ValueError('truncated unary field')
        pos+=1
        return n if tag=='0' else [parse() for _ in range(n)]
    ans=parse()
    if pos!=len(bits): raise ValueError('trailing bits')
    return ans

def candidate(n: int) -> str:
    if type(n) is not int or n<0: raise ValueError('natural number required')
    return bin(n+1)[3:] # delete the leading 1: length-lexicographic enumeration

def bounded_search(stop: int) -> dict:
    if type(stop) is not int or stop < 0:
        raise ValueError("stop must be a nonnegative integer")
    from logic import check
    accepted=0
    for n in range(stop):
        try: c=decode(candidate(n))
        except ValueError: continue
        result=check(c)
        accepted+=int(result['valid'])
        if result['refutation']: return {'halted':True,'index':n,'certificate':c}
    return {'halted':False,'candidates':stop,'valid_certificates':accepted,
            'meaning':'finite prefix only; no non-halting or consistency conclusion'}

if __name__=='__main__':
    import argparse,json
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stop',type=int,default=10000)
    args=p.parse_args()
    if args.stop<0: p.error('--stop must be nonnegative')
    print(json.dumps(bounded_search(args.stop),indent=2))
