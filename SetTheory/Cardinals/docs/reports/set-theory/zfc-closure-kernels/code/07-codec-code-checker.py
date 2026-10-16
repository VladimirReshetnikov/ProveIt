"""Assumption-free reference certificate checker for the proposed Q theory.

A successful check is syntactic theoremhood, NOT an assertion of set-theoretic
truth. No supplied record is allowed to assert its own unchecked conclusion.
Resource exhaustion is an execution failure, never a successful refutation.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Any
from syntax import (Formula,T,B,I,A,parse,nat,free,subst,alpha_key,congruence,closure)

class InvalidCertificate(ValueError): pass

def check(records: Any) -> dict[str,Any]:
    if not isinstance(records,list) or not records:
        raise InvalidCertificate('Expected a nonempty list of proof records')
    lines: list[Formula]=[]
    def previous(i: Any) -> Formula:
        i=nat(i)
        if i>=len(lines): raise InvalidCertificate('Reference must be strictly backward')
        return lines[i]
    for number,r in enumerate(records):
        try:
            if not isinstance(r,list) or not r or not isinstance(r[0],str):
                raise InvalidCertificate('Expected a tagged record')
            tag,args=r[0],r[1:]
            if tag=='TOP' and len(args)==0: f=T
            elif tag=='K' and len(args)==2:
                p,q=map(parse,args); f=I(p,I(q,p))
            elif tag=='S' and len(args)==3:
                p,q,s=map(parse,args); f=I(I(p,I(q,s)),I(I(p,q),I(p,s)))
            elif tag=='PEIRCE' and len(args)==2:
                p,q=map(parse,args); f=I(I(I(p,q),p),p)
            elif tag=='EFQ' and len(args)==1: f=I(B,parse(args[0]))
            elif tag=='UI' and len(args)==3:
                x,y=nat(args[0]),nat(args[1]); p=parse(args[2])
                f=I(A(x,p),subst(p,{x:y}))
            elif tag=='Q' and len(args)==3:
                x=nat(args[0]); p,q=map(parse,args[1:])
                if x in free(p): raise InvalidCertificate('Q requires x not free in its antecedent')
                f=I(A(x,I(p,q)),I(p,A(x,q)))
            elif tag=='MP' and len(args)==2:
                p,imp=map(previous,args)
                if imp[0]!='I' or alpha_key(p)!=alpha_key(imp[1]):
                    raise InvalidCertificate('MP antecedent mismatch')
                f=imp[2]
            elif tag=='GEN' and len(args)==2: f=A(nat(args[0]),previous(args[1]))
            elif tag=='ALPHA' and len(args)==2:
                p=previous(args[0]); f=parse(args[1])
                if alpha_key(p)!=alpha_key(f): raise InvalidCertificate('Not alpha equivalent')
            elif tag=='EC' and len(args)==0: f=congruence()
            elif tag=='PSC' and len(args)==1: f=closure(parse(args[0]))
            else: raise InvalidCertificate('Unknown rule or wrong arity')
            lines.append(f)
        except ValueError as exc:
            raise InvalidCertificate(f'Line {number}: {exc}') from exc
    return {'valid':True,'refutation':lines[-1]==B,'lines':len(lines),'conclusion':lines[-1]}

def encode_bytes(records: Any) -> int:
    payload=json.dumps(records,separators=(',',':'),ensure_ascii=True).encode('ascii')
    return (1<<(8*len(payload))) | int.from_bytes(payload,'big')

def decode_bytes(n: int) -> Any:
    n=nat(n)
    if n==0: raise ValueError('Missing length marker')
    width=n.bit_length()-1
    if width%8: raise ValueError('Not a byte-string candidate')
    payload=(n^(1<<width)).to_bytes(width//8,'big')
    return json.loads(payload.decode('ascii'))

def search(start: int=1, stop: int|None=None) -> int|None:
    """Ideal unbounded fair search, or a finite prefix with stop supplied.

    This reference enumerates canonical JSON byte strings, not the proposed
    compact machine's future instruction stream. No state bound is inferred.
    """
    n=nat(start)
    while stop is None or n<stop:
        try: result=check(decode_bytes(n))
        except (ValueError,UnicodeError): pass
        else:
            if result['refutation']: return n
        n+=1
    return None

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',type=Path)
    args=ap.parse_args()
    try: result=check(json.loads(args.certificate.read_text()))
    except (ValueError,UnicodeError) as exc:
        print(json.dumps({'valid':False,'error':str(exc)},indent=2)); raise SystemExit(1)
    print(json.dumps(result,indent=2))
if __name__=='__main__': main()
