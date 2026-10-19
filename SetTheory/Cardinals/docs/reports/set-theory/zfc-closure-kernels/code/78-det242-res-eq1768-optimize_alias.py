#!/usr/bin/env python3
"""Trade one C-congruence axiom for two, keeping a ground alias at four bits.

The axiom replacement is interderivable using the retained equality axioms.
The fresh nullary symbol o is a conservative explicit term definition.
"""
from pathlib import Path
import json
from hashlib import sha256
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'reference'))
from equational_search import Kernel,freeze,nodes,variables
from build_equations import encode_packet,decode_packet,canonical_equation,pretty,optimized_equation
D=('d',);O=('o',);ONE=('I',D,D)

def Eq(x,y):return ('p_Eq',x,y)
def C(x,y,z):return ('C',x,y,z)
def lit(sign,x,y):return (sign,'Eq',x,y)

def split_clauses():
    return [
      [lit(False,'x','u'),lit(False,'y','v'),lit(True,C('x','y','z'),C('u','v','z'))],
      [lit(False,'z','w'),lit(True,C('x','y','z'),C('x','y','w'))]
    ]

def alias(t):
    if t==ONE:return O
    return t if isinstance(t,str) else (t[0],)+tuple(alias(x) for x in t[1:])

def fused(t):
    if t==('top',):return D
    return t if isinstance(t,str) else (t[0],)+tuple(fused(x) for x in t[1:])

def build():
    inp=json.loads((ROOT/'output/combined.json').read_text());old=freeze(inp['equations'])
    sig=dict(inp['signature']);sig['o']=0
    split=[];certs=[]
    for clause in split_clauses():
        eq,cert=optimized_equation([clause]);split.append(tuple(fused(t) for t in eq));certs.append(cert)
    # Index 14 is exactly the ternary C congruence; reconstruct its source
    # equation below rather than selecting an unverified row by position alone.
    expected=('d',),('N',('N',('d',),('N',Eq('x0','y0'),Eq('x1','y1'))),('N',('d',),('N',Eq('x2','y2'),('N',('d',),Eq(C('x0','x1','x2'),C('y0','y1','y2'))))))
    assert old[14]==expected
    eqs=[]
    for i,eq in enumerate(old):
        eqs.extend(split if i==14 else [eq])
    eqs=[tuple(alias(t) for t in eq) for eq in eqs]+[(O,ONE)]
    start,target=freeze(inp['start']),freeze(inp['target'])
    Kernel(sig,eqs,start,target)
    bits,stats=encode_packet(eqs,sig,start,target)
    assert decode_packet(bits,list(sig))==(sig,[canonical_equation(e) for e in eqs],start,target)
    assert stats['opcode_width']==4 and stats['local_variable_capacity']==5
    data={'name':'FC13B_incidence_truth_alias','signature':sig,'equations':eqs,'start':start,'target':target,
          'status':'complete 4-bit-opcode equational packet; ordinary equiconsistency; no binary TM state count'}
    stats['packet_sha256']=sha256((bits+'\n').encode()).hexdigest()
    stats['split_boolean_certificates']=certs
    out=ROOT/'output'
    (out/'alias.json').write_text(json.dumps(data,indent=2)+'\n')
    (out/'alias.bits').write_text(bits+'\n')
    (out/'alias.equations').write_text('\n'.join(f'{i}: {pretty(a)} = {pretty(b)}' for i,(a,b) in enumerate(eqs))+'\n')
    (out/'alias_metrics.json').write_text(json.dumps(stats,indent=2)+'\n')
    return stats

if __name__=='__main__':print(json.dumps(build(),indent=2))
