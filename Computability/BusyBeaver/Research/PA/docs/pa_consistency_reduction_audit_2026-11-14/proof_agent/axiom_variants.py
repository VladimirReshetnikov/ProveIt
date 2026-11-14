#!/usr/bin/env python3
"""Formula-level, propositionally justified variants of PA196's AX emitter.

This module emits macro tokens only. It does not by itself allocate or certify
any Turing machine. Tokens D,H,A push the old accumulator and load a register;
P pushes it and loads zero; C pops and forms 4*CantorPair; i increments.
"""
from pathlib import Path
import itertools,json,re
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/'ProveIt/Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Source/AXProgram.lean'
TOKEN={'push':'P','copyD':'D','copyH':'H','copyA':'A','cons':'C','incT':'i','readH':'r','readDCons':'s','copyGuard':'g','compareGuard':'j','close':'z'}
def I(x,y): return (0,x,y)
def M(x,y): return (1,x,y)
def U(x,b): return (2,b,x)
def E(x,y): return (3,x,y)
def N(x): return I(x,1)
def And(x,y): return N(I(x,N(y)))
def Ex(x,p): return N(U(x,N(p)))
def emit(x):
    if isinstance(x,str): return x
    if isinstance(x,int): return 'P'+'i'*x
    r,a,b=x
    return emit(a)+emit(b)+'C'+'i'*r

def formulas(bits=0):
    # h1,h2,h3,h4,h5,h6 are emitted in baseline order.
    # Bits 0,1,2 permute the curried antecedents of h3,h4,h6.
    # Bit 3 swaps Δ and V in the outer guarded gate.
    # Bit 4 swaps the conjuncts in S. Bit 5 swaps the first
    # two antecedents of M(H,D) -> (A -> M(A,D)) inside S.
    h1=I(Ex('D',U('D','H')),'H')
    h2=I(U('D',U('A','H')),U('A',U('D','H')))
    a,b,c=M('H','D'),E('H','A'),M('A','D')
    h3=I(b,I(a,c)) if bits&1 else I(a,I(b,c))
    a,b,c=E('H','D'),M('A','H'),M('A','D')
    h4=I(b,I(a,c)) if bits&2 else I(a,I(b,c))
    h5=Ex('D',E('H','D'))
    a,b,c=U('D','A'),U('D',I('A','H')),U('D','H')
    h6=I(b,I(a,c)) if bits&4 else I(a,I(b,c))
    delta=I(E('H','D'),U('A',E('H','D')))
    vac=I(M('H','D'),U('A',M('H','D')))
    p=I('A',M('A','D'))
    left=I('A',I(M('H','D'),M('A','D'))) if bits&32 else I(M('H','D'),p)
    right=I(M('A','D'),'A')
    s=U('D',And(right,left) if bits&16 else And(left,right))
    q=U('A',I(s,N(p)))
    gate=N(I(vac,I(delta,q))) if bits&8 else N(I(delta,I(vac,q)))
    return [h1,h2,h3,h4,h5,h6],gate

def baseline_tokens():
    text=SRC.read_text().split('def blocks :',1)[1].split('def program :',1)[0]
    return ''.join(TOKEN[x] for x in re.findall(r'\(\.(\w+),',text))
BASE=baseline_tokens()
HEADS,GATE=formulas()
EMITTED=''.join(map(emit,HEADS))+emit(GATE)
# Every formula emitter starts by pushing the previous accumulator;
# original h1/h5 use 'P i C' to form negation, exactly as emit does.
assert BASE.endswith(EMITTED+'gjz'), (BASE,EMITTED)
PREFIX=BASE[:-len(EMITTED+'gjz')]

def rename(expr,mapping):
    if isinstance(expr,str): return mapping.get(expr,expr)
    if isinstance(expr,int): return expr
    r,a,b=expr
    return r,rename(a,mapping),rename(b,mapping)

PERMS=list(itertools.permutations('DHA'))
def tokens(bits=0,order=None,permutations=None,h1_contrapositive=False,gate_reverse=False):
    heads,gate=formulas(bits)
    if h1_contrapositive:
        raise ValueError('Unsupported: explosion depends on h1; do not use this candidate')
    if permutations is not None:
        assert len(permutations)==6
        heads=[rename(f,dict(zip('DHA',PERMS[k]))) for f,k in zip(heads,permutations)]
    if gate_reverse:
        gate=rename(gate,{'D':'H','H':'D'})
    if order is None: order=range(6)
    assert sorted(order)==list(range(6))
    return PREFIX+''.join(emit(heads[i]) for i in order)+emit(gate)+'gjz'

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(); p.add_argument('--output',default='proof_agent/axiom_variants.json'); a=p.parse_args()
    out={'baseline_tokens':BASE,'prefix':PREFIX,'notes':'64 formula equivalence variants; literal token baseline asserted; allocation and correctness transfer required',
         'variants':[{'mask':i,'tokens':tokens(i),'count':len(tokens(i))} for i in range(64)]}
    Path(a.output).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'output':a.output,'baseline_length':len(BASE),'prefix':PREFIX,'baseline_matches':tokens()==BASE,'variants':64},indent=2))
