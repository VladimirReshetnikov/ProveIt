#!/usr/bin/env python3
"""Independent integer-interval proof of two register sources' control equality.

Unlike the inherited tree rotation checker, this checker does not replay
rotations, recurse through a program tree, or import supplied executable code.
It interprets each prefix-free codeword as a dyadic integer interval and
compares all next-instruction indices for both decrement outcomes. The
RegisterPath consumption convention truncates/pads the pointer to the leaf
codeword before applying arithmetic, so the compared instruction-index
system exactly projects the original source semantics from an empty pointer.
"""
import argparse,bisect,hashlib,json,sys
from pathlib import Path

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Proof checking requires enabled assertions; do not use -O or -OO.')

BASELINE_SHA256='74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'
CANDIDATE_SHA256='7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(path):
    sites=json.loads(path.read_text())
    assert isinstance(sites,list) and sites
    assert all(isinstance(x,list) and len(x)==3 for x in sites)
    depth=max(len(p) for p,_,_ in sites)
    lower=[];upper=[];descriptors=[]
    for p,kind,arg in sites:
        assert p and isinstance(p,str) and set(p)<={'0','1'}
        assert kind in {'CI','CD','CB','CC','CH'}
        if kind in {'CI','CD'}:assert type(arg) is int and 0<=arg<9
        elif kind in {'CB','CC'}:assert type(arg) is int and arg>=1
        else:assert arg is None
        lo=int(p,2) << (depth-len(p));hi=(int(p,2)+1) << (depth-len(p))
        lower.append(lo);upper.append(hi);descriptors.append((kind,arg))
    assert lower[0]==0 and upper[-1]==1<<depth
    assert upper[:-1]==lower[1:], 'Not an ordered complete prefix code'
    def leaf(v,n):
        assert 0<=n<=depth and 0<=v<(1<<n)
        x=v << (depth-n)
        index=bisect.bisect_right(lower,x)-1
        assert lower[index]<=x<upper[index]
        assert x==lower[index], 'Successor has a nonzero unused suffix after decoding'
        return index
    def inc(v,n):return ((v+1) % (1<<n),n)
    def strip(v,n,target,count):
        while count and n:
            if v&1==target:count-=1
            v>>=1;n-=1
        return v,n
    graph=[]
    for p,kind,arg in sites:
        v,n=int(p,2),len(p)
        if kind=='CH':succ=[]
        elif kind=='CI':succ=[leaf(*inc(v,n))]
        elif kind=='CD':succ=[leaf(*inc(v,n)),leaf(*inc(*strip(v,n,0,1)))]
        elif kind=='CB':succ=[leaf(*inc(*strip(v,n,0,arg)))]
        else:succ=[leaf(*strip(v,n,1,arg))]
        graph.append([kind,arg,succ])
    assert leaf(0,0)==0
    return sites,graph,depth

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('baseline',type=Path);ap.add_argument('candidate',type=Path)
    ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    assert digest(a.baseline)==BASELINE_SHA256,'Unexpected calibrated baseline source bytes'
    assert digest(a.candidate)==CANDIDATE_SHA256,'Unexpected candidate source bytes'
    s0,g0,d0=verify(a.baseline);s1,g1,d1=verify(a.candidate)
    assert len(s0)==len(s1)
    assert g0==g1, 'Different instruction descriptor or successor index'
    changed=sum(x[0]!=y[0] for x,y in zip(s0,s1))
    edges=sum(len(x[2]) for x in g0)
    result=dict(status='PASS_INDEPENDENT_SOURCE_CONTROL_EQUALITY',
      baseline_sha256=digest(a.baseline),candidate_sha256=digest(a.candidate),
      checker_sha256=digest(Path(__file__)),leaves=len(s0),
      exact_input_pins_checked=True,assertions_enabled=__debug__,
      guarded_successors=edges,halt_leaves=sum(x[0]=='CH' for x in g0),
      baseline_maximum_depth=d0,candidate_maximum_depth=d1,changed_codewords=changed,
      all_instruction_descriptors_identical=True,all_guarded_successor_indices_identical=True,
      complete_prefix_codes_verified_by_dyadic_interval_partition=True,
      every_generated_successor_equals_decoded_leaf_after_infinite_zero_padding=True,
      initial_instruction_index=0,
      common_control_graph_sha256=hashlib.sha256(json.dumps(g0,separators=(',',':')).encode()).hexdigest(),
      proof='Project every RegisterPath state to (decoded leaf index, unchanged register file). Consumption makes the next decoded index depend only on the current leaf and its decrement guard. All labels, updates, halt flags, and successor indices coincide; induction on source steps gives exact instruction-index bisimulation for every natural register vector. Empty pointers both decode to index zero.',
      limitations='Ordinary finite certificate; no binary-TM runtime claim and no newly executed Lean/Rocq proof.')
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
