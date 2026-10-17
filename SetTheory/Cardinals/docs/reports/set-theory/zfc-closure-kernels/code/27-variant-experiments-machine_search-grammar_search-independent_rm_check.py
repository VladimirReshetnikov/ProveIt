#!/usr/bin/env python3
"""Independent tuple-based checker for the delivered finite RM certificate.

This module does not import the certificate generator or the earlier string/
integer RM simulator. Trailing zeroes are canonically discarded; the decoder
supplies them when a deeper leaf is read.
"""
from collections import Counter

def canon(bits):
    bits=list(bits)
    while bits and bits[-1]==0:bits.pop()
    return tuple(bits)

def input_pc(text):
    assert isinstance(text,str) and set(text)<={'0','1'}
    return canon(int(b) for b in text)

def decode(nodes,root,pc):
    state=root;path=[]
    while True:
        bit=pc[len(path)] if len(path)<len(pc) else 0;path.append(bit)
        edge=nodes[state][bit]
        if edge[0]!='N':return edge,tuple(path)
        state=edge[1]

def increment(path):
    path=list(path)
    while path and path[-1]==1:path.pop()
    if path:path[-1]=1
    return canon(path)

def drop_through(path,bit,count):
    path=list(path)
    while path and count:
        count-=path.pop()==bit
    return path

def successor(edge,path,positive):
    kind=edge[0]
    if kind=='I' or(kind=='D' and positive):return increment(path)
    if kind=='D':return increment(drop_through(path,0,1))
    if kind=='B':return increment(drop_through(path,0,edge[1]))
    if kind=='C':return canon(drop_through(path,1,edge[1]))
    raise AssertionError('halt has no successor')

def segment(nodes,root,pc):
    effects=Counter()
    for steps in range(1000):
        edge,path=decode(nodes,root,pc)
        if edge[0] in ('D','H'):return effects,pc,steps
        if edge[0]=='I':effects[edge[1]]+=1
        pc=successor(edge,path,False)
    raise AssertionError('nonterminating or overly long increment segment')

def check(first,second,certificate):
    nodes_a,root_a=first;nodes_b,root_b=second;largest=0
    normalized=[(input_pc(a),input_pc(b),j,k) for a,b,j,k in certificate]
    assert normalized
    def edge_check(a,b,index):
        nonlocal largest
        assert type(index) is int and 0<=index<len(normalized)
        ea,pa,na=segment(nodes_a,root_a,a);eb,pb,nb=segment(nodes_b,root_b,b)
        largest=max(largest,na,nb)
        assert ea==eb and (pa,pb)==normalized[index][:2]
    edge_check((),(),0)
    for a,b,j,k in normalized:
        ea,pa=decode(nodes_a,root_a,a);eb,pb=decode(nodes_b,root_b,b)
        if ea==eb==('H',):continue
        assert ea==eb and ea[0]=='D'
        edge_check(successor(ea,pa,True),successor(eb,pb,True),j)
        edge_check(successor(ea,pa,False),successor(eb,pb,False),k)
    return largest

def main():
    import json
    import cost_search as s
    n,e,k=s.rot.options(s.NODES)[0];nodes,root=s.rot.mutate(s.NODES,s.ROOT,n,e)
    certificate=json.loads((s.HERE/'results/rotation0_rm_certificate.json').read_text())
    a=check((s.NODES,s.ROOT),(nodes,root),certificate)
    b=check((nodes,root),(s.NODES,s.ROOT),[[y,x,j,k] for x,y,j,k in certificate])
    bad=[row[:] for row in certificate];bad[0][0]='1'+bad[0][0]
    try:check((s.NODES,s.ROOT),(nodes,root),bad)
    except AssertionError:pass
    else:raise AssertionError('corrupt initial relation accepted')
    output={'entries':len(certificate),'both_directions':True,'maximum_segment':max(a,b),
            'malformed_initial_relation_rejected':True,'independence':'New tuple/bit-prefix semantics; no generator or prior string/integer RM interpreter functions imported.'}
    (s.HERE/'candidate/independent_rm_result.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__':main()
