#!/usr/bin/env python3
"""Extract the six independent PA196 AX head emitters from symbolic execution.

This checks their exact arithmetic expression trees and stack effects. It does
not claim that a reordered source has the old primitive CFG or literal TM.
"""
import re,sys,json,itertools,collections
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
import grammar as g
raw=(ROOT/'vendor/PA196/Source/AXProgram.lean').read_text()
ops=re.findall(r'\.(\w+)',raw.split('def program : List AXMacro.Op := [')[1].split(']')[0])
blocks=[(name,int(a),int(b)) for name,a,b in re.findall(r'\(\.(\w+), (\d+), (\d+)\)',raw.split('def blocks')[1].split('def program')[0])]
atom_for=dict(push='node49',copyD='node55',copyH='node58',copyA='node70',cons='node65',incT='inc1',readH='node72',readDCons='node75',copyGuard='node142')
expansion=dict(push=['push'],copyD=['push','copyD'],copyH=['push','copyH'],copyA=['push','copyA'],cons=['cons'],incT=['incT'],readH=['readH'],readDCons=['readD','push','copyD','cons'])
assert [atom_for[t] for t,a,b in blocks[:-2]]+["x65"]==g.seq
assert [op for name,a,b in blocks[:-3] for op in expansion[name]]==ops

ZERO=('zero',)
def atom(i):return ('atom',i)
def initial():return dict(t=atom(0),a=atom(1),d=atom(2),h=atom(3),fields=[atom(4),atom(5)],stack=[])
def plus(x,y):return y if x==ZERO else x if y==ZERO else ('add',x,y)
def execute(op,st):
    st={**st,'fields':st['fields'].copy(),'stack':st['stack'].copy()}
    if op=='push':st['stack'].insert(0,st['t']);st['t']=ZERO
    elif op=='cons':st['t']=('im',st['stack'].pop(0),st['t'])
    elif op=='incT':st['t']=('succ',st['t'])
    elif op.startswith('copy'):st['t']=plus(st['t'],st[op[-1].lower()])
    elif op.startswith('read'):k=op[-1].lower();st[k]=plus(st[k],st['fields'].pop(0))
    else:raise ValueError(op)
    return st
def run(seq,st=None):
    st=initial() if st is None else st
    for op in seq:st=execute(op,st)
    return st

def collapse_tree(t):
    if t in g.atoms:return g.atoms[t]
    return tuple(map(collapse_tree,t))

def main():
    state=initial();trace=[state]
    for op in ops:state=execute(op,state);trace.append(state)
    result=trace[-1];assert len(result['stack'])==9
    op_ends=[];head_blocks=[]
    for head in range(1,7):
        expr=result['stack'][6-head]
        matches=[i for i,s in enumerate(trace) if s['t']==expr and len(s['stack'])==head+2]
        assert len(matches)==1,(head,matches)
        op_ends.append(matches[0])
    rho=result['stack'][6]
    rhoends=[i for i,s in enumerate(trace) if s['t']==rho and len(s['stack'])==2]
    assert len(rhoends)==1;op_start=rhoends[0]
    op_boundaries=[0]
    for name,a,b in blocks[:-3]:op_boundaries.append(op_boundaries[-1]+len(expansion[name]))
    assert op_boundaries[-1]==len(ops)
    starts=[op_start]+op_ends[:-1]
    for head,start,end in zip(range(1,7),starts,op_ends):
        i=op_boundaries.index(start);j=op_boundaries.index(end)
        head_blocks.append(dict(head=head,operation_interval=[start,end],atomic_interval=[i,j],
                                source_ordinal_interval=[blocks[i][1],blocks[j-1][2]],
                                operations=ops[start:end],atoms=g.seq[i:j]))
    first=head_blocks[0]['atomic_interval'][0];last=head_blocks[-1]['atomic_interval'][1]
    prefix=g.seq[:first];suffix=g.seq[last:]
    # Every permutation must preserve all scalar registers and have precisely
    # the permuted six head formulas followed by the same three older entries.
    for perm in itertools.permutations(range(6)):
        changed=ops[:op_start]+[op for i in perm for op in head_blocks[i]['operations']]+ops[op_ends[-1]:]
        actual=run(changed)
        want={**result,'stack':[result['stack'][5-i] for i in reversed(perm)]+result['stack'][6:]}
        assert actual==want,perm
    ct=collapse_tree(g.nodes['x67']);intervals={}
    def visit(t,i=0):
        if isinstance(t,str):return i+1
        j=visit(t[0],i);k=visit(t[1],j);intervals[i,k]=t;return k
    assert visit(ct)==200
    for item in head_blocks:item['exact_original_tree_subtree']=tuple(item['atomic_interval']) in intervals
    report=dict(atomic_word_length=len(g.seq),symbolic_operations=len(ops),composite_blocks=len(blocks),
                head_blocks=head_blocks,prefix_atoms=prefix,suffix_atoms=suffix,
                all_720_permutations_symbolic_pass=True,
                scope='Exact symbolic expression/stack computation only. Reordered source control graphs, arithmetic completeness, physical allocation and literal runtime require separate validation.')
    (ROOT/'results/ax_head_intervals.json').write_text(json.dumps(report,indent=2)+'\n')
    print('prefix',len(prefix),'suffix',len(suffix))
    for b in head_blocks:print('head',b['head'],'operations',b['operation_interval'],'atoms',b['atomic_interval'],'source',b['source_ordinal_interval'],'subtree',b['exact_original_tree_subtree'])
    print('all720 permutations symbolically verified')

if __name__=='__main__':main()
