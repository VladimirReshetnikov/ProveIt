"""Finite bisimulation of the literal program after erasing silent jumps.

Every class has one command/register label and matching successor classes for
each zero/nonzero guard. The observer accepts only actual visible-action PCs;
it never identifies an arbitrary jump boundary with an action entry.
"""
from action_contract import normalizer,walk

def build_quotient(nodes,successor):
    normalize=normalizer(nodes,successor);leaves={}
    def visit(q,p):
        for b,e in enumerate(nodes[q]):
            path=p+str(b);op,*arg=e.split()
            if op=='CN':visit(int(arg[0]),path)
            elif op not in ('CB','CC'):leaves[path]=(op,int(arg[0]) if arg else None)
    visit(0,'');assert len(leaves)==4533
    edges={};normalizations=[]
    for p,(op,r) in leaves.items():
        targets=[]
        if op!='CH':
            for zero in ((True,False) if op=='CD' else (None,)):
                result,chain,terminal=normalize(successor(p,op,r,zero))
                targets.append(terminal[0])
                normalizations.append(dict(path=p,zero=zero,target_pc=result,target_leaf=terminal[0],chain=chain))
        edges[p]=tuple(targets)
    ids={};partition={p:ids.setdefault(label,len(ids)) for p,label in leaves.items()}
    rounds=[len(ids)]
    while True:
        ids={};new={}
        for p,label in leaves.items():
            key=(label,tuple(partition[t] for t in edges[p]))
            new[p]=ids.setdefault(key,len(ids))
        rounds.append(len(ids))
        if new==partition:break
        partition=new
    groups={}
    for p,c in partition.items():groups.setdefault(c,[]).append(p)
    for members in groups.values():
        representative=members[0]
        assert all(leaves[p]==leaves[representative] and
                   tuple(partition[t] for t in edges[p])==tuple(partition[t] for t in edges[representative])
                   for p in members)
    return dict(action_leaves=leaves,successors=edges,classes=partition,
                classes_count=len(groups),refinement_rounds=rounds,
                nontrivial_classes=[members for members in groups.values() if len(members)>1],
                normalizations=normalizations)

def quotient_observer(original_canon,nodes,quotient):
    def observe(left,right):
        l,r=original_canon(left,right)
        if len(r)<3 or r[-1][0]!='box' or r[-2]!=(1,0,1):return l,r
        gap=r[-3]
        if len(gap)!=3 or gap[0]!=0:return l,r
        prefix=r[:-3]
        if any(len(s)!=3 or s[0] not in (0,1) or s[1]!=0 for s in prefix):return l,r
        length=sum(s[2] for s in prefix)
        if gap[1]<0 or gap[2]+length<40:return l,r
        pc=''.join(str(b)*c for b,a,c in prefix)
        try:path,op,reg=walk(nodes,pc)
        except AssertionError:return l,r
        if path not in quotient['classes']:return l,r
        return l,(('action_class',quotient['classes'][path]),('gap_at_least',40),r[-2],r[-1])
    return observe
