#!/usr/bin/env python3
"""Erase one phase-proved zero-transfer occurrence and rebase all jumps.

The source equivalence relies on the independently audited phase invariant;
finite CFG contraction alone would not justify deleting the nonzero guard.
All remaining leaf effects and successor identities are checked exactly.
"""
from pathlib import Path
import json, sys, time
import control_rebased_rotations as g


def run():
    g.setup(True)
    r,c=g.r,g.c
    old,root=r.NODES,r.ROOT
    prefix='11101001011000110'
    def edge_at(p):
        e=('N',root)
        for b in p:e=old[e[1]][int(b)]
        return e
    removed_edge=edge_at(prefix)
    assert removed_edge[0]=='N'
    assert g.graph(old,removed_edge[1])==[('D',6,0,1),('I',5,2),('J',0)]
    assert prefix[-1]=='0'
    parent=prefix[:-1];sibling=edge_at(parent+'1')
    leaves,ix=g.leaves(old,root)
    removed=[i for i,(p,e) in enumerate(leaves) if p.startswith(prefix)]
    assert len(removed)==3 and removed==list(range(removed[0],removed[0]+3))
    lo,hi=removed[0],removed[-1]+1
    ref=g.graph(old,root)
    remaining=[i for i in range(len(ref)) if i not in removed]
    renumber={i:j for j,i in enumerate(remaining)}
    def target(i):
        if lo<=i<hi:
            assert i==lo,('external entrance into skipped nonzero body',i)
            i=hi
        return renumber[i]
    contracted=[]
    for i in remaining:
        row=ref[i]
        if row[0]=='H':contracted.append(row)
        elif row[0]=='D':contracted.append((*row[:2],target(row[2]),target(row[3])))
        elif row[0]=='I':contracted.append((*row[:2],target(row[2])))
        else:contracted.append(('J',target(row[1])))
    new,seen={},{}
    def visit(e,p,skip=False):
        if p==parent and not skip:return visit(sibling,parent+'1',True)
        if e[0]!='N':return e
        a,b=old[e[1]];pair=(visit(a,p+'0',skip),visit(b,p+'1',skip))
        if pair not in seen:seen[pair]=len(new);new[len(new)]=pair
        return ('N',seen[pair])
    nr=visit(('N',root),'')[1]
    fixed=g.rebase(new,nr,contracted)
    result={'erased_prefix':prefix,'erased_original_leaf_indices':removed,'phase_requirement':'logical X=0 at this loop entry; all nonzero loop paths unreachable','remaining_leaves':len(contracted)}
    if fixed is None:
        result['status']='contracted control not representable with current break/continue options'
    else:
        nn,nr,changes,ambiguity=fixed
        result.update(control_changes=changes,ambiguous_leaves=ambiguity,dag_nodes=len(nn),metrics=r.metrics(nn,nr))
        table=r.gc(r.emit(nn,nr));result['states']=len(table)//2
        check=c.run(table,nn,nr);result['affine']=check
        folder=Path(__file__).resolve().parent/'control-rebased-candidates'
        path=folder/f'phase-erased-{len(table)//2}'
        path.with_suffix('.json').write_text(json.dumps({'nodes':nn,'root':nr,'contraction':{k:v for k,v in result.items() if k!='affine'}},indent=2)+'\n')
        path.with_suffix('.tm').write_text('#! start 0\n'+''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t)in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1]))))
        result['status']='conditional_affine_pass' if not check['failures'] else 'conditional_affine_rejected'
    (Path(__file__).resolve().parent/'phase-erased-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='affine'},indent=2))
    if 'affine' in result:print('affine',result['affine']['cases_checked'],'failures',result['affine']['failures'][:8], 'failure_count',len(result['affine']['failures']))


if __name__=='__main__':run()
