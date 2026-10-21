#!/usr/bin/env python3
"""Check exact source-prefix binding for K215 independently of allocation.

The known finite prefix includes the marker at -1. Every compound-child
decoder path must preserve that entire prefix and advance the head once.
All tape cells read by these paths must lie in this known prefix. Actual
primitive execution is covered separately by the universal runtime proof.
"""
from pathlib import Path
from collections import defaultdict
import argparse,json
import reconstruct215 as c

def decode(T,tree):
    groups=defaultdict(set);occurrences=[];helper_rows=set();steps=0;longest=0
    def walk(n,p,q):
        nonlocal steps,longest
        if c.leaf(n):return
        groups[q].add(n);occurrences.append((p,q,n))
        for bit,ch in enumerate(n):
            if c.leaf(ch):continue
            tape={i:int(x)for i,x in enumerate(p+str(bit))};tape[-1]=1
            before=tape.copy();head=len(p);state=q;count=0
            for _ in range(100):
                if head==len(p)+1:break
                c.require(head in tape,f'Decoder reads unknown cell: {p}/{bit}')
                read=tape[head]
                c.require((state,read)in T,'Undefined decoder transition')
                if count:helper_rows.add((state,read))
                w,d,state=T[state,read];tape[head]=w;head+=d;count+=1
            c.require(head==len(p)+1 and tape==before,f'Decoder does not preserve prefix: {p}/{bit}')
            steps+=count;longest=max(longest,count)
            walk(ch,p+str(bit),state)
    walk(tree,'',84)
    return groups,occurrences,helper_rows,steps,longest

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent-table',type=Path,required=True)
    ap.add_argument('--parent-source',type=Path,required=True)
    ap.add_argument('--candidate-table',type=Path,required=True)
    ap.add_argument('--candidate-source',type=Path,required=True)
    ap.add_argument('--plan',type=Path,default=Path(__file__).with_name('k215_decoder_plan.json'))
    ap.add_argument('--recipe',type=Path,default=Path(__file__).with_name('k215_transition_recipe.json'))
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();recipe=json.loads(a.recipe.read_text());plan=json.loads(a.plan.read_text())
    pins=((a.parent_table,'parent_native_sha256'),(a.parent_source,'parent_source_sha256'),(a.candidate_table,'candidate_native_sha256'),(a.candidate_source,'candidate_source_sha256'))
    for path,key in pins:c.require(c.sha(path.read_bytes())==recipe[key],f'Wrong {key}')
    old=c.parse(json.loads(a.parent_source.read_text()));new=c.parse(json.loads(a.candidate_source.read_text()))
    parent,_,_,_,_=decode(c.table(a.parent_table.read_bytes()),old)
    current,occ,helpers,steps,longest=decode(c.table(a.candidate_table.read_bytes()),new)
    parent_roles=defaultdict(set)
    for q,nodes in parent.items():
        for n in nodes:parent_roles[n].add(q)
    assigned={}
    for item in plan['assignments']:
        n=c.at(new,item['path']);c.require(not c.leaf(n),'Plan names a leaf')
        c.require(n not in assigned,'Duplicate new subtree assignment')
        c.require(n not in parent_roles,'New assignment is an unchanged parent subtree')
        assigned[n]=item['q']
    changed_occ=0;unchanged_occ=0
    for p,q,n in occ:
        if n in assigned:
            c.require(q==assigned[n],f'Changed subtree bound to wrong state at {p}')
            changed_occ+=1
        else:
            c.require(q in parent_roles[n],f'Preserved subtree bound to wrong parent state at {p}')
            unchanged_occ+=1
    c.require(set(assigned)<={n for p,q,n in occ},'Unused planned subtree')
    receipt={'status':'EXACT_K215_ALL_PREFIX_BINDINGS_PASS',
             'candidate_native_sha256':recipe['candidate_native_sha256'],
             'candidate_source_sha256':recipe['candidate_source_sha256'],
             'compound_occurrences':len(occ),'distinct_compound_subtrees':len({n for p,q,n in occ}),
             'bound_decoder_states':len(current),'state_subtree_roles':sum(map(len,current.values())),
             'new_distinct_subtree_assignments':len(assigned),
             'new_subtree_occurrences':changed_occ,'retained_subtree_occurrences':unchanged_occ,
             'literal_prefix_transition_checks':steps,'maximum_compound_edge_duration':longest,
             'intermediate_helper_rows':len(helpers),
             'scope':'Exact known-prefix execution and parent/new source-role bindings for every compound occurrence. Primitive successors, complete blank startup and logical calibration are separate obligations.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);c.dump(a.output,receipt)
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
