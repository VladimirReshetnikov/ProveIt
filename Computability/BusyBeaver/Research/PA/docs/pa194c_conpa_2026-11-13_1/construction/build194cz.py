#!/usr/bin/env python3
"""Zero-register jump variant of PA194C; an additional 194-state search seed.

Proof: joint nine-bit positivity-mask invariant, plus fresh symbolic physical
contracts (including the unreachable positive source26 branch).
"""
from pathlib import Path
import hashlib,json,time
import build194 as p
import build194c as x
c=x.c
HERE=Path(__file__).resolve().parent

def succ(code,pc,mask):
    z=code[pc]
    if z[0]=='jump':return [(z[1],mask)]
    if z[0]=='inc':return [(z[2],mask|(1<<z[1]))]
    if z[0]=='dec':
        bit=1<<z[1]
        return [(z[3],mask&~bit),(z[3],mask)] if mask&bit else [(z[2],mask)]
    assert z[0]=='halt'
    return []

def closure(code):
    seen={(25,1)};todo=list(seen)
    for pc,m in todo:
        for item in succ(code,pc,m):
            assert 0<=item[0]<len(code) and 0<=item[1]<512
            if item not in seen:seen.add(item);todo.append(item)
    assert all(item in seen for pc,m in seen for item in succ(code,pc,m))
    return seen

def build():
    assert __debug__
    started=time.monotonic()
    parent=p.read_table(HERE/'tables/pa194c.native.tm')
    rows=dict(parent);rows[27,1]=(1,True,21)
    dense,labels=p.dense_table(rows)
    for name,text in [('pa194cz.native.tm',p.table_text(rows)),
                      ('pa194cz.tm',p.table_text(dense)),
                      ('pa194cz.labels.json',json.dumps(labels)+'\n')]:
        (HERE/'tables'/name).write_text(text)
    old_machine,old_nodes=c.machine,c.raw_nodes
    def machine():
        tab,lab=old_machine();tab.update(x.EDITS);tab[27,1]=(1,True,21)
        return tab,lab
    def nodes():
        nn=old_nodes();nn['node163']=('node6','node147')
        nn['node170']=(('node36',('node167','node145')),'node57')
        assert nn['node22']==(('leaf','dec',8),('leaf','breakTo',1))
        nn['node22']=(('leaf','dec',8),('leaf','dec',6))
        return nn
    c.machine,c.raw_nodes=machine,nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    tree=c.read_grammar(HERE/'source/pa194.grammar.json')
    raw,index,shape=c.build(tree)
    assert len(raw)==402 and len(shape)==67
    folds=json.loads((HERE/'source/pa194.folds.json').read_text())
    reconstructed,aliases=p.apply_folds(raw,folds)
    assert rows==reconstructed
    local=p.check_local_folds(raw,rows,aliases,folds)
    sites,cfg,contracts=c.source(tree)
    olds=json.loads((HERE/'source/pa194c.sites.json').read_text())
    new_sites=[[''.join(map(str,path)),op,arg] for path,op,arg in sites]
    assert [i for i,(a,b) in enumerate(zip(olds,new_sites)) if a!=b]==[26]
    assert new_sites[26]==[olds[26][0],'dec',6]
    old=json.loads((HERE/'source/pa194c.instructions.json').read_text())
    new=json.loads(json.dumps(cfg))
    assert [i for i,(a,b) in enumerate(zip(old,new)) if a!=b]==[26]
    assert old[26]==['jump',34] and new[26]==['dec',6,34,27]
    r0,r1=closure(old),closure(new)
    assert r0==r1 and len(r0)==263244
    assert all(succ(old,pc,m)==succ(new,pc,m) for pc,m in r0)
    masks=sorted(m for pc,m in r0 if pc==26)
    assert masks and all(m&64==0 for m in masks)
    inv=dict(inductive_pairs=len(r0),contains_seed=True,all_abstract_successors_closed=True,
             concrete_seed=[25,[2,0,0,0,0,0,0,0,0]],site26_masks=masks,R6_zero_at26=True,
             shared_abstract_transitions_equal=True,
             closure_sha256=hashlib.sha256(json.dumps(sorted(r0),separators=(',',':')).encode()).hexdigest())
    print('joint invariant PASS',len(r0),flush=True)
    assert len(contracts)==4750
    runtime=c.validate(rows,contracts)
    assert runtime['ok']
    blank=p.startup(rows,sites[25][0]);assert blank['steps']==58168
    for suffix,data in [('sites',new_sites),('instructions',new)]:
        (HERE/'source'/('pa194cz.'+suffix+'.json')).write_text(json.dumps(data)+'\n')
    (HERE/'tables/unfolded201cz.native.tm').write_text(p.table_text(raw))
    receipt=dict(family='PA194CZ',status='PASS',working_states=194,rows=388,
        source_sites=len(sites),source_contracts=len(contracts),local_fold_cases=len(local['cases']),
        source_edit={'site':26,'before':old[26],'after':new[26]},
        native_edit={'row':[27,1],'before':parent[27,1],'after':rows[27,1]},
        invariant=inv,symbolic_runtime=runtime,startup=blank,
        sha256={nm:hashlib.sha256((HERE/'tables'/nm).read_bytes()).hexdigest()
                for nm in ('pa194cz.native.tm','pa194cz.tm','unfolded201cz.native.tm')},
        seconds=round(time.monotonic()-started,6),kernel_checked=False,
        proof='Source runs agree by induction on the common positivity-mask invariant; literal simulation is checked for both branches at source26.')
    (HERE/'evidence/pa194cz.verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    return rows,sites,cfg,receipt

if __name__=='__main__':build()
