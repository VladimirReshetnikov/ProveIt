#!/usr/bin/env python3
"""Reconstruct and verify PA194G from the frozen inputs, without search/network.

Standard library only. This is executable symbolic evidence, not a newly
kernel-checked PA theorem. Run without -O.
"""
from pathlib import Path
import argparse, hashlib, json, sys, tempfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
import support

def tup(t):return tuple(map(tup,t)) if isinstance(t,list) else t
INC=('leaf','inc',1)
def normal(t):
    if t=='node60':return INC,INC
    if t=='node61':return (INC,INC),(INC,INC)
    return tuple(map(normal,t)) if c.isnode(t) else t

def word(t):return word(t[0])+word(t[1]) if c.isnode(t) else [t]
def sha(data):return hashlib.sha256(data).hexdigest()
def dump(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')

def main(output,full=True):
    assert __debug__ and not sys.flags.optimize
    nodes0={k:tup(v) for k,v in json.loads((ROOT/'inputs/primary.nodes.json').read_text()).items()}
    assert nodes0['node163']==('node6','node55')
    nodes=dict(nodes0);nodes['node163']=('node6','node54')
    raw0=support.read_table(ROOT/'inputs/primary.raw.native.tm')
    raw0[164,1]=(1,True,114)
    c.machine=lambda:(raw0,[]);c.raw_nodes=lambda:nodes
    c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
    grammar=normal(c.read_grammar(ROOT/'grammar.json'))
    oldgrammar=normal(c.read_grammar(ROOT/'inputs/primary.grammar.json'))
    oldword,newword=word(oldgrammar),word(grammar)
    assert len(oldword)==len(newword)==190
    assert [(i,a,b)for i,(a,b)in enumerate(zip(oldword,newword))if a!=b]==[
        (1,'node55','node70'),(103,'node55','node58'),(105,INC,'node55'),
        (106,INC,'node65'),(107,'node70',INC),(108,'node58',INC),(109,'node65','node70')]
    sites,ins,contracts=c.source(grammar)
    # Same new macro word in the accepted primary association: every resolved
    # successor must agree, not merely the linear primitive operation list.
    stream=iter(newword)
    def replace(t):return tuple(map(replace,t)) if c.isnode(t) else next(stream)
    reference=replace(oldgrammar);assert next(stream,None)is None
    rs,ri,rc=c.source(reference)
    assert ins==ri
    assert [(op,a)for p,op,a in sites]==[(op,a)for p,op,a in rs]
    # Independently check the no-push source splice against its parent graph.
    c.raw_nodes=lambda:nodes0
    oldsites,oldins,_=c.source(grammar)
    c.raw_nodes=lambda:nodes
    assert len(oldins)==3673 and len(ins)==3654
    lo,hi=3634,3653
    def move(t):
        if t<lo:return t
        if t==lo:return lo
        assert t>=hi,('edge enters erased push interior',t)
        return t-(hi-lo)
    def port(row):
        n={'inc':2,'dec':2,'jump':1,'halt':1}[row[0]]
        return row[:n]+tuple(move(x)for x in row[n:])
    for i,row in enumerate(oldins):
        if lo<=i<hi:continue
        assert port(row)==ins[move(i)]
    raw,_,shape=c.build(grammar)
    assert len(raw)==402 and len(shape)==67
    folds=json.loads((ROOT/'folds.json').read_text());assert len(folds)==7
    rows,aliases=support.apply_folds(raw,folds)
    local=support.check_local_folds(raw,rows,aliases,folds)
    assert len(local['cases'])==28
    dense,labels=support.dense_table(rows,194)
    for q in c.BOXSTATES:
        for bit in (0,1):assert rows[q,bit]==raw0[q,bit]
    assert support.table_text(dense)==(ROOT/'machine.tm').read_text()
    assert support.table_text(rows)==(ROOT/'machine.native.tm').read_text()
    assert labels==json.loads((ROOT/'labels.json').read_text())
    assert json.loads(json.dumps(ins))==json.loads((ROOT/'instructions.json').read_text())
    assert [[''.join(map(str,p)),op,a]for p,op,a in sites]==json.loads((ROOT/'sites.json').read_text())
    startup=support.startup(rows,sites[25][0]);assert startup['steps']==58154
    runtime=c.validate(rows,contracts) if full else None
    if full:assert runtime==dict(ok=True,contracts=4755,max_steps=470,total_steps=1477258)
    receipt=dict(family='PA194G',working_states=194,transition_rows=388,
       source_sites=3654,source_outcomes=4755,fixed_controls=134,AX_readers=67,
       simultaneous_folds=7,local_cases=28,source_reassociation_graph_equal=True,
       no_push_deletion=[lo,hi],no_exterior_edge_into_erased_interior=True,
       physical_box_rows_unchanged=True,source_macro_word_changes=[1,103,105,106,107,108,109],
       runtime=runtime,startup=startup,
       dense_sha256=sha(support.table_text(dense).encode()),kernel_checked=False)
    assert receipt['dense_sha256']=='28bd991a84200351f36c98afac369ab5a555eb8793821ad35555f0aa4a0fdeeb'
    output.mkdir(parents=True,exist_ok=True)
    dump(output/'construction.json',receipt);dump(output/'local_folds.json',local)
    print(json.dumps(receipt,indent=2))
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--quick',action='store_true',help='Skip the full construction symbolic pass.')
    args=ap.parse_args()
    main(args.output or Path(tempfile.mkdtemp(prefix='pa194g-check-')),not args.quick)
