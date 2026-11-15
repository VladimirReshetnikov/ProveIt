#!/usr/bin/env python3
"""Reconstruct PA194LC_AX11H and prove exact resolved-source preservation.

The loop continuation transformation changes three transition rows and the
binary parse tree of the four-increment loop tail. All 3671 source opcodes,
register operands, and resolved successor ordinals remain identical.
Standard-library Python, assertions required; no proof-assistant claim.
"""
from pathlib import Path
import argparse,hashlib,json,sys
import compiler as c
import support
ROOT=Path(__file__).resolve().parent
FAMILY='PA194LC_AX11H'
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main(full=True):
    assert __debug__ and not sys.flags.optimize
    for name,digest in json.loads((ROOT/'parent_integrity.json').read_text()).items():
        assert sha(ROOT/name)==digest,name
    src=ROOT/'parent'
    original=support.read_table(src/'raw.native.tm')
    nodes={k:tup(v)for k,v in json.loads((src/'nodes.json').read_text()).items()}
    grammar=c.read_grammar(src/'grammar.json')
    c.machine=lambda:(original,[]);c.raw_nodes=lambda:nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99
    c.MACROS[((inc,inc),(inc,inc))]=190
    oldsites,oldins,_=c.source(grammar)
    assert json.loads(json.dumps(oldins))==json.loads((src/'instructions.json').read_text())
    assert [[''.join(map(str,p)),op,a]for p,op,a in oldsites]==json.loads((src/'sites.json').read_text())
    oldtree=nodes['node62']
    nodes['node62']=((inc,inc),((inc,inc),('leaf','continueTo',3)))
    # State 190 now decodes a continuation edge; it is no longer 4INC.
    c.MACROS.pop(((inc,inc),(inc,inc)))
    c.MACROS.pop('node61',None)
    fixed=dict(original)
    assert fixed[139,0]==(0,True,190)
    assert fixed[139,1]==(0,False,16)
    assert fixed[190,1]==(1,True,99)
    fixed[139,0]=(0,True,99)
    fixed[139,1]=(1,True,190)
    fixed[190,1]=(1,False,73)
    c.machine=lambda:(fixed,[])
    raw,index,shape=c.build(grammar)
    assert len(raw)==402 and len(shape)==67
    edits=[[q,b,list(original[q,b]),list(raw[q,b])]for q,b in sorted(original)if original[q,b]!=raw[q,b]]
    assert [(q,b)for q,b,_,_ in edits]==[(139,0),(139,1),(190,1)],edits
    folds=json.loads((src/'folds.json').read_text())
    rows,aliases=support.apply_folds(raw,folds)
    parent_rows=support.read_table(src/'machine.native.tm')
    folded_edits=[[q,b,list(parent_rows[q,b]),list(rows[q,b])]for q,b in sorted(parent_rows)if parent_rows[q,b]!=rows[q,b]]
    assert folded_edits==edits and set(rows)==set(parent_rows)
    local=support.check_local_folds(raw,rows,aliases,folds)
    assert len(local['cases'])==28
    sites,ins,contracts=c.source(grammar)
    assert oldins==ins and len(ins)==3671 and len(contracts)==4778
    assert all(raw[q,b]==original[q,b]for q in c.BOXSTATES for b in(0,1))
    startup=support.startup(rows,sites[25][0]);assert startup['steps']==57922
    dense,labels=support.dense_table(rows,194)
    runtime=c.validate(rows,contracts)if full else None
    if full:assert runtime['ok']and runtime['contracts']==4778
    for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
        (ROOT/name).write_text(support.table_text(table))
    for name,value in [('nodes.json',nodes),('grammar.tree.json',grammar),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('labels.json',labels),('local.json',local)]:dump(ROOT/name,value)
    receipt=dict(family=FAMILY,working_states=194,transition_rows=388,raw_controls=201,raw_reader_controls=67,folds=7,source_sites=3671,source_contracts=4778,source_graph_equal=True,source_graph_sha256=sha(ROOT/'instructions.json'),source_path_changes=sum(a[0]!=b[0]for a,b in zip(oldsites,sites)),node62_before=oldtree,node62_after=nodes['node62'],raw_transition_edits=edits,folded_transition_edits=folded_edits,arithmetic_box_rows_unchanged=True,runtime=runtime,startup=startup,dense_sha256=sha(ROOT/'machine.tm'),native_sha256=sha(ROOT/'machine.native.tm'),parent_dense_sha256=sha(src/'machine.tm'),full_construction_replay=full,kernel_checked=False,absolute_consistency_calibration_proved_here=False)
    dump(ROOT/'receipt.json',receipt);print(json.dumps(receipt,indent=2),flush=True)
    return receipt
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--quick',action='store_true');args=parser.parse_args();main(not args.quick)
