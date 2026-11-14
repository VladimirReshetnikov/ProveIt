#!/usr/bin/env python3
"""Build PA194AX11H from the pinned PA194 grammar and two exact source edits.

Python3 standard library, with assertions enabled. Default output is a fresh
scratch directory; repository and frozen artifacts are never overwritten.
"""
from pathlib import Path
import sys,argparse,tempfile,json,hashlib
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
import support

def tup(x):return tuple(map(tup,x)) if isinstance(x,list)else x

def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')

def replace_exit(t):
    if t==c.BREAK:return 'node49'
    return tuple(map(replace_exit,t)) if c.isnode(t)else t

def flatten(t):return flatten(t[0])+flatten(t[1]) if c.isnode(t)else[t]

def grammar_json(t):
    rules={};names={}
    def node(t):
        if not c.isnode(t):return t
        if t in names:return names[t]
        name='g'+str(len(names));names[t]=name
        rules[name]=list(map(node,t));return name
    root=node(t)
    return {'root':root,'rules':rules}

def build(out,full=True):
    assert __debug__ and not sys.flags.optimize
    inp=ROOT/'inputs'
    raw0=support.read_table(inp/'primary.raw.native.tm')
    nodes={k:tup(v)for k,v in json.loads((inp/'primary.nodes.json').read_text()).items()}
    assert nodes['node163']==('node6','node55')
    c.machine=lambda:(raw0,[]);c.raw_nodes=lambda:nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    oldg=c.read_grammar(inp/'primary.grammar.json')
    oldsites,oldins,_=c.source(oldg)
    assert json.loads(json.dumps(oldins))==json.loads((inp/'primary.instructions.json').read_text())
    assert [[''.join(map(str,p)),op,a]for p,op,a in oldsites]==json.loads((inp/'primary.sites.json').read_text())
    word=flatten(oldg)
    assert word[-1]==c.BREAK and word.count(c.BREAK)==1
    grammar=replace_exit(oldg)
    assert flatten(grammar)==word[:-1]+['node49']
    nodes['node163']=('node6','node54')
    raw0=dict(raw0);raw0[164,1]=(1,True,114)
    raw0.update({(38,0):(0,True,11),(38,1):(1,True,122), (214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)})
    nodes['node170']=(('node36',('node167','node145')),'node57')
    raw,index,shape=c.build(grammar)
    folds=json.loads((inp/'primary.folds.json').read_text())
    assert len(raw)==402 and len(shape)==67 and len(folds)==7
    rows,aliases=support.apply_folds(raw,folds)
    local=support.check_local_folds(raw,rows,aliases,folds)
    assert len(local['cases'])==28
    sites,instructions,contracts=c.source(grammar)
    assert len(sites)==3671 and len(contracts)==4778
    runtime=c.validate(rows,contracts)if full else None
    if full:assert runtime['ok']
    startup=support.startup(rows,sites[25][0])
    dense,labels=support.dense_table(rows,194)
    text=support.table_text(dense)
    for q in c.BOXSTATES:
        for bit in(0,1):assert rows[q,bit]==raw0[q,bit]
    out.mkdir(parents=True,exist_ok=True)
    for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
        (out/name).write_text(support.table_text(table))
    for name,data in [('labels.json',labels),('grammar.tree.json',grammar),('nodes.json',nodes),('grammar.json',grammar_json(grammar)),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',instructions),('folds.json',folds),('local_folds.json',local)]:dump(out/name,data)
    receipt=dict(family='PA194AX11H',working_states=194,transition_rows=388,fixed_controls=134,AX_readers=67,folds=7,local_fold_cases=28,source_sites=len(sites),source_contracts=len(contracts),source_edits=['terminal AX breakTo1 -> push node49','successful MP node55 -> node54','Shift tests only cached head'],runtime=runtime,startup=startup,arithmetic_box_rows_unchanged=True,dense_sha256=hashlib.sha256(text.encode()).hexdigest(),native_sha256=hashlib.sha256(support.table_text(rows).encode()).hexdigest(),kernel_checked=False)
    dump(out/'receipt.json',receipt)
    print(json.dumps(receipt,indent=2));return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--quick',action='store_true',help='Skip construction symbolic replay; not full verification.')
    args=ap.parse_args();build(args.output or Path(tempfile.mkdtemp(prefix='pa194ax11-')),not args.quick)
