#!/usr/bin/env python3
"""Rebuild AX11GH and AX11GHS from pinned GH/GHS sources.

The recurring AX return is replaced by Push, falling through into full MP.
All input mathematical and checker code is attributed in licenses/.
"""
from pathlib import Path
import sys,json,hashlib,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'construction'))
import compiler as c
import support as s

def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x

def replace_break(t):
    if t==c.BREAK:return 'node49'
    return tuple(map(replace_break,t)) if c.isnode(t) else t

def build(family,full=False):
    parent={'PA194AX11GH':'PA194GH','PA194AX11GHS':'PA194GHS'}[family]
    inp=HERE/'inputs'/parent;out=HERE/'machines'/family
    raw0=s.read_table(inp/'raw.native.tm')
    nodes={k:tup(v)for k,v in json.loads((inp/'nodes.json').read_text()).items()}
    c.machine=lambda:(raw0,[]);c.raw_nodes=lambda:nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    old=c.read_grammar(inp/'grammar.json')
    grammar=replace_break(old)
    raw,index,shape=c.build(grammar)
    folds=json.loads((inp/'folds.json').read_text())
    child,aliases=s.apply_folds(raw,folds)
    cases=s.check_local_folds(raw,child,aliases,folds)
    sites,ins,contracts=c.source(grammar)
    print(family,'source',len(sites),len(contracts),flush=True)
    runtime=c.validate(child,contracts) if full else None
    if full:assert runtime['ok']
    blank=s.startup(child,sites[25][0])
    dense,labels=s.dense_table(child,194)
    changed=[[q,b,list(v),list(raw[q,b])]for(q,b),v in sorted(raw0.items())if(q,b)in raw and raw[q,b]!=v]
    out.mkdir(parents=True,exist_ok=True)
    for name,rows in [('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]:
        (out/name).write_text(s.table_text(rows))
    receipt={'family':family,'parent':parent,'status':'PASS','working_states':194,'transition_rows':388,
        'fixed_controls':sum(q<1300 for q,b in raw)//2,'raw_AX_readers':len(shape),'folds':len(folds),
        'raw_changes_from_parent':changed,'source_sites':len(sites),'source_outcomes':len(contracts),
        'local_fold_cases':len(cases['cases']),'full_construction_replay':full,'runtime':runtime,'startup':blank,
        'dense_sha256':hashlib.sha256(s.table_text(dense).encode()).hexdigest(),'kernel_checked':False}
    vals=[('receipt.json',receipt),('nodes.json',nodes),('grammar.tree.json',grammar),('folds.json',folds),
      ('fold_cases.json',cases),('labels.json',labels),('sites.json',[[''.join(map(str,p)),op,arg]for p,op,arg in sites]),('instructions.json',ins)]
    for name,obj in vals:(out/name).write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full',action='store_true')
    ap.add_argument('--family',choices=['PA194AX11GH','PA194AX11GHS'])
    args=ap.parse_args()
    for name in ([args.family] if args.family else ['PA194AX11GH','PA194AX11GHS']):build(name,args.full)
