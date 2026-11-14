#!/usr/bin/env python3
"""Reconstruct PA194AX11QH5 from frozen QH5 inputs; Python standard library only."""
import argparse, hashlib, json, sys
from pathlib import Path
import compiler as c
import support as s

HERE=Path(__file__).resolve().parent
BASE=HERE/'inputs/qh5'
def tup(x): return tuple(map(tup,x)) if isinstance(x,list) else x
def dump(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
def replace_exit(t):
    if t==c.BREAK:return 'node49'
    return tuple(map(replace_exit,t)) if c.isnode(t) else t
def word(t):return word(t[0])+word(t[1]) if c.isnode(t) else [t]
def grammar_json(t):
    rules={};names={}
    def visit(t):
        if not c.isnode(t):return t
        if t in names:return names[t]
        name='g'+str(len(names));names[t]=name;rules[name]=list(map(visit,t));return name
    return {'root':visit(t),'rules':rules}

def setup():
    raw=s.read_table(BASE/'machine/raw.native.tm')
    ns={k:tup(v)for k,v in json.loads((BASE/'machine/nodes.json').read_text()).items()}
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99
    c.MACROS.pop(((inc,inc),(inc,inc)),None)
    c.machine=lambda:(raw,[]);c.raw_nodes=lambda:ns
    oldg=c.read_grammar(BASE/'construction/inputs/q.grammar.json')
    return raw,ns,oldg

def build(out,full=True,grammar=None):
    assert __debug__ and not sys.flags.optimize
    raw0,ns,oldg=setup()
    g=c.read_grammar(grammar) if grammar else replace_exit(oldg)
    assert word(oldg).count(c.BREAK)==1
    if not grammar:assert word(g)==word(oldg)[:-1]+['node49']
    oldsites,oldins,_=c.source(oldg)
    raw,index,shape=c.build(g)
    folds=json.loads((BASE/'machine/folds.json').read_text())
    rows,aliases=s.apply_folds(raw,folds)
    local=s.check_local_folds(raw,rows,aliases,folds)
    sites,ins,contracts=c.source(g)
    print('raw',len(raw)//2,'readers',len(shape),'folds',len(folds),'working',len(rows)//2,'sites',len(sites),flush=True)
    out.mkdir(parents=True,exist_ok=True)
    for name,data in [('grammar.json',grammar_json(g)),('nodes.json',ns),('folds.json',folds),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('local_folds.json',local)]:dump(out/name,data)
    for name,tab in [('raw.native.tm',raw),('machine.native.tm',rows)]: (out/name).write_text(s.table_text(tab))
    runtime=c.validate(rows,contracts) if full else None
    if full:assert runtime['ok'],runtime
    startup=s.startup(rows,sites[25][0])
    n=len(rows)//2;dense,labels=s.dense_table(rows,n)
    (out/'machine.tm').write_text(s.table_text(dense));dump(out/'labels.json',labels)
    receipt=dict(family='PA194AX11QH5',working_states=n,rows=len(rows),fixed_controls=len(raw)//2-len(shape),AX_readers=len(shape),folds=len(folds),local_cases=len(local['cases']),source_sites=len(sites),source_outcomes=len(contracts),coefficient=5,runtime=runtime,startup=startup,dense_sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),native_sha256=hashlib.sha256(s.table_text(rows).encode()).hexdigest(),kernel_checked=False)
    dump(out/'receipt.json',receipt);print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=HERE.parent/'machine');p.add_argument('--quick',action='store_true');p.add_argument('--grammar',type=Path);a=p.parse_args();build(a.output,not a.quick,a.grammar)
