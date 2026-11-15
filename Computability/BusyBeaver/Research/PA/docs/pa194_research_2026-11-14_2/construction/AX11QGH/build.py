#!/usr/bin/env python3
"""Construct PA194AX11QGH and verify its exact source/tape interfaces.

Derived from the pinned AX11G compiler and the cached-only H Shift.
This executable is a finite/symbolic certificate, not a Lean endpoint.
"""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c
import support as s

def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def expand(t):
    inc=('leaf','inc',1)
    if t=='node60':return (inc,inc)
    if t=='node61':return ((inc,inc),(inc,inc))
    return tuple(map(expand,t)) if c.isnode(t) else t
def flatten(t):return flatten(t[0])+flatten(t[1]) if c.isnode(t) else [t]
def populate(t,w):
    it=iter(w)
    def go(t):return tuple(map(go,t)) if c.isnode(t) else next(it)
    out=go(t);assert next(it,None) is None;return out
def grammar_json(t):
    names,rules={},{}
    def go(t):
        if not c.isnode(t):return t
        if t in names:return names[t]
        name='g'+str(len(names));names[t]=name
        rules[name]=[go(t[0]),go(t[1])];return name
    return dict(root=go(t),rules=rules)

def build(output,full=True):
    assert __debug__ and not sys.flags.optimize
    inp=HERE/'inputs'
    raw0=s.read_table(inp/'parent.raw.native.tm')
    nodes={k:tup(v) for k,v in json.loads((inp/'ax11g.nodes.json').read_text()).items()}
    assert nodes['node163']==('node6','node54')
    assert nodes['node170']==('node36','node169')
    fixed=dict(raw0)
    patches=[]
    for q,b,act in json.loads((inp/'h_shift_edits.json').read_text()):
        patches.append([q,b,fixed[q,b],act]);fixed[q,b]=tuple(act)
    nodes['node170']=(('node36',('node167','node145')),'node57')
    c.machine=lambda:(fixed,[]);c.raw_nodes=lambda:nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    grammar=tup(json.loads((inp/'ax11g.grammar.tree.json').read_text()))
    word=flatten(expand(grammar))
    assert len(word)==190 and word[1]=='node70' and word[-1]=='node49'
    # Check against QAX11H's accepted source association with only the G edit.
    canonical=expand(c.read_grammar(inp/'q.grammar.json'))
    cw=flatten(canonical)
    assert cw[1]=='node55' and cw[-1]==c.BREAK
    cw[1]='node70';cw[-1]='node49'
    assert cw==word
    canonical=populate(canonical,cw)
    sites,instructions,contracts=c.source(grammar)
    cs,ci,cc=c.source(canonical)
    assert instructions==ci
    assert [(op,arg) for p,op,arg in sites]==[(op,arg) for p,op,arg in cs]
    assert len(sites)==3671 and len(contracts)==4778
    raw,index,shape=c.build(grammar)
    folds=json.loads((inp/'ax11g.folds.json').read_text())
    rows,aliases=s.apply_folds(raw,folds)
    local=s.check_local_folds(raw,rows,aliases,folds)
    assert len(raw)==402 and len(shape)==67 and len(folds)==7
    assert len(local['cases'])==28
    for q in c.BOXSTATES:
        for b in (0,1):assert rows[q,b]==raw0[q,b]
    runtime=c.validate(rows,contracts) if full else None
    if full:assert runtime['ok'] and runtime['contracts']==4778
    startup=s.startup(rows,sites[25][0]);assert startup['steps']==57922
    dense,labels=s.dense_table(rows,194)
    assert hashlib.sha256(s.table_text(dense).encode()).hexdigest()==\
        '513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1'
    output.mkdir(parents=True,exist_ok=True)
    for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
        (output/name).write_text(s.table_text(table))
    values={'labels.json':labels,'nodes.json':nodes,'grammar.tree.json':grammar,
        'grammar.json':grammar_json(grammar),'sites.json':[[''.join(map(str,p)),op,a] for p,op,a in sites],
        'instructions.json':instructions,'folds.json':folds,'local_folds.json':local,
        'fixed_patch.json':patches}
    for name,value in values.items():dump(output/name,value)
    receipt=dict(family='PA194AX11QGH',status='PASS',working_states=194,transition_rows=388,
        fixed_controls=134,raw_AX_readers=67,simultaneous_folds=7,local_fold_cases=28,
        source_sites=len(sites),source_outcomes=len(contracts),arithmetic_box_rows_unchanged=True,
        canonical_QAX11H_source_with_one_G_edit=True,universal_construction_replay_performed=full,
        runtime=runtime,startup=startup,dense_sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),
        native_sha256=hashlib.sha256(s.table_text(rows).encode()).hexdigest(),
        kernel_checked=False)
    dump(output/'receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=HERE/'machine')
    p.add_argument('--quick',action='store_true')
    a=p.parse_args();build(a.output,not a.quick)
