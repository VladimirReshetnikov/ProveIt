#!/usr/bin/env python3
"""Reconstruct PA194AX11Q6, using the attributed PA194 physical proof engines.

The two source changes combine AX11 fallthrough with QN6 arithmetic/emission.
This is a new verified composition, not a new kernel-checked endpoint.
"""
from pathlib import Path
import sys, json, hashlib, argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c, baseline_tools as b, source_audit as audit
c.ROOT=HERE/'inputs'
BASE_NODES=c.raw_nodes
BASE=b.read_table(HERE/'inputs/unfolded201.native.tm')
INC=('leaf','inc',1)
c.MACROS[(INC,INC)]=99
c.MACROS[((INC,INC),(INC,INC))]=190

def nodes(k):
    ns=BASE_NODES()
    assert ns['node163']==('node6','node55')
    ns['node163']=('node6','node54')
    if k==6:
        triple=(INC,'node60');ns['node61']=(triple,triple)
    else: assert k==4
    return ns

def replace_exit(t):
    if t==c.BREAK:return 'node49'
    return tuple(map(replace_exit,t)) if c.isnode(t) else t

def flattened(t):
    return flattened(t[0])+flattened(t[1]) if c.isnode(t) else [t]

def grammar_json(t):
    names={};rules={}
    def rec(u):
        if not c.isnode(u):return u
        if u not in names:
            name='g'+str(len(names));names[u]=name
            rules[name]=list(map(rec,u))
        return names[u]
    root=rec(t)
    return dict(root=root,rules=rules)

def build(out,full=True):
    assert __debug__ and not sys.flags.optimize
    for path,digest in json.loads((HERE/'PROVENANCE.json').read_text())['input_files'].items():
        assert hashlib.sha256((HERE/path).read_bytes()).hexdigest()==digest,path
    rawbase=dict(BASE);rawbase[164,1]=(1,True,114)
    c.machine=lambda:(rawbase,[])
    original_grammar=c.read_grammar(HERE/'inputs/grammar.json')
    grammar=replace_exit(original_grammar)
    assert flattened(grammar)==flattened(original_grammar)[:-1]+['node49']
    assert flattened(original_grammar).count(c.BREAK)==1
    c.raw_nodes=lambda:nodes(4)
    oldsites,oldins,_=c.source(grammar)
    audit.BASE_NODES=c.raw_nodes
    raw,index,shape=c.build(grammar)
    assert len(raw)==402 and len(shape)==67
    raw.update({(190,0):(0,True,330),(190,1):(1,True,330),
      (330,0):(0,True,61),(330,1):(1,True,99)})
    folds=json.loads((HERE/'inputs/folds.json').read_text())+[[41,99,[[0,False,30],[1,False,2040]]]]
    child,aliases=b.apply_folds(raw,folds)
    local=b.check_local_folds(raw,child,aliases,folds)
    assert len(raw)==404 and len(child)==388 and len(local['cases'])==32
    assert all(child[q,bit]==BASE[q,bit] for q in c.BOXSTATES for bit in (0,1))
    c.raw_nodes=lambda:nodes(6)
    sites,ins,contracts=c.source(grammar)
    binding=audit.source_binding(grammar,oldsites,oldins,nodes(6),sites,ins,6)
    # The original Q emitter's free-algebra audit covers everything preceding
    # the final guard and exit. This replacement only appends one Push.
    free=audit.emitter_audit(original_grammar,6)
    valid=c.validate(child,contracts) if full else None
    if full: assert valid['ok'], valid
    seed=b.startup(child,sites[25][0])
    dense,labels=b.dense_table(child,194)
    out.mkdir(parents=True,exist_ok=True)
    for fn,table in [('machine.native.tm',child),('machine.tm',dense),('raw.native.tm',raw)]:
        (out/fn).write_text(b.table_text(table))
    for fn,obj in [('labels.json',labels),('nodes.json',nodes(6)),('folds.json',folds),
      ('local_cases.json',local),('sites.json',[[list(p),op,arg]for p,op,arg in sites]),
      ('instructions.json',ins),('source_binding.json',binding),('emitter_audit.json',free),
      ('grammar.json',grammar_json(grammar)),('grammar.tree.json',grammar)]:
        (out/fn).write_text(json.dumps(obj,indent=2)+'\n')
    receipt=dict(name='PA194AX11Q6',states=194,raw_states=202,reader_states=67,folds=8,
      source_sites=len(sites),source_outcomes=len(contracts),local_fold_cases=32,
      runtime=valid,startup=seed,dense_sha256=hashlib.sha256(b.table_text(dense).encode()).hexdigest(),
      native_sha256=hashlib.sha256(b.table_text(child).encode()).hexdigest(),
      contribution='AX11 fallthrough composed with Q6 emitter and no-push MP',
      kernel_checked=False)
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    return raw,child,shape

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick',action='store_true')
    parser.add_argument('--output',type=Path,default=HERE/'machine')
    args=parser.parse_args();build(args.output,not args.quick)
