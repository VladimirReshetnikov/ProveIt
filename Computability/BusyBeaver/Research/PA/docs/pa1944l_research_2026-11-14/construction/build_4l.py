#!/usr/bin/env python3
"""A reassociated four-increment decoder: source-preserving conditional result."""
import json, hashlib
from pathlib import Path
import compiler as c
import support as s
import build as baseline
HERE=Path(__file__).resolve().parent
INC=('leaf','inc',1)
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main(output=None):
    c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
    grammar=c.read_grammar(HERE/'inputs/pa194.grammar.json')
    oldsites,oldins,_=c.source(grammar)
    raw,index,shape=c.build(grammar)
    folds=json.loads((HERE/'inputs/pa194.folds.json').read_text())
    primary,_=s.apply_folds(raw,folds)
    print('raw,parent',len(raw)//2,len(primary)//2,flush=True)
    original_nodes=c.raw_nodes()
    nodes=dict(original_nodes);nodes['node61']=((INC,'node60'),INC)
    raw.update({(190,0):(0,True,330),(190,1):(1,True,61),
                (330,0):(0,True,61),(330,1):(1,True,99)})
    folds += [[41,99,[[0,False,30],[1,False,2035]]]]
    child,aliases=s.apply_folds(raw,folds)
    local=s.check_local_folds(raw,child,aliases,folds)
    c.raw_nodes=lambda:nodes
    sites,ins,contracts=c.source(grammar)
    assert ins==oldins
    binding=baseline.source_binding(grammar,oldsites,oldins,nodes,sites,ins,4)
    print('source equality',len(sites),len(contracts),flush=True)
    valid=c.validate(child,contracts);assert valid['ok'],valid
    print('symbolic',valid,flush=True)
    seed=s.startup(child,sites[25][0]);print('seed',seed['steps'],flush=True)
    dense,labels=s.dense_table(child,len(child)//2)
    text=s.table_text(dense)
    out=Path(output) if output else HERE.parent/'machine';out.mkdir(parents=True,exist_ok=True)
    for name,table in [('machine.tm',dense),('machine.native.tm',child),('unfolded202.native.tm',raw)]:
        (out/name).write_text(s.table_text(table))
    for name,data in [('labels.json',labels),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('folds.json',folds),('local_fold_cases.json',local),('source_binding.json',binding),('nodes.json',nodes)]:save(out/name,data)
    receipt={'name':'PA1944L','states':len(child)//2,'dense_sha256':hashlib.sha256(text.encode()).hexdigest(),'source_instructions_identical':True,'source_sites':len(sites),'source_outcomes':len(contracts),'symbolic':valid,'startup':seed,'kernel_checked':False,'scope':'Exact source-preserving physical compiler transformation. iPRA consistency calibration remains conditional on parent.'}
    save(out/'receipt.json',receipt)
    print(json.dumps({k:v for k,v in receipt.items()if k not in ['startup','symbolic']},indent=2),flush=True)
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path)
    main(p.parse_args().output)
