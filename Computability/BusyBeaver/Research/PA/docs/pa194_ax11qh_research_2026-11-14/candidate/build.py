#!/usr/bin/env python3
"""Rebuild PA194AX11QH and its finite/symbolic certificates (Python standard library).
No iPRA consistency equivalence is asserted by this executable checker.
"""
from pathlib import Path
import argparse, hashlib, json, sys, tempfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor'))
import compiler as c
import support as s
DENSE_SHA='19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50'
NATIVE_SHA='424bd5175bbca161e76af485f1eda03f2f169d90afe80563035b60289361bf07'
H_EDITS={(38,0):(0,True,11),(38,1):(1,True,122),(164,1):(1,True,114),
         (214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)}
def tup(x):return tuple(map(tup,x)) if isinstance(x,list)else x
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def replace_exit(t):
    return 'node49' if t==c.BREAK else tuple(map(replace_exit,t))if c.isnode(t)else t

def grammar_json(t):
    rules={};names={}
    def node(t):
        if not c.isnode(t):return t
        if t in names:return names[t]
        name='g'+str(len(names));names[t]=name
        rules[name]=list(map(node,t));return name
    root=node(t);return {'root':root,'rules':rules}

def build(out,full=True):
    assert __debug__ and not sys.flags.optimize,'Assertions must be enabled.'
    inp=ROOT/'inputs'
    for name,expected in json.loads((ROOT/'INPUT_HASHES.json').read_text()).items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==expected,name
    nodes={k:tup(v)for k,v in json.loads((inp/'primary.nodes.json').read_text()).items()}
    raw0=s.read_table(inp/'primary.raw.native.tm')
    c.machine=lambda:(raw0,[]);c.raw_nodes=lambda:nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    gram=replace_exit(c.read_grammar(inp/'q.grammar.json'))
    raw0.update(H_EDITS)
    assert nodes['node163']==('node6','node55')
    assert nodes['node170']==('node36','node169')
    nodes['node163']=('node6','node54')
    nodes['node170']=(('node36',('node167','node145')),'node57')
    raw,index,shape=c.build(gram)
    folds=json.loads((inp/'q.folds.json').read_text())
    rows,aliases=s.apply_folds(raw,folds)
    assert (len(raw),len(shape),len(folds),len(rows))==(402,67,7,388)
    local=s.check_local_folds(raw,rows,aliases,folds)
    assert len(local['cases'])==28
    assert all(rows[q,b]==raw0[q,b]for q in c.BOXSTATES for b in(0,1))
    sites,instructions,contracts=c.source(gram)
    assert len(sites)==3671 and len(contracts)==4778
    runtime=c.validate(rows,contracts)if full else None
    if full:assert runtime=={'ok':True,'contracts':4778,'max_steps':497,'total_steps':1547747}
    startup=s.startup(rows,sites[25][0]);assert startup['steps']==57922
    dense,labels=s.dense_table(rows,194)
    native_text=s.table_text(rows);dense_text=s.table_text(dense)
    assert hashlib.sha256(dense_text.encode()).hexdigest()==DENSE_SHA
    assert hashlib.sha256(native_text.encode()).hexdigest()==NATIVE_SHA
    out.mkdir(parents=True,exist_ok=True)
    for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
        (out/name).write_text(s.table_text(table))
    for name,data in [('labels.json',labels),('nodes.json',nodes),('grammar.json',grammar_json(gram)),
                      ('grammar.tree.json',gram),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),
                      ('instructions.json',instructions),('folds.json',folds),('local_fold_cases.json',local)]:dump(out/name,data)
    receipt={'family':'PA194AX11QH','working_states':194,'rows':388,'fixed':134,'readers':67,'folds':7,
             'source_sites':3671,'source_contracts':4778,'runtime':runtime,'startup':startup,
             'dense_sha256':DENSE_SHA,'native_sha256':NATIVE_SHA,'ipra_equivalence_proven':False,
             'scope':'Concrete construction; simultaneous fold cases; source outcome contracts; complete blank startup. Consistency calibration remains a separate obligation.'}
    dump(out/'receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True);return receipt
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path)
    p.add_argument('--quick',action='store_true',help='Skip construction symbolic source replay only.')
    a=p.parse_args();build(a.output or Path(tempfile.mkdtemp(prefix='pa194ax11qh-')),not a.quick)
