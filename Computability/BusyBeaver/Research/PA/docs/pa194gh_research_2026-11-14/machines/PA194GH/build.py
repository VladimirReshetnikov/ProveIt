#!/usr/bin/env python3
"""PA194GH: explicit-operand generalization, no-push MP, cached-head Shift.
Constructs a new combined controller; retains incomplete iPRA calibration status.
"""
from pathlib import Path
import sys,json,hashlib
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'construction'))
import compiler as c
import support as s

def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x

def main():
    out=HERE
    rawg=s.read_table(HERE/'inputs/G.raw.native.tm')
    fixedg={key:val for key,val in rawg.items()if key[0]<1300}
    changes={(38,0):(0,True,11),(38,1):(1,True,122),
             (214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)}
    raw=dict(rawg);raw.update(changes)
    edits=[[q,b,list(fixedg[q,b]),list(val)]for(q,b),val in sorted(changes.items())]
    nodesg={k:tup(v)for k,v in json.loads((HERE/'inputs/G.nodes.json').read_text()).items()}
    assert nodesg['node170']==('node36','node169')
    nodesh=dict(nodesg);nodesh['node170']=(('node36',('node167','node145')),'node57')
    c.machine=lambda:(raw,[]);c.raw_nodes=lambda:nodesh
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    grammar=c.read_grammar(HERE/'grammar.json')
    rebuilt,idx,shape=c.build(grammar)
    assert rebuilt==raw
    folds=json.loads((HERE/'folds.json').read_text())
    child,aliases=s.apply_folds(raw,folds)
    cases=s.check_local_folds(raw,child,aliases,folds)
    sites,ins,cs=c.source(grammar)
    print('source',len(sites),len(cs),flush=True)
    runtime=c.validate(child,cs);print(runtime,flush=True);assert runtime['ok']
    blank=s.startup(child,sites[25][0]);print('startup',blank['steps'],flush=True)
    dense,labels=s.dense_table(child,194)
    for name,rows in [('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]:
        assert (out/name).read_text()==s.table_text(rows), name
    receipt=dict(name='PA194GH',working_states=194,transitions=388,start=0,halt=194,raw_fixed_states=134,raw_reader_states=len(shape),folds=len(folds),fixed_edits_from_G=edits,source_sites=len(sites),source_outcomes=len(cs),runtime=runtime,startup=blank,dense_sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),kernel_checked=False,ipra_calibration_complete=False)
    for name,x in [('receipt.json',receipt),('labels.json',labels),('nodes.json',nodesh),('grammar.json',json.loads((HERE/'grammar.json').read_text())),('folds.json',folds),('fold_cases.json',cases),('sites.json',[[''.join(map(str,p)),op,arg]for p,op,arg in sites]),('instructions.json',ins)]:
        if name=='receipt.json':
            (out/name).write_text(json.dumps(x,indent=2)+'\n')
        else:
            assert json.loads((out/name).read_text())==json.loads(json.dumps(x)), name
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
