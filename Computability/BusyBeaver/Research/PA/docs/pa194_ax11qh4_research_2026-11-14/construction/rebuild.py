#!/usr/bin/env python3
"""Rebuild the two AX11QH four-increment reassociations.

This deterministic checker uses Python's standard library. It proves finite
table identities, replays symbolic source contracts using the unchanged
register-box interface, and checks the exact blank startup. The separate
literal-tape audit discharges that interface. No PA calibration is asserted.
"""
from pathlib import Path
import argparse, hashlib, json, sys

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor'))
import compiler as c
import support as s
INC=('leaf','inc',1)
EXPECTED={'4L':'c825ec97fdaa36868d1830b601863d255853ebe061af8b22f432d55233763659',
          '4R':'9ea0169880ecaea748d11217c829420aa8694948d2578b8fc28adcc3bcf76815'}
PARENT_SHA='19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50'

def tup(x):
    return tuple(map(tup,x))if isinstance(x,list)else x

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def occurrences(grammar,nodes,target):
    found=[]
    def walk(t,p):
        if isinstance(t,str):
            if t==target:found.append(p)
            walk(grammar if t=='x67'else nodes[t],p)
        elif c.isnode(t):
            walk(t[0],p+(0,));walk(t[1],p+(1,))
    walk('node172',())
    return found

def check(variant):
    folder=ROOT/('AX11QH'+variant)
    assert sha(ROOT/'inputs/machine.tm')==PARENT_SHA
    assert sha(folder/'machine.tm')==EXPECTED[variant]
    raw0=s.read_table(ROOT/'inputs/raw.native.tm')
    nodes0={k:tup(v)for k,v in json.loads((ROOT/'inputs/nodes.json').read_text()).items()}
    grammar=c.read_grammar(ROOT/'inputs/grammar.json')
    c.MACROS[(INC,INC)]=99
    c.MACROS[((INC,INC),(INC,INC))]=190
    c.raw_nodes=lambda:nodes0
    c.machine=lambda:(raw0,[])
    old_sites,old_ins,_=c.source(grammar)
    assert json.loads(json.dumps(old_ins))==json.loads((ROOT/'inputs/instructions.json').read_text())
    assert [[''.join(map(str,p)),op,a]for p,op,a in old_sites]==json.loads((ROOT/'inputs/sites.json').read_text())
    rebuilt,_,shape=c.build(grammar)
    assert rebuilt==raw0 and len(shape)==67 and len(raw0)==402
    parent_folds=json.loads((ROOT/'inputs/folds.json').read_text())
    parent,parent_aliases=s.apply_folds(raw0,parent_folds)
    assert parent==s.read_table(ROOT/'inputs/machine.native.tm')
    parent_dense,parent_labels=s.dense_table(parent,194)
    assert s.table_text(parent_dense)==(ROOT/'inputs/machine.tm').read_text()
    assert parent_labels==json.loads((ROOT/'inputs/labels.json').read_text())
    parent_local=s.check_local_folds(raw0,parent,parent_aliases,parent_folds)
    assert len(parent_local['cases'])==28
    ns=dict(nodes0)
    assert ns['node61']==('node60','node60')
    ns['node61']=((INC,'node60'),INC)if variant=='4L'else(INC,(INC,'node60'))
    raw=dict(raw0)
    raw[330,0]=(0,True,61);raw[330,1]=(1,True,99)
    raw[190,0]=(0,True,330 if variant=='4L'else 61)
    raw[190,1]=(1,True,61 if variant=='4L'else 330)
    assert raw==s.read_table(folder/'raw.native.tm')
    folds=json.loads((folder/'folds.json').read_text())
    assert len(folds)==8
    child,aliases=s.apply_folds(raw,folds)
    assert child==s.read_table(folder/'machine.native.tm')
    assert all(child[q,b]==parent[q,b]for q in c.BOXSTATES for b in(0,1))
    local=s.check_local_folds(raw,child,aliases,folds)
    assert len(local['cases'])==32
    c.raw_nodes=lambda:ns
    sites,ins,contracts=c.source(grammar)
    assert ins==old_ins and len(ins)==3671 and len(contracts)==4778
    assert json.loads(json.dumps(ins))==json.loads((folder/'instructions.json').read_text())
    assert [[''.join(map(str,p)),op,a]for p,op,a in sites]==json.loads((folder/'sites.json').read_text())
    old_paths=occurrences(grammar,nodes0,'node61')
    new_paths=occurrences(grammar,ns,'node61')
    assert old_paths==new_paths and len(old_paths)==61
    body_checks=[]
    for p in old_paths:
        oi=[i for i,(q,op,a)in enumerate(old_sites)if q[:len(p)]==p]
        ni=[i for i,(q,op,a)in enumerate(sites)if q[:len(p)]==p]
        assert oi==ni and len(oi)==4
        assert all(ins[i]==('inc',1,i+1)for i in oi)
        body_checks.append({'prefix':''.join(map(str,p)),'first_site':oi[0],'sites':oi})
    runtime=c.validate(child,contracts)
    assert runtime['ok']
    startup=s.startup(child,sites[25][0])
    assert startup['steps']==58088
    dense,labels=s.dense_table(child,194)
    assert s.table_text(dense)==(folder/'machine.tm').read_text()
    assert labels==json.loads((folder/'labels.json').read_text())
    return {'status':'PASS','name':'PA194AX11QH'+variant,
            'raw_states':202,'fixed_controls':135,'AX_readers':67,
            'contextual_folds':8,'working_states':194,'transition_rows':388,
            'source_sites':3671,'source_outcomes':4778,
            'all_resolved_source_instructions_identical_to_AX11QH':True,
            'four_increment_occurrences':body_checks,
            'arithmetic_box_rows_unchanged':True,
            'local_fold_certificate':local,'symbolic':runtime,'startup':startup,
            'native_sha256':sha(folder/'machine.native.tm'),
            'dense_sha256':sha(folder/'machine.tm'),
            'parent_dense_sha256':sha(ROOT/'inputs/machine.tm'),
            'iPRA_consistency_calibration_established':False,
            'scope':'Relative source-preserving physical transformation; the written proof and separate literal-tape audit justify the unbounded transfer.'}

def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run with Python assertions enabled.')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--variant',choices=['4L','4R'],action='append')
    p.add_argument('--receipt',type=Path)
    a=p.parse_args()
    result={v:check(v)for v in a.variant or['4L','4R']}
    if a.receipt:
        a.receipt.parent.mkdir(parents=True,exist_ok=True)
        a.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({v:{k:r[k]for k in('status','name','working_states','source_outcomes','dense_sha256')}for v,r in result.items()},indent=2))
if __name__=='__main__':main()
