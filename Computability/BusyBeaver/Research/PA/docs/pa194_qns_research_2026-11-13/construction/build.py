#!/usr/bin/env python3
"""Build PA194QNS from the pinned QN parent and the supplied SUMS transformation.

All inputs are local. The source compiler and first symbolic checker are inherited
unchanged; the new composition and exact source/table bindings are checked here.
"""
from pathlib import Path
import argparse, hashlib, json, sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c
import baseline_tools as b

INPUT=HERE/'inputs'
BASE_NODES=c.raw_nodes

def sha(data):return hashlib.sha256(data).hexdigest()
def emit(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def jtuple(obj):return json.loads(json.dumps(obj))

def check_inputs():
    manifest=json.loads((HERE/'PROVENANCE.json').read_text())
    for item in manifest['inputs']:
        assert sha((HERE/item['path']).read_bytes())==item['sha256'],item['path']

def nodes(symmetric=False):
    out=BASE_NODES()
    assert out['node163']==('node6','node55')
    out['node163']=('node6','node54')
    if symmetric:
        assert out['node168']==('node37','node57')
        out['node168']=('node37','node56')
        out['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
    return out

def source(grammar,symmetric=False):
    c.raw_nodes=lambda:nodes(symmetric)
    return c.source(grammar)

def build(output,full=True):
    assert __debug__ and not sys.flags.optimize,'Assertions must remain enabled.'
    check_inputs()
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    baseline=b.read_table(INPUT/'pa194.native.tm')
    def parent_machine():
        rows=dict(baseline)
        assert rows[164,1]==(1,True,98)
        rows[164,1]=(1,True,114)
        return rows,[]
    c.machine=parent_machine
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99
    c.MACROS[((inc,inc),(inc,inc))]=190
    grammar=c.read_grammar(INPUT/'q.grammar.json')
    raw_parent,index,shape=c.build(grammar)
    assert raw_parent==b.read_table(INPUT/'qn/raw.native.tm')
    folds=json.loads((INPUT/'qn/folds.json').read_text())
    parent,aliases=b.apply_folds(raw_parent,folds)
    assert parent==b.read_table(INPUT/'qn/machine.native.tm')
    parent_dense,parent_labels=b.dense_table(parent,194)
    assert b.table_text(parent_dense)==(INPUT/'qn/machine.tm').read_text()
    assert sha(b.table_text(parent_dense).encode())=='d1cf0f6e7a3c8f999d045694efc107dd1f9a03d45dd6c15e3d197ff7754c7231'
    old_sites,old_ins,old_cs=source(grammar,False)
    assert jtuple(old_ins)==json.loads((INPUT/'qn/instructions.json').read_text())
    assert jtuple(dict(sites=old_sites,instructions=old_ins))==json.loads((INPUT/'qn/source.json').read_text())

    raw=dict(raw_parent)
    assert raw[38,1]==(1,True,20) and raw[310,1]==(1,True,62)
    raw[38,1]=(1,True,30)
    raw[310,1]=(1,True,330)
    raw[330,0]=(0,True,63)
    raw[330,1]=(1,False,73)
    folds=folds+[[41,330,[[0,False,31],[1,False,46]]]]
    child,aliases=b.apply_folds(raw,folds)
    local=b.check_local_folds(raw,child,aliases,folds)
    assert len(shape)==67 and len(raw)==404 and len(folds)==8
    assert len(child)==388 and len(local['cases'])==32
    assert all(child[q,bit]==baseline[q,bit] for q in c.BOXSTATES for bit in (0,1))
    sites,instructions,contracts=source(grammar,True)
    assert len(sites)==3651 and len(contracts)==4751
    assert instructions[:3649]==old_ins[:3649]
    assert instructions[3649:]==[('inc',5,3650),('jump',0)]
    assert len(old_ins)==3654
    assert tuple(sites[25][0])==(1,0,0,0,0,0)
    primary_grammar=c.read_grammar(INPUT/'primary.grammar.json')
    plain_sites,plain_ins,_=source(primary_grammar,True)
    emitter_changes=[dict(site=i,old=plain_ins[i],new=instructions[i])
                     for i in range(len(instructions)) if instructions[i]!=plain_ins[i]]
    assert len(plain_ins)==len(instructions)==3651
    assert len(emitter_changes)==79
    assert min(x['site'] for x in emitter_changes)==1953
    assert max(x['site'] for x in emitter_changes)==2067
    incoming=[]
    for pc,row in enumerate(old_ins[:3649]):
        k=2 if row[0] in ('inc','dec') else 1
        incoming += [[pc,target] for target in row[k:] if target>=3649]
    assert all(target==3649 for pc,target in incoming)
    source_delta=dict(parent='PA194QN',parent_dense_sha256=sha((INPUT/'qn/machine.tm').read_bytes()),
        old_sites=len(old_sites),new_sites=len(sites),unchanged_instruction_prefix=3649,
        old_tail=old_ins[3649:],new_tail=instructions[3649:],
        incoming_from_prefix=incoming,
        changed_nodes={k:dict(old=nodes(False)[k],new=nodes(True)[k]) for k in ['node168','node171']},
        logical_registers=dict(T=1,H=5,X=6),
        arithmetic_statement='For arbitrary incoming T=t,H=h,X=x the compared operands become (x+t+h,1) in QN and (1,x+t+h) in QNS; both halt iff x+t+h=1 and otherwise leave T=h,H=X=0.')
    changes=[]
    for key in sorted(set(parent)|set(child)):
        if parent.get(key)!=child.get(key):changes.append(dict(state=key[0],read=key[1],old=parent.get(key),new=child.get(key)))
    assert {tuple((r['state'],r['read'])) for r in changes}=={(28,0),(38,1),(41,0),(41,1),(70,0),(310,1),(330,0),(330,1)}
    symbolic=c.validate(child,contracts) if full else None
    if full:assert symbolic['ok'],symbolic
    seed=b.startup(child,sites[25][0]);assert seed['steps']==58004
    dense,labels=b.dense_table(child,194)
    for name,table in [('machine.native.tm',child),('machine.tm',dense),('raw.native.tm',raw)]:
        (output/name).write_text(b.table_text(table))
    for name,value in [('labels.json',labels),('folds.json',folds),('local_cases.json',local),
                       ('source.json',dict(sites=sites,instructions=instructions)),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),
                       ('instructions.json',instructions),('source_delta.json',source_delta),('table_delta.json',changes),
                       ('emitter_delta_from_sum_NS.json',emitter_changes),('nodes.json',nodes(True))]:
        emit(output/name,value)
    receipt=dict(status='PASS',family='PA194QNS',working_states=194,transition_rows=388,
        raw_states=202,fixed_states=135,AX_readers=67,folds=8,simultaneous_fold_cases=32,
        graph_reachable_working_states=194,native_start=74,native_halt=254,dense_start=0,dense_halt=194,
        source_sites=len(sites),source_outcomes=len(contracts),unchanged_QN_prefix=3649,
        generic_runtime_performed=full,symbolic_runtime=symbolic,startup=seed,
        arithmetic_box_rows_unchanged=True,
        dense_sha256=sha(b.table_text(dense).encode()),native_sha256=sha(b.table_text(child).encode()),
        kernel_checked=False,
        scope='Exact QN-parent reconstruction, sum-comparator source equivalence, simultaneous folds, arbitrary-register source-frame contracts using inherited box lemmas, exact blank startup. A separate literal checker rederives list lemmas. The PA calibration is inherited through the proved finite-trace transport.')
    emit(output/'construction_receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=HERE/'machine')
    ap.add_argument('--quick',action='store_true')
    a=ap.parse_args();build(a.output,not a.quick)
