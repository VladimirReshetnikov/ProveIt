#!/usr/bin/env python3
"""Literal unary-list verification with explicit affine physical clocks.

The four list traversal lemmas are derived from the candidate's own table.
The interpreter is copied unchanged from the AX11H packet whose mathematical
iPRA soundness audit is supplied with the HC4 references. No arithmetic-box
oracle is used. This executable is not a proof-assistant kernel.
"""
from pathlib import Path
import argparse,hashlib,json,sys,time
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'literal_engine'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
sym.HEADER_BASE=48
if not __debug__ or sys.flags.optimize:raise RuntimeError('Disable optimized Python.')
FAMILIES={
 'C32':dict(name='PA194C32',base=P,native=P/'cycle32'/'pa194_cycle32.native.tm',dense=P/'cycle32'/'pa194_cycle32.tm',labels=P/'cycle32'/'labels.json',physical=(6,4,0,3,2,8,7,5,1),native_hash='7a83339f95624c0d9b3935f081f226b17461dac6c4660e03a400ce04be8e0a9e',dense_hash='3af42ea9d430e5df22b69e6fc540e3530f87263372580c7c554bae37ba524ac8',graph_hash='78e7ceb6ada6c162c6a72dea0efc3a0fd9e7c67b2a9015823569f077f3e9d90d',sites=3673,outcomes=4780,startup=56250),
 'HC4':dict(name='PA194AX11HC4',base=P/'ax11hc4',native=P/'ax11hc4'/'machine'/'pa194_ax11hc4.native.tm',dense=P/'ax11hc4'/'machine'/'pa194_ax11hc4.tm',labels=P/'ax11hc4'/'machine'/'labels.json',physical=(6,4,0,3,5,7,8,2,1),native_hash='8081a0ef2c2054963d3153f2a4ad385a381a9d7abe7c0301e0c98e830b2433e1',dense_hash='fe4253a42045c330a499d99cc33d55a14e116cae910eb624c499161a7a7ca755',graph_hash='f92f084b44d6ffc187ceb1bfc67672baea96fc35c72267f150cc9efe4fcda65b',sites=3671,outcomes=4778,startup=57406)
}
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('family',choices=FAMILIES);args=parser.parse_args();cfg=FAMILIES[args.family];started=time.time()
    out=cfg['base']/'receipts'/'literal';out.mkdir(parents=True,exist_ok=True)
    assert sha(cfg['native'].read_bytes())==cfg['native_hash']
    assert sha(cfg['dense'].read_bytes())==cfg['dense_hash']
    rows=runtime.table(cfg['native']);dense=runtime.table(cfg['dense']);labels=json.loads(cfg['labels'].read_text())
    assert len(rows)==388 and len({q for q,b in rows})==194
    assert {(labels[q],b):(w,d,labels[n]) for(q,b),(w,d,n) in dense.items()}==rows
    grammar=json.loads((cfg['base']/'source'/'source_grammar.json').read_text());sites=[]
    op={'i':'CI','d':'CD','b':'CB','c':'CC','h':'CH'}
    def expand(i,p):
        e=grammar['entries'][i]
        if isinstance(e,str):sites.append([p,op[e[0]],int(e[1:]) if len(e)>1 else None])
        else:expand(e[0],p+'0');expand(e[1],p+'1')
    expand(grammar['root'],'');assert len(sites)==cfg['sites']
    graph,_=source.graph_arithmetic(sites);assert graph==source.graph_intervals(sites)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    instructions=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
    assert sha((json.dumps(instructions,separators=(',',':'))+'\n').encode())==cfg['graph_hash']
    mapping={int(k):v for k,v in json.loads((P/'literal_engine'/'legacy_mapping.json').read_text()).items()}
    for q in {q for q,b in rows}|{254}:mapping.setdefault(q,q+10000)
    assert len({mapping[q] for q,b in rows}|{mapping[254]})==195
    assert mapping[84]==96 and mapping[254]==254
    table={(mapping[q],b):(w,d,mapping[n]) for(q,b),(w,d,n) in rows.items()}
    runtime.PHY=cfg['physical'];lemmas,blocks=sym.prove_blocks(table);assert len(blocks)==4
    print(cfg['name'],'four literal list lemmas rederived',flush=True)
    contracts=[]
    for i,site in enumerate(sites):
        for positive in ([False,True] if site[1]=='CD' else [False]):
            result=sym.case(table,lemmas,site,positive)
            contracts.append({'site':i,'positive':positive,'duration':result['duration'],'motion':result['motion'],'symbolic_steps':result['symbolic_steps']})
        if (i+1)%1000==0:print('checked',i+1,'sites in',round(time.time()-started,2),'seconds',flush=True)
    assert len(contracts)==cfg['outcomes']
    assert all(sym.nonnegative(c['duration']) and c['duration'][0]>0 for c in contracts)
    tape=bytearray(4096);origin=2048;head=origin;q=74
    for t in range(cfg['startup']):
        assert 0<=head<len(tape) and q!=254
        w,d,q=rows[q,tape[head]];tape[head]=w;head+=d
    assert q==84 and head-origin==-2
    logical=[2]+[0]*8;physical=[None]*9
    for r,p in enumerate(cfg['physical']):physical[p]=logical[r]
    pc=sites[25][0];frame=bytearray([1]+list(map(int,pc))+[0]*(48-len(pc))+[1])
    for value in physical+[1]*26:frame.extend([0]+[1]*(value+1))
    expected=bytearray(4096);expected[head-1:head-1+len(frame)]=frame;assert tape==expected
    encoded=(json.dumps(contracts,separators=(',',':'))+'\n').encode();(out/'contracts.json').write_bytes(encoded)
    (out/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
    receipt=dict(name=cfg['name'],status='PASS',working_states=194,transition_rows=388,native_sha256=cfg['native_hash'],dense_sha256=cfg['dense_hash'],physical_map=cfg['physical'],source_sites=len(sites),source_outcomes=len(contracts),symbolic_events=sum(c['symbolic_steps'] for c in contracts),maximum_symbolic_events=max(c['symbolic_steps'] for c in contracts),minimum_duration_constant=min(c['duration'][0] for c in contracts),literal_list_lemmas=len(blocks),arithmetic_box_oracles=False,complete_blank_tape_equality=True,startup_steps=cfg['startup'],contracts_sha256=sha(encoded),proof_assistant_kernel_checked=False,scope='Universal literal source-frame simulation with explicit positive affine physical clocks, independently resolved source graph, four list-induction lemmas derived from candidate rows, and exact blank startup. Logical PA calibration is inherited separately.')
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
