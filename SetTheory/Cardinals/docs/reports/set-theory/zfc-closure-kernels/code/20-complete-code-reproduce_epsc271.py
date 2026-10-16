#!/usr/bin/env python3
"""Offline regeneration and local verification of the EPSC271 control.

This is a measured component, not an end-to-end ZFC consistency machine.
The ordinary schema calibration is proved in sections/low_code_epsc.tex.
The altered literal compiler/initializer still needs a universal simulation.

The builder adapter and structured helper interpreter are adapted from
ProveIt's recover_wade_dag.py and pairing_backend_experiment.py (MIT-0;
see vendor/epsc271/LICENSE.ProveIt). Andrew Wade's backend is unchanged.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import re
import sys

from hole_codec import pair, audit as audit_codec

REGISTERS=['nextproof','topwff','wffstack','axiomcode','param1','param2','scratch1','scratch2','prooflist']
EXPECTED={
    'TMBuilder.py':'03d3a636404e1bcdeceafd98b9478b7a367ab334f3ab9f8a00df1d5c03fdf517',
    'tm.py':'2d00bf8c8324d8e9bc5639ba14e508091d854a7c93ecb96ab598f41c15ae9787',
    'tmdb.py':'4ccf4dab37438109a350d77259b5eb52e33ce110a954cd2d56a218e84e653526',
    'LICENSE.wade':'c1dffee77db98625debe39b47538e1d2f3b7956cbc7bcd6ed9363701b2177cfa',
    'epsc270_dag.json':'3eebec7e4c8b162146a45862441a4855d7e742b764c12be42702f8474f4bf24d'}


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def build(backend,nodes,names):
    b=backend.TMBuilder()
    regs=[b.reg(n) for n in REGISTERS]
    def leaf(e):
        if e=='EHalt':return 'halt'
        k,v=e.split();n=int(v)
        if k=='ENode':return n
        if k=='EInc':return regs[n].inc
        if k=='EDecnz':return regs[n].decnz
        return f"_{'break' if k=='EBreak' else 'continue'}.{n}"
    for q in range(len(nodes)):
        seq=backend.Sequence(tuple(map(leaf,nodes[q])))
        seq.name=names[q]
        b.sequences.append(seq)
    return b


def execute_helper(builder,root,values,fuel=1000000):
    remaining=[fuel]
    def run(edge):
        remaining[0]-=1
        if remaining[0]<0:raise RuntimeError('Helper fuel exhausted')
        if isinstance(edge,int):
            while True:
                left,right=builder.sequences[edge].seq
                result=run(left)
                if result[0]=='break':
                    return ('normal',) if result[1]==1 else ('break',result[1]-1)
                if result[0]!='normal':return result
                result=run(right)
                if result[0]=='continue':
                    if result[1]==1:continue
                    return ('continue',result[1]-1)
                return result
        if edge.startswith('_break.'):return 'break',int(edge.split('.')[1])
        if edge.startswith('_continue.'):return 'continue',int(edge.split('.')[1])
        if edge=='halt':return('halt',)
        _,name,kind=edge.split('.')
        register=REGISTERS.index(name)
        if kind=='inc':
            values[register]+=1
            return('normal',)
        if values[register]:
            values[register]-=1
            return('normal',)
        return 'break',1
    return run(root)


def reextract(machine,nodes,names):
    byname={n:q for q,n in names.items()}
    regs={n:i for i,n in enumerate(REGISTERS)}
    count=0
    for q,edges in nodes.items():
        for bit,expected in enumerate(edges):
            action=machine.states[names[q],str(bit)]
            target=action.nextstate
            if target in byname:actual=f'ENode {byname[target]}'
            elif target=='halt':actual='EHalt'
            elif m:=re.fullmatch(r'3\.(.*)\.(inc|decnz)',target):
                actual=f"{'EInc' if m[2]=='inc' else 'EDecnz'} {regs[m[1]]}"
            elif target.startswith('6.break.'):
                actual=f"EBreak {int(target.rsplit('.',1)[1])+(bit==0)}"
            elif target.startswith('6.continue.'):
                actual=('EBreak 0' if bit==0 and action.write=='1' else
                        f"EContinue {int(target.rsplit('.',1)[1])+bit}")
            else:raise ValueError(('Unexpected target',target))
            assert actual==expected,(q,bit,actual,expected)
            direct=expected.split()[0] in ('ENode','EInc','EDecnz','EHalt')
            write=str(bit) if direct else ('1' if expected=='EBreak 0' and bit==0 else '0')
            assert action.write==write and action.direction==('R' if direct else 'L')
            count+=1
    return count


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--codec-bound',type=int,default=100000)
    args=ap.parse_args()
    if not __debug__:ap.error('Run without -O')
    package=Path(__file__).resolve().parents[1]
    vendor=package/'vendor/epsc271'
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    for n,h in EXPECTED.items():
        if digest(vendor/n)!=h:raise ValueError('Pinned source changed: '+n)
    sys.path.insert(0,str(vendor))
    backend=importlib.import_module('TMBuilder')
    obj=json.loads((vendor/'epsc270_dag.json').read_text())
    nodes={int(q):tuple(es) for q,es in obj['nodes'].items()}
    names={int(q):n for q,n in obj['names'].items()}
    baseline=build(backend,nodes,names)
    baseline.generate();baseline.tm.gc()
    baseline.tm.save(str(out/'epsc270_named.tm'))
    assert len({q for q,_ in baseline.tm.states})==270
    assert digest(out/'epsc270_named.tm')=='7da27473d0a33bd810cf7f7ab4d5515178d7f3a9b88a51928198e588325ff797'
    byname={n:q for q,n in names.items()}
    wel,imp,add4=[byname[n] for n in ('wel().0','fn_45().0','node_042.0')]
    assert nodes[wel]==(f'ENode {imp}','EInc 1')
    fresh=len(nodes)
    nodes[fresh]=(f'ENode {add4}','EInc 1')
    names[fresh]='hole_codec_add5().0'
    nodes[wel]=(f'ENode {imp}',f'ENode {fresh}')
    changed=dict(root=0,axioms_root=obj['axioms_root'],nodes=nodes,names=names)
    encoded=json.dumps(changed,indent=2,sort_keys=True)+'\n'
    (out/'epsc271_dag.json').write_text(encoded)
    assert (out/'epsc271_dag.json').read_bytes()==(package/'data/epsc271_dag.json').read_bytes()
    candidate=build(backend,nodes,names)
    checks=0
    roots=((imp,0),(wel,5),(byname['wal().0'],2),(byname['weq().0'],3))
    for a,b,rest in itertools.product(range(5),range(5),(0,1,5)):
        for root,offset in roots:
            values=[7,b,pair(a,rest),0,11,13,0,0,19]
            expected=[7,4*pair(a,b)+offset,rest,0,11,13,0,0,19]
            assert execute_helper(candidate,root,values)==('normal',) and values==expected
            checks+=1
    candidate.generate();candidate.tm.gc()
    candidate.tm.save(str(out/'epsc271_named.tm'))
    assert digest(out/'epsc271_named.tm')=='2f4035379c90afb90f56d9ef2655404584046caf42118d318a4ec70ce2aec8ec'
    edge_checks=reextract(candidate.tm,nodes,names)
    working={q for q,_ in candidate.tm.states}
    missing=[(q,b) for q in sorted(working) for b in ('0','1') if (q,b) not in candidate.tm.states]
    assert missing==[('1.inc','1')]
    ordered=[candidate.tm.start]+sorted(working-{candidate.tm.start})
    ids={n:i for i,n in enumerate(ordered)};ids['halt']=len(ordered)
    total=['#! start 0']
    for q in ordered:
        for bit in ('0','1'):
            action=candidate.tm.states.get((q,bit))
            write,direction,target=((bit,'R',ids['halt']) if action is None else
                                   (action.write,action.direction,ids[action.nextstate]))
            total.append(f'{ids[q]} {bit} {write} {direction} {target}')
    (out/'epsc271.tm').write_text('\n'.join(total)+'\n')
    mapping=dict(start=0,halt=len(ordered),working_names=ordered)
    (out/'epsc271_state_map.json').write_text(json.dumps(mapping,indent=2,sort_keys=True)+'\n')
    # A separate text-level parser validates the literal table and graph.
    parsed={}
    for line in (out/'epsc271.tm').read_text().splitlines()[1:]:
        q,bit,w,d,target=line.split();key=(int(q),int(bit))
        assert key not in parsed and w in ('0','1') and d in ('L','R')
        assert 0<=int(target)<=271
        parsed[key]=(int(w),d,int(target))
    assert set(parsed)==set(itertools.product(range(271),(0,1)))
    seen,pending=set(),[0]
    while pending:
        q=pending.pop()
        if q in seen:continue
        seen.add(q)
        if q<271:pending.extend(parsed[q,b][2] for b in (0,1))
    assert set(range(271))<=seen
    result=dict(status='Measured control; ordinary schema calibrated, literal simulation not yet proved',
        working_states=len(working),decision_states=len(nodes),framework_states=len(working)-len(nodes),
        partial_transition_rows=len(candidate.tm.states),total_transition_rows=len(parsed),
        missing_backend_row=missing,ordinary_partial_halting_completion=True,
        all_working_states_graph_reachable=True,decision_edges_reextracted=edge_checks,
        constructor_register_cases=checks,codec_audits=audit_codec(args.codec_bound),
        formula_codec={'Truth':0,'Bottom':1,'Imp':'4P','All':'4P+2','Eq':'4P+3','Rel':'4P+5'},
        registers=REGISTERS,register_initial_values=[0]*9,
        start_state=0,halt_state=271,standard_input='blank binary tape',
        named_table_sha256=digest(out/'epsc271_named.tm'),
        total_table_sha256=digest(out/'epsc271.tm'),
        changed_dag_sha256=digest(out/'epsc271_dag.json'),
        generator_sha256=digest(Path(__file__)),
        upstream_backend_commit='297ab8df7e5de329605c3875b4934643b371a5e3',
        pinned_inputs=EXPECTED,full_literal_machine_proof=False,new_state_bound_claimed=False)
    (out/'epsc271_results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':main()
