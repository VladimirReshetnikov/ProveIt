#!/usr/bin/env python3
"""Exact118 serial composition and the universal compiler's cyclic entry."""
from pathlib import Path
import json
import sympy as sp
import explore_merged_serial_bounds as old
import explore_three_raw_counter_compiler as compiler


SYM=old.SYM
OUTER_NAMES=old.OUTER_NAMES
CORE_NAMES=old.CORE_NAMES
PROGRAM=old.PROGRAM
assert PROGRAM['I']==PROGRAM['F'] and PROGRAM['initial']==PROGRAM['final']


def build():
    prior_ops,prior_pairs,prior_source,_=old.build()
    ops=[]
    for name,op,left,right in prior_ops:
        if name=='route_lhs':continue
        if name=='route_final':right='twice_J'
        ops.append((name,op,left,right))
    pairs=prior_pairs[:-1]+[('route_product','route_rhs')]
    c=PROGRAM;z=SYM
    route=(z['R']*c['K']-c['g'])*z['PC']-2*c['g']*c['I']*z['Jrep'] \
          -z['R']*(z['PV']+c['hs']*(z['FKplus']-z['Jrep'])+c['hz']*(z['FZ']-z['Jrep']))
    source=prior_source[:-1]+[route]
    return ops,pairs,source


def verify_certificate():
    ops,pairs,source=build();env=dict(SYM)
    hist=old.old.old.aligned.baseline.run_schedule(ops,env);records=[]
    prior_source=old.build()[2];gI=PROGRAM['g']*PROGRAM['I']
    assert sp.expand(source[-1]-prior_source[-1]-gI*prior_source[0])==0
    u=SYM['j']*SYM['c']+2*SYM['r']+1
    for i,((left,right),p) in enumerate(zip(pairs,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[17]*(u*u-SYM['y_aux']**2) if i==18 else 0
        assert sp.expand(actual-p-extra)==0,i
        if i<len(source)-1:assert p==prior_source[i]
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(p),correction=sp.sstr(extra)))
    primitive,counts=old.old.old.aligned.verify_primitives(ops,env)
    assert len(primitive)==118 and counts=={'+':62,'*':56}
    assert len(source)==len(pairs)==31 and len(OUTER_NAMES+CORE_NAMES)==43
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    return dict(status='PASS',operations=118,primitive_histogram=counts,histogram=hist,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=43,
                equations=31,primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_delta=dict(deleted_register='route_lhs',changed_product='route_final=(gI)*twice_J',
                    new_comparison='route_product=route_rhs',
                    route_residual_identity='new=old+gI*(q-2J-1)',unchanged_source_count=30),
                scope='Specialization to identical initial/final control state, with an exact same-witness source equivalence.')


def cyclic_graph(graph):
    initial,final=graph['initial'],graph['final']
    assert initial!=final
    assert not any(v==initial for _,v in graph['edges'])
    assert not any(u==final for u,_ in graph['edges'])
    quotient=lambda node:initial if node==final else node
    nodes={node:label for node,label in graph['nodes'].items() if node!=final}
    edges={(quotient(u),quotient(v)) for u,v in graph['edges']}
    assert len({quotient(n) for n in graph['nodes']})==len(graph['nodes'])-1
    assert all(u!=v and nodes[v][0]==(nodes[u][0]+1)%3 for u,v in edges)
    old_accept_predecessors={u for u,v in graph['edges'] if v==final}
    assert {u for u,v in edges if v==initial}==old_accept_predecessors
    assert all(nodes[u][0]==2 for u in old_accept_predecessors)
    assert {v for u,v in edges if u==initial}=={v for u,v in graph['edges'] if u==initial}
    assert nodes[initial]==(0,1,0)
    return dict(nodes=nodes,edges=edges,initial=initial,final=initial,
                removed=final,accept_predecessors=old_accept_predecessors)


def verify_cyclic_compiler():
    machine=compiler.sample_machine();code=machine['code']
    graph=compiler.serial_graph(code,machine['start']);cyclic=cyclic_graph(graph)
    accepted=rejected=blocks_checked=0;traces=[]
    for x in range(1,32):
        physical=compiler.apply_serial(cyclic['nodes'],graph['prefix'],[2*x,0,0])
        assert physical==[2*x,0,0]
        previous=graph['prefix'][-1];blocks=6;visited_initial=0
        def check_step(pc,before,branch,target,after):
            nonlocal physical,previous,blocks,visited_initial
            sequence=graph['macros'][(pc,branch)]
            assert (previous,sequence[0]) in cyclic['edges']
            assert all(node!=cyclic['initial'] for node in sequence)
            assert physical==[2*n for n in before]
            physical=compiler.apply_serial(cyclic['nodes'],sequence,physical)
            assert physical==[2*n for n in after]
            previous=sequence[-1];blocks+=len(sequence)
        halt,values,steps=compiler.run(code,machine['start'],[x,0,0],callback=check_step)
        old_endpoint=graph['entries'][halt][0]
        endpoint=cyclic['initial'] if old_endpoint==graph['final'] else old_endpoint
        assert (previous,endpoint) in cyclic['edges']
        expected,_=compiler.direct_tm(machine,x)
        if expected:
            assert previous in cyclic['accept_predecessors']
            assert endpoint==cyclic['initial'] and physical==[0,0,0] and blocks%6==0
            visited_initial+=1;accepted+=1
        else:
            assert endpoint!=cyclic['initial'] and previous not in cyclic['accept_predecessors']
            rejected+=1
        assert visited_initial==int(expected)
        blocks_checked+=blocks
        traces.append(dict(x=x,accepted=expected,logical_instructions=steps,serial_blocks=blocks,
                           positive_returns=visited_initial,final_physical=physical))
    return dict(raw_inputs=31,accepted=accepted,rejected=rejected,complete_serial_traces=traces,
                original_vertices=len(graph['nodes']),cyclic_vertices=len(cyclic['nodes']),
                original_edges=len(graph['edges']),cyclic_edges=len(cyclic['edges']),
                accepting_predecessors=len(cyclic['accept_predecessors']),serial_blocks=blocks_checked,
                scope='Exact graph quotient, unique-label preservation, phase/no-shortcut structure, and every labelled step of31 sample-machine runs. Universality and arbitrary first-return soundness are the separate general proof.')


def canonical(x):
    result=old.canonical(x)
    result['inherited_119_outer_residuals']=result.pop('outer_residuals')
    result['retained_118_outer_residuals']=21
    result['route_check']='new route residual is old route residual plus gI times the already zero geometry residual; all21 outer equalities follow.'
    return result


def verify():
    return dict(status='PASS_CYCLIC_ENTRY_SERIAL_COMPOSITION_118',arithmetic=verify_certificate(),
                cyclic_compiler=verify_cyclic_compiler(),canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_CYCLIC_ENTRY_SERIAL_COMPOSITION.md',
                scope='A complete118-operation universal family using a cyclic-entry version of the strong raw-input compiler. It remains above the existing universal frontier90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print({k:v for k,v in result['cyclic_compiler'].items() if k not in ('scope','complete_serial_traces')})
    print(result['canonical'])
