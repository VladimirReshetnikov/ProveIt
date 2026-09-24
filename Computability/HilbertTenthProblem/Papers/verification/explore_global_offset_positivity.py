#!/usr/bin/env python3
"""Independent positivity and marked-prefix audit for the global offset."""
from pathlib import Path
import json
import explore_three_raw_counter_compiler as compiler
import explore_cyclic_entry_serial_composition as cyclic
import explore_raw_ternary_zero_target as raw


def mark_prefix_zero(graph):
    """Return a copied compiler graph with one harmless mandatory zero test.

    The finite graph, signs, phases, entries and endpoints are unchanged.
    Only the first plus-phase instruction on initially zero register1
    acquires a true source-zero label. Apply this before cyclic_graph().
    """
    prefix=graph['prefix'];marked=prefix[1]
    assert prefix==[('prefix','jump',phase,lane) for phase in range(2) for lane in range(3)]
    assert graph['nodes'][marked]==(1,1,0)
    result=dict(graph,nodes=dict(graph['nodes']))
    result['nodes'][marked]=(1,1,1)
    result['positivity_zero_vertex']=marked
    assert {n for n in graph['nodes'] if graph['nodes'][n]!=result['nodes'][n]}=={marked}
    assert result['edges']==graph['edges'] and result['initial']==graph['initial']
    return result


def build_marked_graph(code,start):
    """Reusable entry point for the global-offset source compiler."""
    return mark_prefix_zero(compiler.serial_graph(code,start))


def verify_walk_positivity():
    walks=split_checks=0
    def visit(value,remaining,sources,signs):
        nonlocal walks,split_checks
        if remaining==0:
            if value:return
            assert 2 in sources and signs[0]==1 and signs[-1]==-1 and sources[-1]==1
            for variant in range(3):
                parts=[raw.split_ternary(n,b+variant) for b,n in enumerate(sources)]
                assert all(a+b==n for (a,b),n in zip(parts,sources))
                assert sum(a for a,b in parts)>0 and sum(b for a,b in parts)>0
                split_checks+=1
            walks+=1
            return
        if value>remaining or (value-remaining)%2:return
        for sign in (-1,1):
            if value+sign>=0:visit(value+sign,remaining-1,sources+[value],signs+[sign])
    for x in range(1,5):
        for height in range(2*x+2,15,2):
            visit(2*x+1,height-1,[2*x],[1])
    assert walks==1714 and split_checks==5142
    return dict(complete_first_plus_unit_walks=walks,track_split_checks=split_checks,
                initial_inputs=list(range(1,5)),maximum_walk_length=14,
                scope='Every nonnegative first-plus unit walk in the stated finite ranges ending at zero, with three concrete two-track split variants. The arbitrary-length claim is proved in the note.')


def verify_marked_compiler():
    machine=compiler.sample_machine();code=machine['code']
    original=compiler.serial_graph(code,machine['start'])
    graph=mark_prefix_zero(original);quotient=cyclic.cyclic_graph(graph)
    assert len(original['nodes'])==len(graph['nodes']) and len(original['edges'])==len(graph['edges'])
    marked=graph['positivity_zero_vertex']
    assert quotient['nodes'][marked]==(1,1,1)
    prefix_cases=0
    for x in range(101):
        initial=[2*x,0,0]
        assert compiler.apply_serial(graph['nodes'],graph['prefix'],initial)==initial
        # The same prefix is admissible after any completed cleanup return.
        assert compiler.apply_serial(quotient['nodes'],graph['prefix'],[0,0,0])==[0,0,0]
        prefix_cases+=1

    accepted=rejected=blocks_checked=zero_tests=repeated_returns=0;traces=[]
    for x in range(1,32):
        physical=[2*x,0,0];blocks=0;previous=None
        has_plus=has_minus=has_zero=has_nozero=False
        track_positive=[False,False];first_counter_visits_two=False
        first_label=last_source=None
        def execute(sequence):
            nonlocal physical,blocks,previous,zero_tests,has_plus,has_minus,has_zero,has_nozero
            nonlocal first_counter_visits_two,first_label,last_source
            for node in sequence:
                if previous is not None:assert (previous,node) in quotient['edges']
                lane,sign,zero=quotient['nodes'][node];value=physical[lane]
                if zero:assert value==0;zero_tests+=1
                if first_label is None:first_label=(lane,sign,zero)
                first_counter_visits_two |= lane==0 and value==2
                a0,a1=raw.split_ternary(value,blocks)
                assert a0+a1==value
                track_positive[0] |= a0>0;track_positive[1] |= a1>0
                has_plus |= sign==1;has_minus |= sign==-1
                has_zero |= zero==1;has_nozero |= zero==0
                last_source=(value,sign,zero)
                physical[lane]+=sign;assert min(physical)>=0
                previous=node;blocks+=1
        execute(graph['prefix'])
        assert physical==[2*x,0,0] and has_zero and first_label==(0,1,0)
        def check_step(pc,before,branch,target,after):
            assert physical==[2*n for n in before]
            sequence=graph['macros'][(pc,branch)]
            assert all(node!=quotient['initial'] for node in sequence)
            execute(sequence)
            assert physical==[2*n for n in after]
        halt,values,steps=compiler.run(code,machine['start'],[x,0,0],callback=check_step)
        endpoint=graph['entries'][halt][0]
        if endpoint==graph['final']:endpoint=quotient['initial']
        assert (previous,endpoint) in quotient['edges']
        expected,_=compiler.direct_tm(machine,x)
        assert expected==bool(code[halt][1])
        if expected:
            assert endpoint==quotient['initial'] and previous in quotient['accept_predecessors']
            assert physical==[0,0,0] and blocks%6==0
            assert first_counter_visits_two and all(track_positive)
            assert has_plus and has_minus and has_zero and has_nozero and last_source==(1,-1,0)
            assert compiler.apply_serial(quotient['nodes'],graph['prefix'],physical)==[0,0,0]
            accepted+=1;repeated_returns+=1
        else:
            assert endpoint!=quotient['initial'] and previous not in quotient['accept_predecessors']
            rejected+=1
        blocks_checked+=blocks
        traces.append(dict(x=x,accepted=expected,logical_instructions=steps,serial_blocks=blocks,
                           mandatory_zero_seen=has_zero,both_tracks_positive=all(track_positive),
                           last_source=list(last_source),final_physical=physical))
    assert accepted==16 and rejected==15
    return dict(raw_inputs=31,accepted=accepted,rejected=rejected,
                unchanged_serial_vertices=len(graph['nodes']),cyclic_vertices=len(quotient['nodes']),
                unchanged_serial_edges=len(graph['edges']),modified_vertex=list(marked),
                prefix_cases=prefix_cases,checked_serial_blocks=blocks_checked,
                checked_source_zero_requests=zero_tests,accepted_repeated_prefixes=repeated_returns,
                complete_serial_traces=traces,
                scope='One fixed compiled machine on all raw inputs1..31. Every serial edge, changed/unchanged zero request and physical update is freshly followed. General first-return equivalence and all raw-field positivity are proved separately.')


def verify():
    return dict(status='PASS_GLOBAL_OFFSET_POSITIVITY',unit_walks=verify_walk_positivity(),
                marked_compiler=verify_marked_compiler(),
                proof='../1980/EXPLORATION_GLOBAL_OFFSET_POSITIVITY.md',
                scope='The positivity and unchanged-language compiler interface needed by the proposed global native offset. This focused audit does not itself certify its arithmetic operation count or a new universal bound.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['unit_walks'])
    print({k:v for k,v in result['marked_compiler'].items() if k not in ('scope','complete_serial_traces')})
