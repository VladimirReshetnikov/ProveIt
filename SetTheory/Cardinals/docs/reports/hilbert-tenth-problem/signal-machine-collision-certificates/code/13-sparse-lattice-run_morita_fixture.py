#!/usr/bin/env python3
"""Emit and replay an actual bounded first-pulse certificate for doubling.

This uses the declared 97-row simulation subtable, not the 17,576-row universal
full-configuration lookup. Every row is bound to a completed conserving local
permutation. The fixed worked source is not a universal machine.
"""
import argparse
import json
from pathlib import Path

import morita_audit
from sparse_mass import LocalTable, compile_morita_inputs, physical_step, verify_bound_export


HERE=Path(__file__).resolve().parent
DELTA=[(0,1,'Z',1),(1,0,'Z',6),(1,0,'P',2),(2,0,'-',3),
       (3,1,'+',4),(4,1,'+',5),(5,1,'P',1)]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=int,default=2)
    args=parser.parse_args()
    if args.input<0:
        raise ValueError('nonnegative input required')
    bad,partial,_=morita_audit.audit_rows(7,morita_audit.compile_partial(7,DELTA))
    assert not bad
    complete=morita_audit.complete(7,partial)
    table=LocalTable.from_mapping(25,complete)
    assert table.reversible and len(partial)==97 and len(table.rows)==17576
    source=(0,args.input,0)
    macrosteps=[]
    t=0
    while source[0]!=6:
        after,duration=morita_audit.machine_step(DELTA,*source)
        macrosteps.append({'before':source,'after':after,'start_time':t,'duration':duration})
        source=after;t+=duration
    T=t+3
    builder,metadata=compile_morita_inputs(table,7,0,None,args.input,0,T,first_pulse=True,
                                          allowed_inputs=tuple(partial))
    assert builder.validate_witness()
    assert builder.decode_solution(T,builder.values)==builder.decode(T)
    history=builder.decode(T)
    current=morita_audit.encode(7,DELTA,0,args.input,0)
    for index,actual in enumerate(history):
        assert current==actual
        assert sum(map(sum,actual.values()))==26
        assert actual.get(-1,(0,0,0))[0]==int(index==T)
        if index<T:
            current=physical_step(table,current)
    assert source==(6,0,2*args.input)
    assert history[T].get(0,(0,0,0))[1]==23+(2 if args.input==0 else 0)
    fixture=HERE/'fixtures'/f'morita_doubling_n{args.input}_pulse_T{T}.json.gz'
    payload=builder.export(fixture,metadata)
    counts=payload['counts']
    maxbits=max(x.bit_length() for x in builder.values)
    height=max(builder.values)
    del payload,builder
    replay=verify_bound_export(fixture)
    assert replay['valid']
    M=26;s=97
    V0=4+3*M*(M-1)
    R0=V0
    V=T*(M*(s+14)+5*M*(M-1))+V0+4*M*T+3*M
    R=T*(17*M+5*M*(M-1))+R0+4*M*T+2*M+T
    assert (counts['witnesses'],counts['residuals'])==(V,R)
    report={'status':'passed','input_n0':args.input,'input_n1':0,'source_delta':DELTA,
            'source_is_universal':False,'macrosteps':macrosteps,'final_source':source,
            'final_source_time':t,'pulse_time':T,'M':M,'K':25,
            'total_table_rows':len(table.rows),'declared_partial_rows':s,
            'lookup_contract':'Each actual queried input triple must lie in the explicit 97-row set; every row is verified against the total table.',
            'counts':counts,'actual_max_witness':height,'actual_max_witness_bits':maxbits,
            'certificate_file':fixture.name,'compressed_bytes':fixture.stat().st_size,
            'full_polynomial_coefficients_exported':True,'all_exported_residuals_replayed':True,
            'history':[{'t':i,'configuration':[[x,list(state)] for x,state in sorted(c.items())]} for i,c in enumerate(history)]}
    out=HERE/f'morita_fixture_n{args.input}_results.json'
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('history','macrosteps')},indent=2))


if __name__=='__main__':
    main()
