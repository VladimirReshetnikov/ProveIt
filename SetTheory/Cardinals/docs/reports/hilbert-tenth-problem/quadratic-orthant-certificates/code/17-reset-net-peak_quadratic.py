#!/usr/bin/env python3
"""Canonical minimum-fuel outcome extension. Two peak variables per source step.
This proves an outcome and canonical shortest run, not arbitrary reset-net traces.
"""
from source_quadratic import compile_schema,affine

def compile_peak(table,h,with_duration=True,all_durations=False,initial=None):
    if all_durations and not with_duration:raise ValueError("All durations require the duration parameter")
    assert h>=1
    d=table['register_count']
    if initial is None:initial=['L','R',0] if d==3 else (['raw_A',0] if d==2 else [f'input_{i}' for i in range(d)])
    assert len(initial)==d
    out=compile_schema(table,h,initial=initial);base=out['variables']['count']
    input_parameters=[(x,1) for x in initial if type(x) is str]
    input_constant=sum(x for x in initial if type(x) is int)
    def u(j):return base+2*j
    def v(j):return base+2*j+1
    for j in range(h):
        old=[(f'NEW{i}:{j-1}',1) for i in range(d)] if j else []
        new=[(f'NEW{i}:{j}',-1) for i in range(d)]
        out['affine_squares'].append({'name':f'peak:{j}','affine':affine(forms=old+new,
            variables=([(v(j-1),1)] if j else [])+[(u(j),1),(v(j),-1)],parameters=[] if j else input_parameters,constant=0 if j else input_constant)})
        out['quadratic_products'].append({'name':f'peak_complementarity:{j}',
            'left':affine(variables=[(u(j),1)]),'right':affine(variables=[(v(j),1)])})
    if with_duration:
        out['parameters']['N']='natural integer'
        out['affine_squares'].append({'name':'minimum_reset_duration','affine':affine(
            forms=[(f'NEW{i}:{h-1}',-3) for i in range(d)],variables=[(v(h-1),-2)]+([(base+2*h,-2)] if all_durations else []),
            parameters=[('N',1)]+input_parameters,constant=input_constant-h-d-2)})
    out['format']='canonical-minimum-reset-outcome-v1'
    out['variables']['count']=base+2*h+int(all_durations)
    if all_durations:out['variables']['padding_index']=base+2*h
    out['variables']['source_variable_count']=base
    out['variables']['peak_indexing']='u_j=base+2*j; v_j=base+2*j+1 for j=0,...,h-1'
    out['ledger']={'natural_witnesses':base+2*h+int(all_durations),'affine_squares':(d+3)*h+1+int(with_duration),'quadratic_products':(len(table['branches'])+1)*h,'degree_at_most':2}
    assert len(out['affine_squares'])==out['ledger']['affine_squares'] and len(out['quadratic_products'])==out['ledger']['quadratic_products']
    out['scope']='Externally fixed exact source-instruction horizon h. Unique nonnegative-real or natural witness for natural inputs and prescribed minimum net duration N. This is a canonical outcome projection; arbitrary supplied reset traces require the separate trace certificate. Arity grows with h.'
    if not with_duration:
        out['scope']='Externally fixed exact source horizon h. Unique nonnegative-real or natural witness for natural inputs when the source halts exactly at h; the canonical minimum net duration is an affine output expression, not a parameter. Arity grows with h.'
    if all_durations:
        out['domain']='Natural witnesses, including zero. Nonnegative-real witnesses are not equivalent: padding can be half-integral and erase the accepting-duration parity condition.'
        out['format']='canonical-all-reset-durations-natural-v1'
        out['scope']='Externally fixed exact source horizon h and arbitrary natural net duration N. Unique natural witness for every allowed duration, using padding z=(N-N_min)/2. Nonnegative-real witnesses DO NOT preserve parity: z can be half-integral. Arity grows with h.'
    return out

def add_peak_witness(w,trace,source_slots,initial_mass):
    out=dict(w);M=initial_mass;rows=[]
    for j,row in enumerate(trace):
        S=sum(row['next_registers']);u=max(S-M,0);v=max(M-S,0)
        if u:out[source_slots+2*j]=u
        if v:out[source_slots+2*j+1]=v
        M=max(M,S);rows.append({'step':j+1,'mass':S,'u':u,'v':v,'peak':M})
    return out,rows
