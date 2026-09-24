"""Conditional weighted transport for complete fixed-space TM scan blocks."""
from pathlib import Path
import json
import sympy as sp
import explore_finite_state_raw_queue as basic
import explore_fixed_space_raw_queue as fixed


DAG=[('U0','*','w','A0'),('U1','*','w','A1'),
     ('first_twice','+','First','First'),('zbase','+','H','first_twice'),('Z','*','w','zbase'),
     ('last_twice','+','Last','Last'),('tbase','+','H','last_twice'),
     ('full_length','*',3,'w'),('T','*','full_length','tbase')]


def run(dag,values):
    env=dict(values)
    for name,op,a,b in dag:
        assert name not in env
        a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
        env[name]=a*b if op=='*' else a+b
    return env


def verify_source():
    names='R q w H First Last A0 A1 X0 X1 D0 D1 I0 I1 F0 F1'.split()
    values=dict(zip(names,sp.symbols(' '.join(names))))
    env=run(DAG,values)
    R,q,w,H,First,Last=[values[n] for n in 'R q w H First Last'.split()]
    expected=[w*values['A0'],w*values['A1'],w*(H+2*First),3*w*(H+2*Last)]
    assert all(sp.expand(env[n]-e)==0 for n,e in zip(('U0','U1','Z','T'),expected))
    geometry=(R-1)*H-(q-1)
    boundary=R*Last-First-(q-1)
    length_residual=R*env['T']-3*(env['Z']-3*w+3*w*q)
    assert sp.expand(length_residual-3*w*(geometry+2*boundary))==0
    content=[]
    for i in (0,1):
        X,D,I,F,A=[values[f'{n}{i}'] for n in ('X','D','I','F','A')]
        substituted=R*(X-D+w*A)-3*(X-I+q*F)
        U=sp.Symbol(f'old_U{i}')
        original=R*(X-D+U)-3*(X-I+q*F)
        assert sp.expand(original-substituted-R*(U-w*A))==0
        content.append(substituted)
    assert len(DAG)==9
    assert sum(op=='*' for _,op,_,_ in DAG)==5
    return dict(materialization_operations=9,multiplications=5,additions=4,dag=DAG,
                content_residuals=[sp.sstr(v) for v in content],length_residual=sp.sstr(length_residual),
                head_geometry_residual=sp.sstr(geometry),marker_boundary_residual=sp.sstr(boundary),
                exact_content_corrections=['old_content_i-new_content_i=R*(old_Ui-w*Ai) for i=0,1'],
                exact_length_correction='length_residual=3*w*(geometry+2*boundary)',
                supplied_scalar='w=3L0^2; its construction is outside the nine-operation materialization',
                scope='Materializes four conditional weighted words from already synchronized scan data. No control selection or full verifier cost is asserted.')


def row_data(state,word,table):
    nxt,out,event=table[state,word[0]]
    return dict(n=[basic.coordinate(word,i) for i in (0,1)],W=3**len(word),
                d=list(word[0]),u=[basic.coordinate(out,i) for i in (0,1)],a=len(out),
                first=state.kind=='scan' and state.previous is None,last=word[0]==basic.DELIM,
                event=event)


def verify_block(rows,initial,final,ell):
    w=3*3**(2*ell);full=2*ell+2;R=fixed.C_RADIX*3**(2*ell)
    assert len(rows)%full==0
    vals=dict(R=R,q=R**len(rows),w=w,H=0,First=0,Last=0,A0=0,A1=0,
              X0=0,X1=0,D0=0,D1=0,I0=basic.coordinate(initial,0),I1=basic.coordinate(initial,1),
              F0=basic.coordinate(final,0),F1=basic.coordinate(final,1))
    assert len(initial)==len(final)==full
    direct=dict(U0=0,U1=0,Z=0,T=0);power=1
    for j,row in enumerate(rows):
        first=j%full==0;last=j%full==full-1
        assert row['first']==first and row['last']==last
        assert row['W']==w*(3 if first else 1)
        assert row['a']==(0 if first else 2 if last else 1)
        assert row['a']!=0 or row['u']==[0,0]
        assert row['event']==('pass' if last else '')
        vals['H']+=power;vals['First']+=int(first)*power;vals['Last']+=int(last)*power
        for i in (0,1):
            vals[f'A{i}']+=row['u'][i]*power;vals[f'X{i}']+=row['n'][i]*power
            vals[f'D{i}']+=row['d'][i]*power;direct[f'U{i}']+=row['u'][i]*row['W']*power
        direct['Z']+=row['W']*power;direct['T']+=3**row['a']*row['W']*power
        power*=R
    assert power==vals['q']
    env=run(DAG,vals)
    assert all(env[n]==v for n,v in direct.items())
    assert (R-1)*vals['H']==vals['q']-1
    assert R*vals['Last']==vals['First']+vals['q']-1
    for i in (0,1):
        assert R*(vals[f'X{i}']-vals[f'D{i}']+env[f'U{i}'])==3*(vals[f'X{i}']-vals[f'I{i}']+vals['q']*vals[f'F{i}'])
    assert R*env['T']==3*(env['Z']-3*w+3*w*vals['q'])
    if rows:
        first_bad=vals['First']+R
        assert w*(vals['H']+2*first_bad)!=direct['Z']
        assert R*vals['Last']!=first_bad+vals['q']-1
    return dict(rows=len(rows),qbits=vals['q'].bit_length(),zero_block=not rows)


def verify_runs():
    counts=dict(runs=0,blocks=0,empty_blocks=0,complete_scans=0,checked_rows=0,
                distinct_actual_rows=0,marker_perturbations=0,loader_counterexamples=0,
                unsynchronized_marker_examples=0,largest_q_bits=0)
    wanted={'initial_accept','scan_accept','right_growth','stay_accept','infinite_stay','left_sensor'}
    for machine in fixed.fixtures():
        if machine.name not in wanted:continue
        state0,table,_=machine.compile()
        for x in range(6):
            minimal=1
            while 3**minimal<=x:minimal+=1
            for pad in (0,1):
                ell=minimal+pad;w=3*3**(2*ell)
                word=tuple(fixed.PLAIN[(x//3**i)%3] for i in range(ell))+(fixed.DELIM,)
                state=state0
                loader=row_data(state,word,table)
                if loader['u'][0] and loader['W']!=w:
                    assert loader['u'][0]*loader['W']!=w*loader['u'][0];counts['loader_counterexamples']+=1
                for _ in range(ell+1):state,word,event=basic.one_queue_step(machine,state,word,table)
                assert event=='loaded'
                boundaries=[word];scans=[]
                for _ in range(40):
                    if state.kind!='scan':break
                    rows=[]
                    while True:
                        rows.append(row_data(state,word,table))
                        state,word,event=basic.one_queue_step(machine,state,word,table)
                        if event in ('pass','reject'):break
                    if event=='reject':break
                    scans.append(rows);boundaries.append(word)
                counts['runs']+=1;counts['complete_scans']+=len(scans)
                counts['distinct_actual_rows']+=sum(len(v) for v in scans)
                windows=[(0,len(scans)),(0,min(3,len(scans))),
                         (max(0,len(scans)-3),len(scans)),(0,0)]
                for start,end in windows:
                    rows=[r for scan in scans[start:end] for r in scan]
                    result=verify_block(rows,boundaries[start],boundaries[end],ell)
                    counts['blocks']+=1;counts['checked_rows']+=result['rows']
                    counts['empty_blocks']+=result['zero_block'];counts['marker_perturbations']+=bool(rows)
                    counts['largest_q_bits']=max(counts['largest_q_bits'],result['qbits'])
    for R in (27,81,243):
        # The boundary identity alone permits scans of lengths 1 and 3.
        q=R**4;first=1+R;last=1+R**3
        assert R*last==first+q-1
        assert first!=1 and last!=R**3
        counts['unsynchronized_marker_examples']+=1
    assert counts['loader_counterexamples']>0
    return counts


def verify():
    return dict(status='PASS_FIXED_SCAN_WEIGHTED_TRANSPORT',source=verify_source(),finite=verify_runs(),
                proof='../1980/EXPLORATION_FIXED_SCAN_WEIGHTED_TRANSPORT.md',
                review_status='Author and independent root/binary_encoding full proof/source audits and fresh verify runs PASS; no findings. Publication is separate.',
                scope='Complete legal fixed-space scan blocks only. Raw loading, draining, partial scans, control realization and all positive adapters remain outside this conditional lemma.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['finite'])
