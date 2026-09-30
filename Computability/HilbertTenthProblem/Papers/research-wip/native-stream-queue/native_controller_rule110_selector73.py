"""Exact six-selector binary Rule110 scan FIFO; terminal C, no universality claim."""
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as sp
import native_controller_binary_selector56 as prior

# source state, read bit, append bit, target state
TRANSITIONS=((0,0,0,0),(0,1,1,1),(1,0,1,0),(1,1,1,2),(2,0,1,0),(2,1,0,2))
TABLE={(old,read):(append,new,label) for label,(old,read,append,new) in enumerate(TRANSITIONS)}
CHECKSUM_ORDER=(1,3,2,4,5,0)


def selector_outer():
    rows=[]
    acc='F5'
    for j in range(4,-1,-1):
        times=f'six_pack_m{j}'; plus=f'six_pack_a{j}'
        rows.extend([(times,'*','q',acc),(plus,'+',f'F{j}',times)])
        acc=plus
    acc=f'F{CHECKSUM_ORDER[0]}'
    for j,index in enumerate(CHECKSUM_ORDER[1:],1):
        name=f'six_sum{j+1}'
        rows.append((name,'+',acc,f'F{index}'));acc=name
    rows += [('six_q','+',acc,1),('six_odd2','*',2,'odd_half'),
             ('six_odd','+','six_odd2',1)]
    assert len(rows)==18
    return rows


def composition_rows(terminal_c, preamble=False, free_terminal=False):
    rows=[('six_state_b','+','F2','F3'),('six_target_b','*',2,'F1'),
          ('six_target_c','*',2,'F3'),('six_rhs_c','+','six_target_c','F5')]
    if terminal_c: rows += [('six_lhs_c','+','F4','q')]
    rows += [('six_read','+','six_sum2','F5')]
    rows += ([('six_input_scaled','*',128,'x'),('six_input','+','six_input_scaled',46)]
             if preamble else [('six_input','*',2,'x')])
    rows += [('six_tail','*','W','six_sum4'),('six_transport','+','six_input','six_tail'),
             ('six_width_bound','+','six_input','width_beta'),('six_divisor','*','W','L')]
    if free_terminal:
        rows += [('six_terminal_scaled','*','q','terminal_queue'),
                 ('six_transport_left','+','six_read','six_terminal_scaled')]
    return rows


def source_check(terminal_c=True, preamble=False, free_terminal=False):
    parameters=['q']+[f'F{i}' for i in range(6)]+['W','x']+(['terminal_queue'] if free_terminal else [])
    auxiliaries=prior.CORE_NAMES+['odd_half','bound_beta','width_beta','L']
    z={name:sp.Symbol(name) for name in parameters+auxiliaries}
    schedule=selector_outer()+prior.CORE+prior.BOUND+composition_rows(terminal_c,preamble,free_terminal)
    env=prior.ternary.execute(schedule,dict(z,n2=z['q']))
    equalities=[('r','six_pack_a0'),('six_q','q'),('s','six_odd'),('bs_X_bound','wn2')]
    equalities += prior.CORE_EQUALITIES
    equalities += [('six_state_b','six_target_b'),
                   ('six_lhs_c' if terminal_c else 'F4','six_rhs_c'),
                   ('six_transport_left' if free_terminal else 'six_read','six_transport'),
                   ('six_width_bound','W'),('six_divisor','q')]
    polynomials=prior.independent_sources(z)
    polynomials[0]=z['r']-sum(z[f'F{i}']*z['q']**i for i in range(6))
    polynomials[1]=sum(z[f'F{i}'] for i in range(6))+1-z['q']
    app=z['F1']+z['F2']+z['F3']+z['F4']
    read=z['F1']+z['F3']+z['F5']
    input_word=128*z['x']+46 if preamble else 2*z['x']
    terminal=z['q']*z['terminal_queue'] if free_terminal else 0
    polynomials += [z['F2']+z['F3']-2*z['F1'],
                    z['F4']+int(terminal_c)*z['q']-2*z['F3']-z['F5'],
                    read+terminal-input_word-z['W']*app,input_word+z['width_beta']-z['W'],
                    z['W']*z['L']-z['q']]
    u=z['j']*z['c']-(2*z['r']+1)
    correction=polynomials[11]*(u*u-z['y_aux']**2)
    records=[]
    for index,((left,right),poly) in enumerate(zip(equalities,polynomials)):
        adjust=correction if index==12 else 0
        assert sp.expand(env[left]-env[right]-poly-adjust)==0,index
        records.append(dict(equality=[left,right],source=str(sp.expand(poly)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==72+terminal_c+preamble+2*free_terminal and counts['*']==36+free_terminal
    assert counts['+']+counts['-']==36+terminal_c+preamble+free_terminal
    assert len(equalities)==len(polynomials)==19 and len(auxiliaries)==21
    assert set().union(*(p.free_symbols for p in polynomials))==set(z.values())
    return dict(operations=len(schedule),multiplications=36+free_terminal,
                additions_subtractions=36+terminal_c+preamble+free_terminal,
                equations=19,positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                selector_operations=62,terminal_state='C' if terminal_c else 'A',
                initial_word='128x+46' if preamble else '2x',
                terminal_queue='positive free word' if free_terminal else '0',
                aliases={'n2':'q','append':'six_sum4','read':'six_read'},
                instructions=[list(row) for row in schedule],sources=records)


def words(labels):
    return tuple(sum(1<<j for j,label in enumerate(labels) if label==i) for i in range(6))


def flow_audit():
    checked=admitted_a=admitted_c=0
    for length in range(1,8):
        q=2**length
        for labels in product(range(6),repeat=length):
            fields=words(labels)
            eq_b=fields[2]+fields[3]==2*fields[1]
            eq_a=eq_b and fields[4]==2*fields[3]+fields[5]
            eq_c=eq_b and fields[4]+q==2*fields[3]+fields[5]
            state=0;valid=True
            for label in labels:
                old,read,append,new=TRANSITIONS[label]
                if old!=state: valid=False;break
                state=new
            assert eq_a==(valid and state==0)
            assert eq_c==(valid and state==2)
            admitted_a+=eq_a;admitted_c+=eq_c;checked+=1
    return dict(arbitrary_label_words=checked,max_length=7,
                valid_A_to_A=admitted_a,valid_A_to_C=admitted_c,
                scope='All one-hot label words, including absent labels; tests exact state flow independently of FIFO')


def run(x,m):
    width=2**m;queue=2*x;state=0;mask=0;labels=[];history=[];seen=set()
    while (queue,state,mask) not in seen:
        if queue==0 and state==2 and mask==63:
            return labels,history
        seen.add((queue,state,mask))
        assert not(queue==0 and state==0) # Positive input cannot reach this endpoint.
        read=queue%2;append,new,label=TABLE[state,read]
        next_queue=queue//2+(width//2)*append
        history.append([queue,state,read,append,next_queue,new])
        labels.append(label);mask|=1<<label;queue,state=next_queue,new
    return None,None


def outer_map(x,m,labels,history):
    q=2**len(labels);width=2**m;fields=words(labels)
    assert all(fields) and labels[0]==0 and q%width==0
    app=sum(fields[i] for i in (1,2,3,4))
    read=sum(fields[i] for i in (1,3,5))
    r=sum(field*q**i for i,field in enumerate(fields))
    assert sum(fields)==q-1 and r%2==1 and r.bit_count()==len(labels)
    assert fields[2]+fields[3]==2*fields[1]
    assert fields[4]+q==2*fields[3]+fields[5]
    assert read==2*x+width*app and 0<2*x<width
    assert history[0][:2]==[2*x,0] and history[-1][4:]==[0,2]
    assert labels[-1]==5 and labels[-m:]==[5]*m
    assert history[-m][:2]==[width-1,2]
    return dict(x=x,m=m,W=width,t=len(labels),q=q,fields=list(fields),
                append=app,read=read,packed_r=str(r),width_beta=width-2*x,L=q//width,
                labels=labels,history=history,
                pell_scope='The62 selector theorem supplies all positive Pell coordinates; they are not materialized')


def fifo_audit():
    rows=[];maps=[]
    for m in range(2,11):
        accepted=0
        for x in range(1,2**(m-1)):
            labels,history=run(x,m)
            if labels is not None:
                accepted+=1
                data=outer_map(x,m,labels,history)
                if (x,m) in ((1,3),(2,3),(5,5),(3,4)):
                    maps.append(data)
        rows.append(dict(m=m,positive_inputs=2**(m-1)-1,
                         accepted_terminal_C_with_all_six_labels=accepted))
    assert any(data['x']==1 and data['m']==3 for data in maps)
    return rows,maps


def preamble_and_free_terminal():
    expected=[0,1,3,5,4,1,2]
    examples=[]
    for x in range(1,101):
        I=128*x+46
        m=(2*I).bit_length();W=2**m
        queue=I;state=0;labels=[];prefix_queue=None
        for step in range(m):
            read=queue%2;append,new,label=TABLE[state,read]
            labels.append(label);queue=queue//2+(W//2)*append;state=new
            if step==6:
                assert state==0 and queue==x+118*(W//128)
                prefix_queue=queue
        assert labels[:7]==expected and set(labels)==set(range(6))
        assert state==0 and queue>0
        fields=words(labels);app=sum(fields[i] for i in (1,2,3,4));read=sum(fields[i] for i in (1,3,5))
        assert queue==app and read==I and W*queue+read==I+W*app
        assert fields[2]+fields[3]==2*fields[1] and fields[4]==2*fields[3]+fields[5]
        assert sum(fields)==W-1 and all(fields) and fields[0]%2==1
        if x in (1,2,100):
            examples.append(dict(x=x,I=I,m=m,W=W,q=W,L=1,width_beta=W-I,
                                 terminal_queue=queue,fields=list(fields),prefix_queue=prefix_queue,labels=labels))
    return dict(prefix_labels=expected,read_prefix=46,append_prefix=118,
                prefix_next_queue='x+118*(W/128)',checked_positive_inputs=100,
                free_terminal_all_input_examples=examples,
                scope='The proof supplies a full positive75 witness for every x, not only these examples')


def verify():
    fifo,maps=fifo_audit()
    return dict(status='PASS_EXACT_RULE110_SELECTOR_FIFO73',
                source73=source_check(True),source72_empty=source_check(False),
                source74_preamble=source_check(True,True),
                source75_free_terminal_all_inputs=source_check(False,True,True),
                preamble=preamble_and_free_terminal(),
                flow=flow_audit(),fifo=fifo,positive_outer_maps=maps,
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes()).hexdigest(),
                exact_projection=('Ordinary input2x in a padded width-m binary FIFO; the six stated '
                                  'Rule110 scan transitions, initial stateA, terminal queue0/stateC, '
                                  'all six transitions used, first label0. Moduli W=2^m and q=2^t encode width and time.'),
                obstruction='The variant ending at queue0/stateA is empty for every positive input.',
                scope='Exact finite-machine relation; no universal ordinary-input compiler or universal acceptance theorem',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({key:value for key,value in result.items()
                      if key not in ('source73','source72_empty','source74_preamble','source75_free_terminal_all_inputs','positive_outer_maps','preamble')},indent=2))
