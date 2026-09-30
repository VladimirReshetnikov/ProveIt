"""Paid append00/12 filter; exact endpoints and affine-input obstruction."""
import argparse
from collections import Counter,deque
from itertools import product
import hashlib
import json
from math import gcd
from pathlib import Path
import sympy as sp
import input_bridge_boolean_ternary60 as prior

SPLITS={0:((0,0),),1:((1,0),(0,1)),2:((1,1),)}
WEIGHTS=(-5,2,-28,56)  # append0,append1,read0,read1
BOUNDARY=(-14,-7,0,7,14,21)


def source_check(endpoint=None, affine=False):
    base=prior.source_check(True)
    parameters=base['positive_parameters']+['code_B','code_C']
    auxiliaries=base['positive_auxiliaries']
    fixed=['input_scale','input_offset'] if affine else []
    z={name:sp.Symbol(name) for name in parameters+auxiliaries+fixed}
    fields=['F0','F1','F2','F3','code_B','code_C']
    pack=[];acc=fields[-1]
    for j in range(4,-1,-1):
        mul=f'ac_mul{j}';add=f'ac_add{j}'
        pack += [(mul,'*','q',acc),(add,'+',fields[j],mul)];acc=add
    fifo=[]
    for row in prior.FIFO:
        if affine and row[0]=='bt_initial':
            fifo += [('ac_input_scaled','*','input_scale','x'),('bt_initial','+','ac_input_scaled','input_offset')]
        else:fifo.append(row)
    filter_rows=[('ac_E','+','code_B','code_C'),('ac_eight_E','*',8,'ac_E'),
                 ('ac_q','+','ac_eight_E',1),('ac_append','*',7,'code_B')]
    schedule=pack+prior.CORE+prior.BOUNDS+fifo+filter_rows
    polynomials=prior.independent_sources(z,True)
    polynomials[0]=z['r']-sum(z[name]*z['q']**j for j,name in enumerate(fields))
    if affine:
        I=z['input_scale']*z['x']+z['input_offset']
        polynomials[13]=z['F2']+z['F3']-I-z['W']*(z['F0']+z['F1'])
        polynomials[14]=I+z['width_beta']-z['W']
    equalities=[('r','ac_add0')]+prior.prior.kernel.EQUALITIES[1:]
    equalities += [('bt_X_bound','wn2'),('bt_joint_bound','q'),('bt_read','bt_transport'),
                   ('bt_width','W'),('bt_divisor','q'),('q','ac_q'),('bt_append','ac_append')]
    polynomials += [z['q']-8*(z['code_B']+z['code_C'])-1,
                    z['F0']+z['F1']-7*z['code_B']]
    if endpoint is not None:
        assert endpoint in (0,7)
        schedule += [('ac_two_B','*',2,'code_B'),('ac_eight_F3','*',8,'F3'),
                     ('ac_controller_left','+','ac_two_B','ac_eight_F3'),
                     ('ac_four_F2','*',4,'F2'),('ac_controller_right','+','F0','ac_four_F2')]
        rhs='ac_controller_right'
        if endpoint==7:
            schedule += [('ac_controller_end','+',rhs,'q')];rhs='ac_controller_end'
        equalities += [('ac_controller_left',rhs)]
        polynomials += [2*z['code_B']+8*z['F3']-z['F0']-4*z['F2']-(z['q'] if endpoint==7 else 0)]
    env=prior.prior.execute(schedule,dict(z,n2=z['q']))
    u=2*z['r']+1+z['j']*z['c'];correction=polynomials[8]*(u*u-z['y_aux']**2)
    records=[]
    for ix,((left,right),poly) in enumerate(zip(equalities,polynomials)):
        adjust=correction if ix==9 else 0
        assert sp.expand(env[left]-env[right]-poly-adjust)==0,ix
        records.append(dict(equality=[left,right],source=str(sp.expand(poly)),correction=str(sp.expand(adjust))))
    total=68+(0 if endpoint is None else 5+(endpoint==7))+affine
    count=Counter(row[1] for row in schedule)
    assert len(schedule)==total and count['*']==35+(3 if endpoint is not None else 0)
    assert len(equalities)==18+(endpoint is not None)
    assert set().union(*(p.free_symbols for p in polynomials))==set(z.values())
    return dict(operations=total,multiplications=count['*'],additions_subtractions=count['+']+count['-'],
                equations=len(equalities),positive_existentials_excluding_x=29,
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,fixed_integer_numerals=fixed,
                instructions=[list(row) for row in schedule],sources=records,terminal_carry=endpoint,
                scope='Exact append-code FIFO and entire affine controller, not a universal compiler')


def rail_pairs(word):
    lo,hi=word%3,word//3
    return tuple((a+3*c,b+3*d) for (a,b),(c,d) in product(SPLITS[lo],SPLITS[hi]))


def block_edges(carry):
    rows=[]
    for read,append in product(range(9),(0,7)):
        for rd,ap in product(rail_pairs(read),rail_pairs(append)):
            numerator=carry+sum(c*v for c,v in zip(WEIGHTS,ap+rd))
            if numerator%9:continue
            target=numerator//9
            micro=carry
            for j in range(2):
                digit=tuple(v//3**j%3 for v in ap+rd)
                n=micro+sum(c*v for c,v in zip(WEIGHTS,digit))
                assert n%3==0;micro=n//3
            assert micro==target and target in BOUNDARY
            rows.append(dict(source=carry,target=target,read=read,append=append,read_rails=list(rd),append_rails=list(ap)))
    return rows


def block_graph():
    edges=[row for carry in BOUNDARY for row in block_edges(carry)]
    assert len(edges)==31
    reached={0};changed=True
    while changed:
        new=reached|{row['target'] for row in edges if row['source'] in reached}
        changed=new!=reached;reached=new
    assert reached==set(BOUNDARY)
    table={(k,d):frozenset(row['target'] for row in edges if row['source']==k and row['read']==d)
           for k,d in product(BOUNDARY,range(9))}
    start=frozenset([0]);prefix={start:()};pending=deque([start])
    while pending:
        subset=pending.popleft()
        for d in range(9):
            nxt=frozenset(k for old in subset for k in table[old,d])
            if nxt not in prefix:prefix[nxt]=prefix[subset]+(d,);pending.append(nxt)
    assert len(prefix)==7
    subsets=[]
    for subset,word in prefix.items():
        if not subset:continue
        forbidden=[d for d in range(9) if not any(table[k,d] for k in subset)]
        assert forbidden
        subsets.append(dict(carries=sorted(subset),witness_prefix=list(word),forbidden_next=forbidden[0]))
    # Complete interval proof at block boundaries, using scaled carry k=7s.
    intervals=0
    for s in range(-2,4):
        for r0,r1,z in product((0,1,3,4),(0,1,3,4),(0,1,2)):
            numerator=s-4*r0+8*r1-z
            if numerator%9==0:assert -2<=numerator//9<=3
            intervals+=1
    return dict(edges=edges,reachable_carries=sorted(reached),subsets=subsets,
                complete_scaled_interval_cases=intervals),table


def prefix_subset(value,length,table):
    subset=frozenset([0])
    for _ in range(length):
        d=value%9;value//=9
        subset=frozenset(k for old in subset for k in table[old,d])
    return subset


def affine_rejection(scale,offset,table):
    assert scale>0
    x0=max(1,1-offset);I0=scale*x0+offset
    n=1
    while gcd(scale,9**(n+1))!=gcd(scale,9**n):n+=1
    base=9**n;common=gcd(scale,base);step=base//common
    subset=prefix_subset(I0,n,table)
    if not subset:
        x=x0+step*9*(base+abs(offset)+1)
        assert prefix_subset(scale*x+offset,n,table)==frozenset()
        return dict(scale=scale,offset=offset,x=x,prefix_length=n,initial_rejection=True)
    forbidden=next(d for d in range(9) if not any(table[k,d] for k in subset))
    increment=(scale//common)%9
    assert gcd(increment,9)==1
    shift=((forbidden-I0//base)*pow(increment,-1,9))%9
    x=x0+step*shift
    while scale*x+offset<9**(n+1):x+=step*9
    I=scale*x+offset
    assert I%base==I0%base and I//base%9==forbidden
    assert prefix_subset(I,n+1,table)==frozenset()
    return dict(scale=scale,offset=offset,x=x,input_word=I,prefix_length=n,
                prefix_carries=sorted(subset),forbidden_next=forbidden,initial_rejection=False)


def filter_checks():
    count=admitted=0
    for t in range(1,8):
        q=3**t;words=[sum(bit*3**j for j,bit in enumerate(bits)) for bits in product((0,1),repeat=t)]
        for B,C in product(words[1:],repeat=2):
            arithmetic=q==8*(B+C)+1
            semantic=(t%2==0 and B+C==(q-1)//8 and all((B//3**j%3+C//3**j%3)==(j%2==0) for j in range(t)))
            assert arithmetic==semantic
            if arithmetic:
                app=7*B
                assert app<q
                assert all((app//3**j%9) in (0,7) for j in range(0,t,2))
                admitted+=1
            count+=1
    return dict(positive_boolean_helper_pairs=count,admitted_partitions=admitted)


def positive_C_fixture():
    labels=[(1,0,1,0),(1,1,1,0),(0,0,0,1),(0,0,1,1),
            (1,0,0,0),(1,1,0,0),(1,0,0,1),(1,1,1,1),
            (0,1,1,0),(1,1,1,1),(0,0,1,0),(0,0,1,1)]
    x=2;W=9;t=len(labels);q=3**t
    fields=[sum(bits[i]*3**j for j,bits in enumerate(labels)) for i in range(4)]
    A=sum(fields[:2]);D=sum(fields[2:]);B=A//7;C=(q-1)//8-B
    N=2*x;carry=0
    for bits in labels:
        assert N%3==sum(bits[2:])
        N=N//3+(W//3)*sum(bits[:2])
        numerator=carry+sum(w*b for w,b in zip(WEIGHTS,bits))
        assert numerator%3==0;carry=numerator//3
    assert N==0 and carry==7
    assert min(fields+[B,C])>0 and all(prior.native_boolean(v,t) for v in fields+[B,C])
    r=prior.pack(fields+[B,C],q)
    assert r%2==0 and prior.prior.valuation(r)==0 and D==2*x+W*A and A+D<q
    assert 8*(B+C)+1==q and A==7*B and 2*B+8*fields[3]==fields[0]+4*fields[2]+q
    return dict(x=x,W=W,q=q,fields=fields,code_B=B,code_C=C,r=str(r),
                alpha=q-A-D,width_beta=W-2*x,L=q//W,labels=[list(v) for v in labels],
                kernel_extension='Full positive modified-kernel map; no enormous auxiliary tuple materialized')


def verify():
    graph,table=block_graph()
    rejections=[affine_rejection(c,d,table) for c in range(1,41) for d in range(-5,16)]
    assert -140 not in BOUNDARY and -56 not in BOUNDARY and -28 not in BOUNDARY
    return dict(status='PASS_PAID_APPEND_CODE_AND_AFFINE_INPUT_OBSTRUCTION',
                source68=source_check(),source73_empty=source_check(0),source74_C=source_check(7),
                source75_affine_C=source_check(7,True),filter=filter_checks(),raw_block_graph=graph,
                affine_input_checks=dict(programs=len(rejections),examples=[rejections[0],rejections[11],rejections[-1]]),
                positive_C_fixture=positive_C_fixture(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
                scope='Exact paid append filter; endpoint0 empty; endpoint7 nonempty but no positive affine input map gives all ordinary inputs',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(dict(status=result['status'],operations=[result[k]['operations'] for k in ('source68','source73_empty','source74_C','source75_affine_C')],
                         helper_checks=result['filter'],raw_block_edges=len(result['raw_block_graph']['edges']),
                         affine_programs=result['affine_input_checks']['programs'],scope=result['scope']),indent=2))
