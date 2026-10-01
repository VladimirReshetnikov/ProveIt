"""Positive bilinear rows certify every outcome of a fixed finite game DAG.

This is a family of finite-graph circuits, not a fixed-variable universal
polynomial or an ordinary-input compiler for an unbounded game board.
"""
import argparse
from collections import Counter
from itertools import product
import json
from math import comb, lcm
from pathlib import Path
import random


def build(options, target=None, desired=1, divisor=None):
    """Vertices are topologically ordered: all options of v have index <v.

    u_v=1+the P-position bit; w_v is positive, for nonterminals only.
    target/desired optionally require one specified outcome (P=1, N=0).
    """
    options = [list(row) for row in options]
    assert options and desired in (0,1)
    for v,row in enumerate(options):
        assert len(set(row)) == len(row) and all(0 <= j < v for j in row)
    bound = max(2,max(map(len,options)))
    D = lcm(*range(1,bound+1)) if divisor is None else divisor
    assert isinstance(D,int) and D >= 2 and all(D % j == 0 for j in range(1,bound+1))
    source, comparisons, auxiliary = [], [], [f'u{v}' for v in range(len(options))]
    for v,row in enumerate(options):
        if not row:
            comparisons.append((f'u{v}',2))
            continue
        auxiliary.append(f'w{v}')
        total = f'u{row[0]}'
        for k,j in enumerate(row[1:],1):
            nxt = f'v{v}_sum{k}'
            source.append((nxt,'+',total,f'u{j}'))
            total = nxt
        source += [(f'v{v}_S','-',total,len(row)),
                   (f'v{v}_weighted','*',f'v{v}_S',f'w{v}'),
                   (f'v{v}_out','*',D,f'u{v}'),
                   (f'v{v}_lhs','+',f'v{v}_weighted',f'v{v}_out')]
        comparisons.append((f'v{v}_lhs',2*D))
    if target is not None:
        assert 0 <= target < len(options)
        comparisons.append((f'u{target}',desired+1))
    known = set(auxiliary)
    for n,_,a,b in source:
        assert n not in known and all(not isinstance(x,str) or x in known for x in (a,b))
        known.add(n)
    assert all(not isinstance(x,str) or x in known for row in comparisons for x in row)
    return dict(source=source,comparisons=comparisons,auxiliaries=auxiliary,
                options=options,divisor=D,target=target,desired=desired)


def polynomial_source(packet):
    source = list(packet['source'])
    total = None
    for j,(a,b) in enumerate(packet['comparisons']):
        r,s = f'residual{j}',f'square{j}'
        source += [(r,'-',a,b),(s,'*',r,r)]
        if total is None: total=s
        else:
            n=f'total{j}';source.append((n,'+',total,s));total=n
    return source,total


def execute(source,values):
    e=dict(values)
    for n,op,a,b in source:
        x=e[a] if isinstance(a,str) else a
        y=e[b] if isinstance(b,str) else b
        e[n]=x*y if op=='*' else x+y if op=='+' else x-y
    return e


def ledger(packet):
    n=len(packet['options']);h=sum(bool(row) for row in packet['options'])
    edges=sum(map(len,packet['options']));c=n+(packet['target'] is not None)
    source,out=polynomial_source(packet)
    count=lambda rows:dict(Counter('M' if op=='*' else 'A' for _,op,_,_ in rows))
    degrees={name:1 for name in packet['auxiliaries']}
    degree=lambda x:degrees[x] if isinstance(x,str) else 0
    for name,op,a,b in source:
        degrees[name]=degree(a)+degree(b) if op=='*' else max(degree(a),degree(b))
    assert len(packet['source'])==edges+3*h
    assert count(packet['source'])=={k:v for k,v in {'M':2*h,'A':edges+h}.items() if v}
    assert len(source)==edges+3*h+3*c-1
    assert count(source)==dict(M=2*h+c,A=edges+h+2*c-1)
    assert len(packet['auxiliaries'])==n+h and len(packet['comparisons'])==c
    assert degrees[out]==(4 if h else 2)
    return dict(vertices=n,nonterminals=h,edges=edges,divisor=packet['divisor'],
                certificate_operations=len(packet['source']),certificate_split=count(packet['source']),
                comparisons=c,positive_witnesses=n+h,polynomial_operations=len(source),
                polynomial_split=count(source),degree=degrees[out])


def outcomes(options):
    bits=[]
    for row in options:bits.append(int(not any(bits[j] for j in row)))
    return bits


def positive_extension(packet,bits):
    """The unique output projection, with w=1 when its multiplier is zero."""
    assert len(bits)==len(packet['options']) and all(b in (0,1) for b in bits)
    values={f'u{v}':b+1 for v,b in enumerate(bits)}
    for v,row in enumerate(packet['options']):
        if row:
            s=sum(bits[j] for j in row)
            values[f'w{v}']=packet['divisor']//s if s else 1
    return values


def board_graph(moves,weights,radius,defeated=()):
    """Full rank sublevel; a legal subtraction always remains in this set."""
    moves=[tuple(g) for g in moves];weights=tuple(weights);dimension=len(weights)
    assert radius>=0 and dimension and all(isinstance(a,int) and a>0 for a in weights)
    assert len(set(moves))==len(moves)
    rank=lambda p:sum(a*x for a,x in zip(weights,p))
    assert all(len(g)==dimension and rank(g)>0 for g in moves)
    excluded={tuple(p) for p in defeated}
    points=[p for p in product(*(range(radius//a+1) for a in weights))
            if rank(p)<=radius and p not in excluded]
    points.sort(key=lambda p:(rank(p),p))
    index={p:i for i,p in enumerate(points)}
    rows=[]
    for p in points:
        row=[]
        for g in moves:
            q=tuple(x-y for x,y in zip(p,g))
            if min(q)>=0 and q not in excluded:
                assert q in index and rank(q)<rank(p)
                row.append(index[q])
        rows.append(row)
    return points,rows


# Fink, arXiv:1106.1883, Example 2.5, Gamma' on printed p.10.
# This is the non-rational-strategy example, NOT an explicit universal table.
FINK28 = [
    (1,1,0),(5,-2,0),(-1,4,0),(3,-2,0),(-3,4,0),(1,2,0),(2,1,0),
    (0,2,0),(0,4,0),(1,4,0),(2,2,0),(2,4,0),(3,0,0),(3,1,0),
    (3,3,0),(3,5,0),(4,2,0),(4,4,0),
    (-2,1,1),(-1,-1,1),(-1,2,1),(0,3,1),(1,-1,1),(1,4,1),
    (2,0,1),(2,1,1),(3,2,1),(4,3,1),
]


def verify():
    rng=random.Random(20261001)
    identity_cases=degree_cases=0;records=[]
    for k in range(32):
        n=rng.randrange(2,10)
        options=[[j for j in range(v) if rng.randrange(3)==0] for v in range(n)]
        packet=build(options,target=n-1,desired=k%2)
        record=ledger(packet);records.append(record)
        source,out=polynomial_source(packet);D=packet['divisor']
        for j in range(16):
            values={name:rng.randrange(1,9) if j<8 else rng.randrange(-5,6)
                    for name in packet['auxiliaries']}
            e=execute(source,values)
            expected=[]
            for v,row in enumerate(options):
                expected.append((sum(values[f'u{i}']-1 for i in row)*values[f'w{v}']
                                 +D*values[f'u{v}']-2*D) if row else values[f'u{v}']-2)
            expected.append(values[f'u{n-1}']-(packet['desired']+1))
            literal=[(e[a] if isinstance(a,str) else a)-(e[b] if isinstance(b,str) else b)
                     for a,b in packet['comparisons']]
            assert literal==expected and e[out]==sum(r*r for r in expected)
            identity_cases+=1
        offsets={name:rng.randrange(1,8) for name in packet['auxiliaries']}
        ys=[execute(source,{name:t+c for name,c in offsets.items()})[out] for t in range(5)]
        if record['nonterminals']:
            assert sum((-1)**(4-j)*comb(4,j)*ys[j] for j in range(5))==24*sum(len(r)**2 for r in options)
        else:
            assert ys[2]-2*ys[1]+ys[0]==2*record['comparisons']
        degree_cases+=1

    graphs=positive_assignments=wrong_target_checks=0
    for n in range(1,6):
        allowed=[(v,j) for v in range(n) for j in range(v)]
        for mask in range(1<<len(allowed)):
            options=[[] for _ in range(n)]
            for bit,(v,j) in enumerate(allowed):
                if mask>>bit&1:options[v].append(j)
            packet=build(options);D=packet['divisor'];truth=outcomes(options)
            accepted=[]
            for us in product(range(1,4),repeat=n):
                possible=True
                for v,row in enumerate(options):
                    if not row:
                        possible &= us[v]==2
                    else:
                        s=sum(us[j]-1 for j in row);rhs=D*(2-us[v])
                        possible &= (rhs==0 if s==0 else rhs>0 and rhs%s==0)
                    if not possible:break
                assert possible==(us==tuple(b+1 for b in truth))
                if possible:accepted.append(us)
                positive_assignments+=1
            assert len(accepted)==1
            source,out=polynomial_source(packet)
            assert execute(source,positive_extension(packet,truth))[out]==0
            wrong=build(options,target=n-1,desired=1-truth[-1])
            wrongsource,wrongout=polynomial_source(wrong)
            assert execute(wrongsource,positive_extension(wrong,truth))[wrongout]==1
            wrong_target_checks+=1
            graphs+=1

    board_cases=board_vertices=board_edges=0
    board_records=[]
    families=[([(1,0),(0,1)],(1,1)),
              ([(2,-1),(-1,2),(1,1)],(1,1)),
              ([(1,0,0),(0,1,0),(0,0,1),(2,-1,0),(-1,2,0)],(1,1,1))]
    for moves,weights in families:
        for radius in (4,7,10):
            for deleted in ((),(tuple(0 for _ in weights),)):
                points,options=board_graph(moves,weights,radius,deleted)
                truth=outcomes(options);packet=build(options,target=len(points)-1,
                        desired=truth[-1],divisor=lcm(*range(1,max(2,len(moves))+1)))
                source,out=polynomial_source(packet)
                assert execute(source,positive_extension(packet,truth))[out]==0
                # Enlarging the predecessor-closed domain preserves every old outcome.
                bigger,bigoptions=board_graph(moves,weights,radius+3,deleted)
                bigtruth=dict(zip(bigger,outcomes(bigoptions)))
                assert all(bigtruth[p]==b for p,b in zip(points,truth))
                board_vertices+=len(points);board_edges+=sum(map(len,options));board_cases+=1
                board_records.append(ledger(packet))

    assert len(FINK28)==28
    points,options=board_graph(FINK28,(1,1,3),39)
    truth=outcomes(options);position_bits=dict(zip(points,truth));fink_checks=0
    for i in range(7):
        for j in range(7-i):
            assert position_bits[(6*i,6*j,1)]==comb(i+j,i)%2
            fink_checks+=1
    # Complete actual-source positive zero on a smaller closed Fink board.
    small,smallrows=board_graph(FINK28,(1,1,3),12)
    smalltruth=outcomes(smallrows)
    actual=build(smallrows,target=len(small)-1,desired=smalltruth[-1],
                 divisor=lcm(*range(1,29)))
    actualsource,actualout=polynomial_source(actual)
    assert execute(actualsource,positive_extension(actual,smalltruth))[actualout]==0

    # Deleting a legal option makes the true N-position 2 look like P.
    full=[[],[0],[0,1]];selected=[[],[0],[1]]
    assert outcomes(full)==[1,0,0] and outcomes(selected)==[1,0,1]
    selected_packet=build(selected,target=2,desired=1)
    selected_source,selected_out=polynomial_source(selected_packet)
    selected_values=positive_extension(selected_packet,[1,0,1])
    assert execute(selected_source,selected_values)[selected_out]==0
    assert selected_values==dict(u0=2,u1=1,u2=2,w1=2,w2=1)
    # Keeping only vertex1 of the subtraction-by1 game changes N to terminal P.
    assert outcomes([[],[0]])==[1,0] and outcomes([[]])==[1]

    example=build([[],[0],[0,1],[1,2],[2,3]],target=4,desired=0)
    exsource,exout=polynomial_source(example)
    assert execute(exsource,positive_extension(example,outcomes(example['options'])))[exout]==0
    return dict(status='PASS_LATTICE_GAME_POSITIVE_NOR',
                complete_source_identities=identity_cases,signed_identities=identity_cases//2,
                exact_degree_checks=degree_cases,all_ordered_dags_through_five_vertices=graphs,
                positive_output_assignments=positive_assignments,wrong_target_checks=wrong_target_checks,
                closed_board_cases=board_cases,closed_board_vertices=board_vertices,
                closed_board_edges=board_edges,board_ledgers=board_records,
                fink28=dict(primary='https://arxiv.org/pdf/1106.1883',
                            scope='Example2.5 non-rational-strategy game; not a universal table.',
                            moves=FINK28,weights=[1,1,3],radius=39,vertices=len(points),
                            binomial_parity_queries=fink_checks,small_full_source=ledger(actual)),
                missing_option_obstruction=dict(full_options=full,selected_options=selected,
                    full_P_bits=[1,0,0],selected_P_bits=[1,0,1],false_selected_positive_zero=selected_values),
                random_graph_ledgers=records,
                example=dict(ledger=ledger(example),source=exsource,output=exout,
                             comparisons=example['comparisons'],auxiliaries=example['auxiliaries'],
                             options=example['options']),
                scope='Complete fixed finite-graph polynomial family. Graph size, witness count '
                      'and circuit length grow with the board; no uniform unbounded-history '
                      'or ordinary-input universal polynomial is supplied.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['example']['ledger'])
