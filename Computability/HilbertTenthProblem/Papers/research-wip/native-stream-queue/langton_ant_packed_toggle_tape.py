"""Chronological binary toggles with one mixed-scale prescribed AND.

The source certifies supplied packed histories at arbitrary positive duration.
Planar ant movement, turning, periodic input loading and a halt query are absent.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import native_binary_masked_selection63 as native
from wang_b_packed_tape import Gates

PARAMETERS = ['initial_tape_hat', 'final_tape_hat']
OUTER_AUX = ['height_slack', 'global_bound', 'J', 'T_hat', 'G_hat', 'C_hat']


def build():
    g=Gates();o=g.emit
    D=g.sum(['initial_tape_hat','final_tape_hat','height_slack'],'height')
    B=o('*',4,D,'radix');Bm1=o('-',B,1,'radix_minus_one')
    v={key:o('-',key+'_hat',1,'unhat_'+key) for key in ('T','G','C')}
    Pm1=o('*',Bm1,'J','scale_minus_one');P=o('+',Pm1,1,'scale')
    H=o('+',v['G'],'J','heads')
    Dm1=o('-',D,1,'height_minus_one');rm=o('*',Dm1,'J','range_mask')
    bound=g.sum(['J','T_hat','G_hat','C_hat','global_bound'],'bound_sum')
    following=o('-',o('+',v['T'],H,'tape_plus_head'),
                    o('+',v['C'],v['C'],'twice_reads'),'next_tapes')
    left=o('+',o('*',B,following,'shift_next'),'initial_tape_hat','transport_left')
    final=o('*',P,'final_tape_hat','terminal')
    right=o('-',o('+',v['T'],final,'transport_sum'),Pm1,'transport_right')
    # All four lane coefficients are <P at zeros. The positive factor B
    # in the prescribed scale types B without reserved radix-test lanes.
    ah=g.pack([H,v['T'],v['T'],v['G']],P,'input_H')
    am=g.pack([v['G'],H,rm,rm],P,'input_M')
    az=g.pack([0,v['C'],v['T'],v['G']],P,'output_Z')
    P2=o('*',P,P,'P2');P4=o('*',P2,P2,'P4');scale=o('*',B,P4,'native_scale')
    ns,np,_=native.source('and64_prescribed')
    assert ns[:7]==[('q','*',16,'P'),('scaled_A','*',16,'Hhat'),('padded_A','-','scaled_A',4),
                   ('scaled_B','*',16,'Mhat'),('padded_B','-','scaled_B',6),
                   ('scaled_Z','*',16,'Zhat'),('F3','-','scaled_Z',8)]
    p='native__';name=lambda x:p+x if isinstance(x,str) else x
    source=g.source+[(p+'q','*',16,scale),(p+'scaled_A','*',16,ah),
        (p+'padded_A','+',p+'scaled_A',12),(p+'scaled_B','*',16,am),
        (p+'padded_B','+',p+'scaled_B',10),(p+'scaled_Z','*',16,az),(p+'F3','+',p+'scaled_Z',8)]
    source += [(name(n),op,name(a),name(b)) for n,op,a,b in ns[7:]]
    pairs=[(bound,P),(left,right)]+[(name(a),name(b)) for a,b in np]
    aux=OUTER_AUX+[name(n) for n in native.domains('and64_prescribed')[1]]
    packet=dict(source=source,comparisons=pairs,parameters=PARAMETERS,auxiliaries=aux,
        interfaces=dict(D=D,B=B,Bm1=Bm1,J='J',P=P,H=H,range_mask=rm,
            joined_H=ah,joined_M=am,joined_Z=az,native_scale=scale,global_bound=bound,
            next_tapes=following,transport_left=left,transport_right=right,**v))
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    packet.update(operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
                  equations=len(pairs),witnesses=len(aux))
    names=set(PARAMETERS+aux)
    for n,op,a,b in source:
        assert n not in names and op in ('+','-','*')
        assert all(not isinstance(v,str) or v in names for v in (a,b));names.add(n)
    assert all(not isinstance(v,str) or v in names for pair in pairs for v in pair)
    return packet


def polynomial_source(packet):return native.parent.sos_source(packet['source'],packet['comparisons'])


def degree_bound(packet):
    d={n:1 for n in packet['parameters']+packet['auxiliaries']}
    at=lambda v:d[v] if isinstance(v,str) else 0
    for n,op,a,b in packet['source']:d[n]=at(a)+at(b) if op=='*' else max(at(a),at(b))
    return 2*max(max(at(a),at(b)) for a,b in packet['comparisons'])


def ledger(packet):
    s,out=polynomial_source(packet);c=Counter('M' if op=='*' else 'A' for _,op,_,_ in s)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(s),multiplications=c['M'],additions_subtractions=c['A'],output=out,
                        degree_upper_bound=degree_bound(packet),exact_degree_claimed=False))


def execute(source,values):
    e=dict(values)
    def a(x):return e[x] if isinstance(x,str) else x
    for n,op,x,y in source:
        x,y=a(x),a(y);assert n not in e
        e[n]=x*y if op=='*' else x+y if op=='+' else x-y
    return e


def independent(values):
    T,G,C=(values[k+'_hat']-1 for k in ('T','G','C'))
    D=values['initial_tape_hat']+values['final_tape_hat']+values['height_slack']
    B=4*D;J=values['J'];P=(B-1)*J+1;H=G+J;rm=(D-1)*J
    pack=lambda v:sum(c*P**j for j,c in enumerate(v))
    ah=pack([H,T,T,G]);am=pack([G,H,rm,rm]);az=pack([0,C,T,G])
    bound=J+sum(values[k+'_hat'] for k in ('T','G','C'))+values['global_bound']-P
    transport=B*(T+H-2*C)+values['initial_tape_hat']-(T+P*values['final_tape_hat']-(P-1))
    native_values=dict(P=B*P**4,Hhat=ah+1,Mhat=am+1,Zhat=az+1,
                      **{n:values['native__'+n] for n in native.domains('and64_prescribed')[1]})
    ns,np,_=native.source('and64_prescribed');env=native.parent.execute(ns,native_values)
    residuals=[bound,transport]+[env[a]-env[b] for a,b in np]
    return residuals,(ah,am,az),native_values


def positive_path(initial,heads):
    assert initial>=0 and heads
    tapes=[initial];reads=[]
    for h in heads:
        assert h>0 and h&(h-1)==0
        c=tapes[-1]&h;reads.append(c);tapes.append(tapes[-1]^h)
        assert tapes[-1]==tapes[-2]+h-2*c
    D=1
    while D<=max(tapes+list(heads)+[tapes[0]+tapes[-1]+2]):D*=2
    B=4*D;n=len(heads);P=B**n;J=(P-1)//(B-1)
    pack=lambda xs:sum(x*B**j for j,x in enumerate(xs))
    rows=dict(T=tapes[:-1],G=[h-1 for h in heads],C=reads)
    v={k+'_hat':pack(xs)+1 for k,xs in rows.items()}
    v.update(initial_tape_hat=tapes[0]+1,final_tape_hat=tapes[-1]+1,
             height_slack=D-tapes[0]-tapes[-1]-2,J=J)
    v['global_bound']=P-J-sum(v[k+'_hat'] for k in rows)
    assert all(x>0 for x in v.values())
    assert v['global_bound']>=(D+1)*J-2>0
    v.update({'native__'+n:1 for n in native.domains('and64_prescribed')[1]})
    return v,dict(tapes=tapes,heads=list(heads),reads=reads,duration=n,radix=B)


def endpoint_path(initial,final):
    """All nonnegative endpoint pairs have a positive-length toggle path."""
    difference=initial^final
    heads=[1<<j for j in range(difference.bit_length()) if difference>>j&1]
    if not heads:heads=[1,1]
    values,trace=positive_path(initial,heads)
    assert trace['tapes'][-1]==final
    return values,trace


def ant_trace(cells,steps,head=(0,0),direction=0):
    """Independent physical ant: headings north,east,south,west; 0 turnsR."""
    cells=set(cells);states=[];directions=[(0,1),(1,0),(0,-1),(-1,0)]
    for _ in range(steps):
        states.append((set(cells),head,direction))
        color=int(head in cells)
        if color:cells.remove(head)
        else:cells.add(head)
        direction=(direction+(1 if color==0 else -1))%4
        dx,dy=directions[direction];head=(head[0]+dx,head[1]+dy)
    states.append((set(cells),head,direction))
    return states


def flatten_ant(states):
    """Encode only an already supplied finite visited rectangle, not raw input."""
    points=set().union(*(s for s,h,d in states))|{h for s,h,d in states}
    xmin=min(x for x,y in points);ymin=min(y for x,y in points)
    width=max(x for x,y in points)-xmin+1
    index=lambda q:q[0]-xmin+width*(q[1]-ymin)
    word=lambda cells:sum(1<<index(q) for q in cells)
    heads=[1<<index(h) for cells,h,d in states[:-1]]
    values,trace=positive_path(word(states[0][0]),heads)
    assert trace['tapes']==[word(cells) for cells,h,d in states]
    return values,trace


def verify():
    packet=build();rng=random.Random(161108)
    source,out=polynomial_source(packet)
    identities=signed=0
    for j in range(512):
        pos=j<256
        v={n:rng.randrange(1,6) if pos else rng.randrange(-4,5) for n in PARAMETERS+packet['auxiliaries']}
        e=execute(source,v);rr,words,_=independent(v)
        at=lambda n:e[n] if isinstance(n,str) else n
        assert rr==[at(a)-at(b) for a,b in packet['comparisons']]
        assert e[out]==sum(r*r for r in rr)
        if pos:assert min(words)>=0 and e['native__F3']>=8 and e['native__q']>0
        identities+=1;signed+=not pos
    paths=duration1=revisits=0
    for length in range(1,13):
        for j in range(24):
            heads=[1<<rng.randrange(12) for _ in range(length)]
            if j==0:heads=[1]*length
            v,trace=positive_path(0 if j<3 else rng.randrange(4096),heads)
            e=execute(packet['source'],v);r,words,nv=independent(v)
            assert r[:2]==[0,0] and words[0]&words[1]==words[2]
            assert max(words)<nv['P'] and nv['P']&(nv['P']-1)==0
            paths+=1;duration1+=length==1;revisits+=len(set(heads))<length
    ant_paths=ant_steps=0
    for _ in range(72):
        cells={(x,y) for x in range(-2,3) for y in range(-2,3) if rng.randrange(4)==0}
        states=ant_trace(cells,rng.randrange(1,65),direction=rng.randrange(4))
        v,trace=flatten_ant(states);r,words,nv=independent(v)
        assert r[:2]==[0,0] and words[0]&words[1]==words[2]
        assert max(words)<nv['P']
        ant_paths+=1;ant_steps+=len(states)-1
    endpoints=0
    for a in range(32):
        for b in range(32):
            v,trace=endpoint_path(a,b);r,words,nv=independent(v)
            assert r[:2]==[0,0] and words[0]&words[1]==words[2]
            endpoints+=1
    # Consecutive repeated heads certify a toggle history but cannot be ant motion.
    v,trace=positive_path(0,[1,1]);r,words,nv=independent(v)
    assert trace['tapes']==[0,1,0] and r[:2]==[0,0] and words[0]&words[1]==words[2]
    # For positive scale factors, product dyadic iff every factor is dyadic.
    mixed=0
    dyadic=lambda x:x>0 and x&(x-1)==0
    for B in range(1,40):
        for P in range(1,40):
            for a in (1,2,4,7):
                assert dyadic(B*P**a)==(dyadic(B) and dyadic(P));mixed+=1
    # Row-head positivity needs the range lane; whole-word H&G=0 is insufficient.
    borrows=[]
    for B in (16,32,64,128):
        J=B+1;H=2*B;G=H-J
        assert H&G==0 and H%B==0 and G%B==B-1
        borrows.append(dict(B=B,J=J,H=H,G=G,head_digits=[0,2]))
    assert ledger(packet)['certificate']['operations']==105
    assert ledger(packet)['polynomial']['operations']==158
    return dict(status='PASS_LANGTON_ANT_PACKED_TOGGLE_TAPE',ledger=ledger(packet),
        independent_full_residual_sos_cases=identities,signed_cases=signed,
        genuine_chronological_toggle_paths=paths,duration_one_paths=duration1,revisiting_paths=revisits,
        physical_ant_prefixes=ant_paths,physical_ant_steps=ant_steps,
        all_endpoint_projection_examples=endpoints,mixed_scale_integer_cases=mixed,
        repeated_head_non_ant_fixture=trace,zero_head_borrow_counterexamples=borrows,
        source_sha256=hashlib.sha256(json.dumps(source,sort_keys=True).encode()).hexdigest(),
        example=dict(source=source,comparisons=packet['comparisons'],parameters=PARAMETERS,
                     auxiliaries=packet['auxiliaries'],interfaces=packet['interfaces'],output=out),
        scope='Uniform arbitrary-positive-duration chronological binary toggles with positive one-hot '
              'heads in each row, complete native AND positivity and a mixed scale typing both radices. '
              'Head positions are independent: every nonnegative endpoint pair has such a path. '
              'Planar ant turning/motion, periodic input background and raw-input perturbation loading, '
              'and simulated halting are not included. No universal bound; outer fixtures are not '
              'materialized positive Pell zeros.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['ledger'])
