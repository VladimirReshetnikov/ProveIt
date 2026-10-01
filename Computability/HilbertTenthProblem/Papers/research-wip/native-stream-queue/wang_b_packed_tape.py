"""Uniform chronological Wang tape updates in one prescribed native AND.

Heads may be chosen independently in each row; head motion, instruction
selection and a whole universal Wang-program interface remain external.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import native_binary_masked_selection63 as native

PARAMETERS = ['initial_tape_hat','final_tape_hat']
OUTER_AUX = ['height_slack','global_bound','T_hat','G_hat','C_hat',
             'I_hat','N_hat','W_hat','V_hat']


class Gates:
    def __init__(self):
        self.source=[]
        self.cache={}
    def emit(self,op,a,b,label):
        if op=='+' and (a==0 or b==0):return b if a==0 else a
        if op=='*' and (a==1 or b==1):return b if a==1 else a
        if op=='*' and (a==0 or b==0):return 0
        key=(op,*sorted((a,b),key=repr)) if op in ('+','*') else (op,a,b)
        if key in self.cache:return self.cache[key]
        name=f'{label}_{len(self.source)}'
        self.source.append((name,op,a,b));self.cache[key]=name
        return name
    def pack(self,coefficients,base,label):
        value=coefficients[-1]
        for c in reversed(coefficients[:-1]):
            value=self.emit('*',base,value,label+'_shift')
            value=self.emit('+',c,value,label+'_sum')
        return value
    def sum(self,terms,label):
        value=terms[0]
        for t in terms[1:]:value=self.emit('+',value,t,label)
        return value


def build():
    g=Gates();o=g.emit
    D=g.sum(['initial_tape_hat','final_tape_hat','height_slack'],'height')
    B=o('*',8,D,'radix');Bm1=o('-',B,1,'radix_minus_one')
    v={key:o('-',key+'_hat',1,'unhat_'+key) for key in ('T','G','C','I','W','V')}
    J=o('-',o('+','I_hat','N_hat','selector_total'),2,'repunit')
    Pm1=o('*',Bm1,J,'scale_minus_one');P=o('+',Pm1,1,'scale')
    H=o('+',v['G'],J,'heads')
    mask=o('*',Bm1,v['I'],'mark_mask')
    Dm1=o('-',D,1,'height_minus_one');rm=o('*',Dm1,J,'range_mask')
    bound=g.sum([J,'T_hat','G_hat','C_hat','I_hat','W_hat','V_hat','global_bound'],'bound_sum')
    following=o('-',o('+',v['T'],v['W'],'marked_tapes'),v['V'],'next_tapes')
    left=o('+',o('*',B,following,'shift_next'),'initial_tape_hat','transport_left')
    final=o('*',P,'final_tape_hat','terminal')
    right=o('-',o('+',v['T'],final,'transport_sum'),Pm1,'transport_right')
    # Seven scalar lanes plus two reserved top lanes for B<=P.
    ah=g.pack([H,v['T'],H,v['C'],v['I'],v['T'],v['G'],B],P,'input_H')
    am=g.pack([v['G'],H,mask,mask,J,rm,rm,Bm1],P,'input_M')
    az=g.pack([0,v['C'],v['W'],v['V'],v['I'],v['T'],v['G']],P,'output_Z')
    P2=o('*',P,P,'P2');P4=o('*',P2,P2,'P4');P8=o('*',P4,P4,'P8');scale=o('*',P8,P,'P9')
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
        interfaces=dict(D=D,B=B,Bm1=Bm1,J=J,P=P,H=H,mark_mask=mask,range_mask=rm,
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
    T,G,C,I,W,V=(values[k+'_hat']-1 for k in ('T','G','C','I','W','V'))
    D=values['initial_tape_hat']+values['final_tape_hat']+values['height_slack']
    B=8*D;J=values['I_hat']+values['N_hat']-2;P=(B-1)*J+1;H=G+J
    mask=(B-1)*I;rm=(D-1)*J
    pack=lambda v:sum(c*P**j for j,c in enumerate(v))
    ah=pack([H,T,H,C,I,T,G,B]);am=pack([G,H,mask,mask,J,rm,rm,B-1]);az=pack([0,C,W,V,I,T,G])
    bound=J+sum(values[k+'_hat'] for k in ('T','G','C','I','W','V'))+values['global_bound']-P
    transport=B*(T+W-V)+values['initial_tape_hat']-(T+P*values['final_tape_hat']-(P-1))
    native_values=dict(P=P**9,Hhat=ah+1,Mhat=am+1,Zhat=az+1,
                      **{n:values['native__'+n] for n in native.domains('and64_prescribed')[1]})
    ns,np,_=native.source('and64_prescribed');env=native.parent.execute(ns,native_values)
    residuals=[bound,transport]+[env[a]-env[b] for a,b in np]
    return residuals,(ah,am,az),native_values


def positive_path(initial,heads,marks):
    assert initial>=0 and len(heads)==len(marks)>0
    tapes=[initial];reads=[];writes=[];selected_reads=[]
    for h,mark in zip(heads,marks):
        assert h>0 and h&(h-1)==0 and mark in (0,1)
        c=tapes[-1]&h;reads.append(c);writes.append(mark*h);selected_reads.append(mark*c)
        tapes.append(tapes[-1]+mark*(h-c))
    D=1
    while D<=max(tapes+list(heads)+[tapes[0]+tapes[-1]+2]):D*=2
    B=8*D;n=len(heads);P=B**n;J=(P-1)//(B-1)
    pack=lambda xs:sum(x*B**j for j,x in enumerate(xs))
    rows=dict(T=tapes[:-1],G=[h-1 for h in heads],C=reads,I=marks,W=writes,V=selected_reads)
    v={k+'_hat':pack(xs)+1 for k,xs in rows.items()}
    v.update(initial_tape_hat=tapes[0]+1,final_tape_hat=tapes[-1]+1,
             height_slack=D-tapes[0]-tapes[-1]-2,N_hat=pack([1-m for m in marks])+1)
    v['global_bound']=P-J-sum(v[k+'_hat'] for k in rows)
    assert all(x>0 for x in v.values())
    assert v['global_bound']>=(3*D+1)*J-5>0
    v.update({'native__'+n:1 for n in native.domains('and64_prescribed')[1]})
    return v,dict(tapes=tapes,heads=list(heads),marks=list(marks),duration=n,radix=B)


def verify():
    packet=build();rng=random.Random(124193)
    identities=signed=0
    for j in range(384):
        pos=j<192
        v={n:rng.randrange(1,6) if pos else rng.randrange(-4,5) for n in PARAMETERS+packet['auxiliaries']}
        s,out=polynomial_source(packet);e=execute(s,v)
        rr,words,_=independent(v)
        at=lambda n:e[n] if isinstance(n,str) else n
        assert rr==[at(a)-at(b) for a,b in packet['comparisons']]
        assert e[out]==sum(r*r for r in rr)
        if pos:
            assert min(words)>=0 and e['native__F3']>=8 and e['native__q']>=16
        identities+=1;signed+=not pos
    paths=all_zero=all_marks=0
    for length in range(1,10):
        for j in range(24):
            heads=[1<<rng.randrange(9) for _ in range(length)]
            marks=[0 if j==0 else 1 if j==1 else rng.randrange(2) for _ in range(length)]
            values,trace=positive_path(0 if j<3 else rng.randrange(512),heads,marks)
            e=execute(packet['source'],values);r,words,_=independent(values)
            assert r[:2]==[0,0]
            assert words[0]&words[1]==words[2]
            assert max(words)<e[packet['interfaces']['native_scale']]
            paths+=1;all_zero+=not any(marks);all_marks+=all(marks)
    # Wrong chronological tape updates cannot pass the transported digit equation.
    transports=0
    for B in (16,32,64):
        for n in range(1,7):
            for _ in range(32):
                current=[rng.randrange(B//4) for _ in range(n)]
                following=[rng.randrange(B//4) for _ in range(n)]
                initial=rng.randrange(B//4);final=rng.randrange(B//4)
                T=sum(a*B**j for j,a in enumerate(current));U=sum(a*B**j for j,a in enumerate(following))
                assert (B*U+initial==T+B**n*final)==(initial==current[0] and following[:-1]==current[1:] and following[-1]==final)
                transports+=1
    # Positive whole-head words alone do not exclude zero head cells.
    borrows=[]
    for b in range(3,11):
        B=1<<b;J=B+1;H=2*B;G=H-J
        assert 0<J<H<B*B and H&G==0 and H%B==0
        assert G==B-1
        borrows.append(dict(B=B,J=J,H=H,G=G,head_digits=[0,2]))
    source,out=polynomial_source(packet)
    return dict(status='PASS_WANG_B_PACKED_TAPE',ledger=ledger(packet),
        independent_full_residual_sos_cases=identities,signed_cases=signed,
        genuine_chronological_outer_paths=paths,all_read_only_paths=all_zero,all_mark_paths=all_marks,
        independent_transport_cases=transports,zero_head_borrow_counterexamples=borrows,
        source_sha256=hashlib.sha256(json.dumps(source,sort_keys=True).encode()).hexdigest(),
        example=dict(source=source,comparisons=packet['comparisons'],parameters=PARAMETERS,
                     auxiliaries=packet['auxiliaries'],interfaces=packet['interfaces'],output=out),
        scope='Complete arbitrary-positive-duration batch relation for chronological finite '
              'non-erasing tape updates with independently chosen one-hot heads and Boolean '
              'mark selectors. One shared native AND certifies all rows. Head motion, finite '
              'instruction control, TM input coding and a whole universal Wang history are '
              'not included. Finite outer fixtures are not numerical full Pell zeros.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['ledger'])
