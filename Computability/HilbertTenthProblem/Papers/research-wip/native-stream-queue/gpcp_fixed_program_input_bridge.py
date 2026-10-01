"""Paid ordinary-input boundary for a fixed generalized PCP program.

The recoder and scalar boundary relation are complete Diophantine sources.
Selected unbounded tile histories are deliberately not claimed certified.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import native_binary_input_dilation130 as parent

execute=parent.execute
raw=parent.parent


def power_chain(width):
    assert isinstance(width,int) and width>=4
    source=[];power=1;name='q'
    for bit in bin(width)[3:]:
        exponent=2*power
        nxt='Q' if exponent==width else f'width_power{exponent}'
        source.append((nxt,'*',name,name));power,name=exponent,nxt
        if bit=='1':
            exponent=power+1
            nxt='Q' if exponent==width else f'width_power{exponent}'
            source.append((nxt,'*',name,'q'));power,name=exponent,nxt
    assert power==width and name=='Q'
    assert len(source)==width.bit_length()+width.bit_count()-2
    return source


def recoder(width):
    old=parent.build();chain=power_chain(width)
    assert old['source'][:3]==[('q2','*','q','q'),('Q','*','q2','q2'),('B','*',8,'Q')]
    assert {n for n,_,a,b in old['source'] if 'q2' in (a,b)}=={'Q'}
    source=chain+[('B','*',1<<(width-1),'Q')]+old['source'][3:]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    return dict(old,source=source,width=width,power_chain_length=len(chain),
                operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'])


def value(word,width):
    result=0
    for digit in word:
        assert 0<=digit<1<<width
        result=(result<<width)+digit
    return result


def code(word,width):return (1<<(width*len(word)))+value(word,width)


def build(width=4,prefix=(3,6),suffix=(4,5),terminal=(5,3,9,4)):
    old=recoder(width)
    assert prefix and suffix and terminal
    # The defaults encode [start, R delimiter, and delimiter [halt R.
    source=old['source']+[
        ('framed_prefix','*',code(prefix,width),'Q'),
        ('framed_body','+','framed_prefix','z'),
        ('framed_scaled','*',1<<(width*len(suffix)),'framed_body'),
        ('input_bottom','+','framed_scaled',value(suffix,width)),
        ('terminal_scaled','*',1<<(width*len(terminal)),'Ufinal'),
        ('terminal_top','+','terminal_scaled',value(terminal,width))]
    pairs=old['comparisons']+[('input_bottom','Vinitial'),('terminal_top','Vfinal')]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==134+len(power_chain(width))
    assert counts=={'M':68+len(power_chain(width)),'A':66}
    return dict(old,source=source,comparisons=pairs,parameters=['x','Vinitial','Ufinal','Vfinal'],
                auxiliaries=['z']+old['auxiliaries'],prefix=list(prefix),suffix=list(suffix),
                terminal=list(terminal),operations=len(source),multiplications=counts['M'],
                additions_subtractions=counts['A'],witnesses=50,equations=36)


def independent(packet,v):
    q,P,J,K,Ahat,z=(v[n] for n in ('q','P','J','K','Ahat','z'))
    Q=q**packet['width'];B=(1<<(packet['width']-1))*Q
    answer=[(B-1)*J+1-P,(2*B-1)*K+1-q*P,v['x']+v['input_slack']-q,
            Ahat+Q-(Q-1)*v['quotient_hat']-z-2,z+v['output_slack']-Q]
    geo=raw.geometry.build(shared_B=True)
    gv={n:v['geo__'+n] for n in geo['auxiliaries']};gv.update(q=q,J=J)
    answer+=raw.geometry.manual(gv,B)
    answer+=raw.independent(v)[18:]
    if 'prefix' in packet:
        answer += [(code(packet['prefix'],packet['width'])*Q+z)*(1<<(packet['width']*len(packet['suffix'])))
                   +value(packet['suffix'],packet['width'])-v['Vinitial'],
                   (1<<(packet['width']*len(packet['terminal'])))*v['Ufinal']
                   +value(packet['terminal'],packet['width'])-v['Vfinal']]
    return answer


def spread(x,width):
    return sum(((x>>j)&1)<<(width*j) for j in range(x.bit_length()))


def outer_fixture(x,n,width):
    q=1<<n;assert n>=2 and 0<x<q and width>=4
    Q=q**width;B=(1<<(width-1))*Q;P=B**n
    J=(P-1)//(B-1);K=(q*P-1)//(2*B-1)
    A=(x*J)&K;z=spread(x,width)
    assert B>=8*q*q and J>B and J&1 and J.bit_count()==n
    assert A==sum(((x>>j)&1)<<(width*(n+1)*j) for j in range(n))
    assert A%(Q-1)==z and 0<z<=(Q-1)//((1<<width)-1)<Q-1
    v=dict(x=x,z=z,q=q,P=P,J=J,K=K,Ahat=A+1,
           quotient_hat=(A-z)//(Q-1)+1,input_slack=q-x,output_slack=Q-z)
    assert all(a>0 for a in v.values())
    return v


def source_checks():
    rng=random.Random(136504);records=[];cases=signed=0;example=None
    for width in (4,5,8,16,24):
        packet=build(width);sos,out=raw.sos_source(packet)
        counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
        assert len(sos)==241+len(power_chain(width))
        assert counts=={'M':104+len(power_chain(width)),'A':137}
        for case in range(96):
            v={n:rng.randrange(1,8) if case<64 else rng.randrange(-3,5)
               for n in packet['parameters']+packet['auxiliaries']}
            env=execute(sos,v);expected=independent(packet,v)
            assert [env[a]-env[b] for a,b in packet['comparisons']]==expected
            assert env[out]==sum(r*r for r in expected)
            cases+=1;signed+=case>=64
        degrees={n:1 for n in packet['parameters']+packet['auxiliaries']}
        for name,op,a,b in packet['source']:
            da=degrees[a] if isinstance(a,str) else 0;db=degrees[b] if isinstance(b,str) else 0
            degrees[name]=da+db if op=='*' else max(da,db)
        assert max(max(degrees[a],degrees[b]) for a,b in packet['comparisons'])==max(20,width+1)
        t=sp.Symbol('t');weights={n:1+i%3 for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
        env=execute(packet['source'],{n:sp.Poly(w*t+i+1,t) for i,(n,w) in enumerate(weights.items())})
        residuals=[env[a]-env[b] for a,b in packet['comparisons']]
        degree=max(p.degree() for p in residuals)
        assert degree==max(20,width+1) and sum(p.LC()**2 for p in residuals if p.degree()==degree)>0
        records.append(dict(width=width,chain_length=len(power_chain(width)),
            recoder_operations=packet['operations']-6,boundary_operations=packet['operations'],
            boundary_M=packet['multiplications'],boundary_A=packet['additions_subtractions'],
            equations=36,witnesses=50,polynomial_operations=len(sos),polynomial_M=counts['M'],
            polynomial_A=counts['A'],exact_degree=2*degree))
        if width==4:example=dict(packet,polynomial_finalizer=sos[packet['operations']:],polynomial_output=out)
    return dict(records=records,source_example=example,complete_source_cases=cases,signed_cases=signed)


def rewriting_rules(tape,transitions,accept):
    assert '_' in tape and not set(tape)&{'[',']','#',accept}
    rules=[]
    for (state,read),(target,write,direction) in sorted(transitions.items()):
        assert read in tape and write in tape and direction in ('L','R','S')
        if direction=='R':
            rules += [((state,read,c),(write,target,c)) for c in tape]
            rules.append(((state,read,']'),(write,target,'_',']')))
        elif direction=='L':
            rules += [((c,state,read),(target,c,write)) for c in tape]
            rules.append((('[',state,read),('[',target,'_',write)))
        else:rules.append(((state,read),(target,write)))
    rules += [((accept,a),(accept,)) for a in tape]
    rules += [((a,accept),(accept,)) for a in tape]
    assert all(a and b and '#' not in a+b for a,b in rules)
    return tuple(rules)


def successors(word,rules):
    return [(i,pos,word[:pos]+right+word[pos+len(left):])
            for i,(left,right) in enumerate(rules)
            for pos in range(len(word)-len(left)+1) if word[pos:pos+len(left)]==left]


def tiles_for(alphabet,rules):
    assert '#' in alphabet
    return tuple((tuple([a]),tuple([a])) for a in alphabet)+tuple(rules)


def selected_images(tiles,selection):
    return tuple(tuple(letter for i in selection for letter in tiles[i][lane]) for lane in (0,1))


def derivation_selection(initial,steps,alphabet,rules):
    copies={a:i for i,a in enumerate(alphabet)};selection=[];word=initial
    if not steps:return [copies[a] for a in word]
    for number,(rule,pos,target) in enumerate(steps):
        if number:selection.append(copies['#'])
        left,right=rules[rule]
        assert word[pos:pos+len(left)]==left
        assert target==word[:pos]+right+word[pos+len(left):]
        selection += [copies[a] for a in word[:pos]]+[len(alphabet)+rule]
        selection += [copies[a] for a in word[pos+len(left):]]
        word=target
    return selection


def dense_append(tiles,selection,codes,width,initial):
    vector=list(initial)
    for i in selection:
        a,b=([codes[c] for c in part] for part in tiles[i])
        matrix=[[1<<(width*len(a)),0,value(a,width)],
                [0,1<<(width*len(b)),value(b,width)],[0,0,1]]
        vector=[sum(matrix[r][j]*vector[j] for j in range(3)) for r in range(3)]
    return vector


def program_checks():
    tape=('0','1','_');alphabet=('0','1','_','[',']','#','start','odd','reject','halt')
    codes={a:i for i,a in enumerate(alphabet)};width=4
    transitions={}
    for state in ('start','odd'):
        transitions[state,'0']=('start','0','R')
        transitions[state,'1']=('odd','1','R')
    transitions['start','_']=('reject','_','S');transitions['odd','_']=('halt','_','S')
    rules=rewriting_rules(tape,transitions,'halt');tiles=tiles_for(alphabet,rules)
    packet=build(width);target=('[','halt',']');cases=accepting=reflexive=0
    for x in range(1,64):
      for padding in range(3):
        n=max(2,x.bit_length()+padding);bits=tuple(bin(x)[2:].zfill(n))
        initial=('[','start')+bits+(']',);word=initial;steps=[]
        for _ in range(3*n+12):
            if word==target:break
            choices=successors(word,rules)
            if not choices:break
            step=choices[0];steps.append(step);word=step[2]
        assert (word==target)==bool(x&1)
        # All runs, accepting or rejecting, give an exact derivation witness
        # when their actual terminal configuration is used as the boundary.
        selection=derivation_selection(initial,steps,alphabet,rules)
        top,bottom=selected_images(tiles,selection)
        assert top+('#',)+word==initial+('#',)+bottom
        loaded=code([codes[c] for c in initial+('#',)],width)
        U,V,one=dense_append(tiles,selection,codes,width,(1,loaded,1))
        assert U==code([codes[c] for c in top],width)
        assert V==code([codes[c] for c in initial+('#',)+bottom],width) and one==1
        assert ((1<<(width*4))*U+value([5,3,9,4],width)==V)==bool(x&1)
        outer=outer_fixture(x,n,width)
        supplied={name:1 for name in packet['parameters']+packet['auxiliaries']}
        supplied.update(outer,Vinitial=loaded,Ufinal=U,Vfinal=V)
        env=execute(packet['source'],supplied)
        assert env['input_bottom']==loaded
        assert [env[a]-env[b] for a,b in packet['comparisons'][:5]]==[0]*5
        assert (env['terminal_top']==V)==bool(x&1)
        cases+=1;accepting+=bool(x&1)
        identity=derivation_selection(initial,[],alphabet,rules)
        a,b=selected_images(tiles,identity)
        assert a+('#',)+initial==initial+('#',)+b;reflexive+=1
    # Left boundary extension, interior left move, and stay move are tested
    # independently of the right-scanning sample recognizer.
    tiny=rewriting_rules(tape,{('q','1'):('p','0','L'),('p','_'):('a','1','S')},'a')
    left=successors(('[','q','1',']'),tiny)
    assert len(left)==1 and left[0][2]==('[','p','_','0',']')
    interior=successors(('[','0','q','1',']'),tiny)
    assert len(interior)==1 and interior[0][2]==('[','p','0','0',']')
    stay=successors(left[0][2],tiny)
    assert len(stay)==1 and stay[0][2]==('[','a','1','0',']')
    return dict(fixed_tiles=len(tiles),rewrite_rules=len(rules),padded_input_runs=cases,
                accepting_runs=accepting,reflexive_boundary_cases=reflexive,
                fixture_language='Positive odd integers; every sufficient zero padding gives the same answer.',
                fixture_scope='Genuine outer recoder, rewriting, selected word and dense matrix checks; native Pell coordinates are placeholders, not full zeros.')


def generic_outer_checks():
    rng=random.Random(4136);cases=0
    for width in (4,5,8,16,24):
      packet=build(width)
      for _ in range(64):
        n=rng.randrange(2,25);x=rng.randrange(1,1<<n);v=outer_fixture(x,n,width)
        digits=[int(c) for c in bin(x)[2:].zfill(n)]
        loaded=code(packet['prefix']+digits+packet['suffix'],width)
        assert loaded==(code(packet['prefix'],width)*v['q']**width+v['z'])*(1<<(width*len(packet['suffix'])))+value(packet['suffix'],width)
        assert spread(x,width)==outer_fixture(x,n+1,width)['z']
        cases+=1
    return dict(genuine_width_and_padding_cases=cases)


def verify():
    return dict(status='PASS_GPCP_FIXED_PROGRAM_INPUT_BRIDGE',source=source_checks(),
                programs=program_checks(),outer=generic_outer_checks(),
                scope='Complete paid recoding and scalar boundary relation; effective fixed-TM to fixed-GPCP input convention. '
                      'The unbounded common tile selection and its matrix history remain an unpaid Diophantine obligation. '
                      'No improvement of the universal75/88 frontier is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
