"""Explicit Neary--Woods tables with a paid equal-block ordinary-input bridge.

The supplied program coordinates are prefix code, suffix scale and suffix value.
Only suitable fixed slices represent a particular r.e. set; arbitrary program
coordinates are not asserted to describe a well-formed machine simulation.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
from functools import lru_cache

import gpcp_complete_fixed_program as raw
import gpcp_complete_fixed_program_units as units
import gpcp_slope_class_compiler as slope

boundary = raw.boundary
history = raw.history
execute = raw.execute
scalar = raw.scalar
PRIMARY = 'https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf'

# Direct Table 16 and Table 4 transcription. Each token is write/move/state.
# The original blank is c. '-' is a missing instruction, hence halting.
TABLES = {
    '15,2': {
        'c': 'cR2 bR3 cL7 cL6 bR1 bL4 cL8 bL9 cR1 bL11 cR12 cR13 cL2 cL3 cR14',
        'b': 'bR1 bR1 cL5 bL5 bL4 bL4 bL7 bL7 bL10 - bR14 bR12 bR12 cR15 bR14'},
    '9,3': {
        'c': 'bR1 cL3 cL3 bL9 cR6 bL4 dL4 cR7 bL5',
        'b': 'cL2 cL2 bL4 bL4 - bR6 bR7 cR9 cR8',
        'd': 'dR3 dL2 dR1 dL4 dL8 dR6 dR7 dR8 cR1'}}


def transition_table(machine='15,2', accepting=False):
    result = {}
    for read, row in TABLES[machine].items():
        for state, token in enumerate(row.split(), 1):
            if token == '-':
                if accepting: result[f'u{state}', read] = ('halt', read, 'S')
            else: result[f'u{state}', read] = (f'u{token[2:]}', token[0], token[1])
    return result


def compiler_table(machine='15,2',*,state_copies=False):
    rename = lambda x: '_' if x == 'c' else x
    table = {(s, rename(c)): (t, rename(a), direction)
             for (s,c),(t,a,direction) in transition_table(machine, True).items()}
    states = int(machine.split(',')[0])
    tape = tuple(rename(c) for c in TABLES[machine])
    alphabet = tape + ('[',']','#') + tuple(f'u{i}' for i in range(1,states+1)) + ('halt',)
    width = max(4, (len(alphabet)-1).bit_length())
    codes = {a:i for i,a in enumerate(alphabet)}
    rules = boundary.rewriting_rules(tape, table, 'halt')
    copy_alphabet = alphabet if state_copies else tape+('[',']','#')
    tiles = boundary.tiles_for(copy_alphabet, rules)
    numeric = tuple(tuple(tuple(codes[a] for a in word) for word in tile) for tile in tiles)
    return dict(transitions=table,tape=tape,alphabet=alphabet,codes=codes,rules=rules,
                tiles=tiles,numeric=numeric,symbol_width=width,copy_alphabet=copy_alphabet,
                state_copies=state_copies)


def a_code(i, machine='15,2'):
    assert i >= 1
    return 'cb'*(8*i-5)+'bb' if machine=='15,2' else 'b'*(4*i-1)+'d'


def bit_blocks(machine='15,2'):
    # Swapping the pairs keeps the fixed numeric difference positive.
    return (a_code(2,machine)+a_code(1,machine),
            a_code(1,machine)+a_code(2,machine))


def bts_program(q,h,productions,machine='15,2'):
    """Tables 2--3 and Equation (4); production outputs are (A..., E).

    Keys are (j,i) for e_j a_i, 1<=j<h and 1<=i<=q.
    Passive a_i -> a_i productions are automatic.
    """
    assert q>=1 and h>=2 and set(productions)=={(j,i) for j in range(1,h) for i in range(1,q+1)}
    def encoded(output):
        *aa,m=output
        assert len(aa) in (1,2) and all(1<=a<=q for a in aa) and 1<=m<=h
        if machine=='15,2':
            symbol = 'cc'*(8*h*q+3) if m==h else 'cc'*(8*m*q)
            if len(aa)==1:
                head = 'cb'*3+'cccb'*2 if m==h else 'cb'*5
                return head+symbol+'cccb'*2+'cc'*(8*aa[0]-5)
            head = 'cb'+'cccb'*2 if m==h else 'cb'*3
            return head+symbol+'cccb'*2+'cc'*(8*aa[1]-5)+'cccb'*2+'cc'*(8*aa[0]-5)
        if len(aa)==1:return 'dccdd'+'c'*(8*m*q+2)+'d'+'c'*(8*aa[0])
        return 'dd'+'c'*(8*m*q+2)+'d'+'c'*(8*aa[1])+'d'+'c'*(8*aa[0])
    sep = 'cb' if machine=='15,2' else 'dcc'
    prefix = 'bbcccb' if machine=='15,2' else 'bccbc'
    active = [encoded(productions[j,i]) for j in range(h-1,0,-1) for i in range(q,0,-1)]
    passive = [('cb'*4+'cccb'*2+'cc'*(8*i-5) if machine=='15,2'
                else 'ddccd'+'c'*(8*i)) for i in range(q,0,-1)]
    return prefix+sep.join(active)+sep*2+(sep*2).join(passive)+sep*3


def encoded_configuration(q,h,productions,data,machine='15,2'):
    """data is a list of ('a',i)/('e',j), with exactly one e marker."""
    assert sum(kind=='e' for kind,_ in data)==1
    program=bts_program(q,h,productions,machine)
    encoded=''
    for kind,i in data:
        if kind=='a':encoded+=a_code(i,machine)
        else:
            assert kind=='e' and 1<=i<=h
            encoded+=('cb'*(8*h*q+3)+'bb' if i==h else 'cb'*(8*i*q)) if machine=='15,2' else 'b'*(4*i*q)
    if machine=='15,2':
        contents=program+'bc'+encoded;head=len(program)+1
    else:contents=program+encoded;head=len(program)
    return contents,head


def simulate(contents,head,machine='15,2',limit=2000000):
    tape={i:c for i,c in enumerate(contents) if c!='c'};state='u1'
    table=transition_table(machine)
    for step in range(limit+1):
        read=tape.get(head,'c');instruction=table.get((state,read))
        if instruction is None:return dict(steps=step,state=state,read=read,halted=True)
        if machine=='9,3' and state=='u1' and read=='c' and head>max(tape,default=head-1):
            assert instruction==('u1','b','R')
            return dict(steps=step,state=state,read=read,halted=False,proved_right_escape=True)
        if step==limit:break
        state,write,direction=instruction
        if write=='c':tape.pop(head,None)
        else:tape[head]=write
        head+=1 if direction=='R' else -1
    return dict(steps=limit,state=state,read=tape.get(head,'c'),halted=False)


def program_parameters(q,h,productions,right_index,left_index,machine='15,2'):
    """Valid per-program slice for initial BTS e1 pair(bits) a_right a_left."""
    assert q>=2 and 1<=right_index<=q and 1<=left_index<=q
    info=compiler_table(machine);d=info['symbol_width'];codes=info['codes']
    physical=lambda w:tuple('_' if a=='c' else a for a in w)
    program=physical(bts_program(q,h,productions,machine))
    if machine=='15,2':prefix=('[',)+program+('b','u1','_')+physical('cb'*(8*q))
    else:prefix=('[',)+program+('u1',)+physical('b'*(4*q))
    suffix=physical(a_code(right_index,machine)+a_code(left_index,machine))+(']','#')
    numeric=lambda w:tuple(codes[a] for a in w)
    values=dict(program_prefix=boundary.code(numeric(prefix),d),
                program_suffix_scale=1<<(d*len(suffix)),
                program_suffix_value=boundary.value(numeric(suffix),d))
    assert all(v>0 for v in values.values())
    return values,prefix,suffix


@lru_cache(None)
def chosen_history(machine,state_copies):
    info=compiler_table(machine,state_copies=state_copies)
    maps=history.maps_from_tiles(info['numeric'],info['symbol_width'])
    return slope.choose_history(maps)


def build(machine='15,2',*,layout='auto',inline_initial=True,optimized=True,state_copies=False):
    info=compiler_table(machine,state_copies=state_copies);d=info['symbol_width'];codes=info['codes']
    b0,b1=bit_blocks(machine)
    encode=lambda w:boundary.value(tuple(codes['_' if a=='c' else a] for a in w),d)
    assert len(b0)==len(b1)
    k=d*len(b0);c0,c1=encode(b0),encode(b1)
    assert 0<c0<c1<(1<<k)
    left=boundary.recoder(k)
    terminal=tuple(codes[a] for a in ('#','[','halt',']'))
    extra=[('input_repunit_scaled','*',(1<<k)-1,'input_repunit'),
           ('input_repunit_power','+','input_repunit_scaled',1),
           ('zero_blocks','*',c0,'input_repunit'),
           ('one_correction','*',c1-c0,'z'),
           ('encoded_body','+','zero_blocks','one_correction'),
           ('framed_prefix','*','program_prefix','Q'),
           ('framed_body','+','framed_prefix','encoded_body'),
           ('framed_scaled','*','program_suffix_scale','framed_body'),
           ('input_bottom','+','framed_scaled','program_suffix_value'),
           ('terminal_scaled','*',1<<(d*len(terminal)),'Ufinal'),
           ('terminal_top','+','terminal_scaled',boundary.value(terminal,d))]
    right=history.build_from_tiles(info['numeric'],d,layout)
    def alias(v):
        if isinstance(v,int):return v
        if v=='Vinitial' and inline_initial:return 'input_bottom'
        return v if v in right['parameters'] else 'hist__'+v
    source=left['source']+extra+[('hist__'+n,op,alias(a),alias(b)) for n,op,a,b in right['source']]
    pairs=left['comparisons']+[('input_repunit_power','Q'),('terminal_top','Vfinal')]
    if not inline_initial:pairs.append(('input_bottom','Vinitial'))
    pairs += [(alias(a),alias(b)) for a,b in right['comparisons']]
    params=['x','program_prefix','program_suffix_scale','program_suffix_value']
    aux=['z']+left['auxiliaries']+['input_repunit','Ufinal','Vfinal']
    if not inline_initial:aux.append('Vinitial')
    aux+=['hist__'+a for a in right['auxiliaries']]
    known=set(params+aux)
    assert len(known)==len(params)+len(aux)
    for n,op,a,b in source:
        assert n not in known and all(isinstance(v,int) or v in known for v in (a,b))
        known.add(n)
    cc=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    old=dict(source=source,comparisons=pairs,parameters=params,auxiliaries=aux,
        operations=len(source),multiplications=cc['M'],additions_subtractions=cc['A'],
        equations=len(pairs),witnesses=len(aux),width=k,tiles=len(info['tiles']),layout=right['layout'],
        inline_initial=inline_initial,program_code=None,loader_operations=0,loaded_input='x',
        history_packet=right,boundary_packet=left,boundary_comparisons=len(pairs)-len(right['comparisons']),
        machine=machine,symbol_width=d,
        block_symbols=len(b0),block_values=[c0,c1],terminal=terminal)
    assert len(pairs)==56-int(inline_initial)
    assert len(aux)==3*len(info['tiles'])+80-int(inline_initial)
    if optimized:old=slope.factored.replace_history(old,chosen_history(machine,state_copies))
    packet=units.rewrite(old)
    packet.update(table=info,optimized=optimized,state_copies=state_copies)
    return packet


def degree_audit(packet):
    """Literal homogeneous upper bounds, with the three exact norm cancellations."""
    degree={n:1 for n in packet['parameters']+packet['auxiliaries']}
    top={n:1+i%3 for i,n in enumerate(degree)}
    for p in packet['native_prefixes']:
        top[p+'tau_gap']=1;top[p+'eta']=top[p+'zeta']=1
    d=lambda v:degree[v] if isinstance(v,str) else 0
    c=lambda v:top[v] if isinstance(v,str) else v
    norms={p+'R15':p for p in packet['native_prefixes']}
    rows={n:(op,a,b) for n,op,a,b in packet['source']}
    for n,op,a,b in packet['source']:
        da,db=d(a),d(b)
        if op=='*':degree[n],top[n]=da+db,c(a)*c(b)
        else:
            degree[n]=max(da,db)
            ca=c(a) if da==degree[n] else 0;cb=c(b) if db==degree[n] else 0
            top[n]=ca+cb if op=='+' else ca-cb
        if n in norms:
            p=norms[n];X=p+'wn2';ac=p+'cam2';G=p+'gam';aa=p+'R12';cc=p+'R10a'
            assert rows[n]==('-',p+'L15',p+'Ac2')
            assert rows[p+'R14']==('+',p+'D1',G) and rows[p+'D1']==('+',X,ac)
            assert rows[ac]==('*',cc,aa) and rows[G]==('*',p+'ga',p+'a4m5')
            assert rows[p+'a4m5']==('+',p+'a4',3) and rows[p+'a4']==('*',4,aa)
            assert rows[p+'A']==('+',p+'a_square',p+'a4m5')
            assert rows[p+'a_square']==('*',aa,aa) and rows[p+'c2']==('*',cc,cc)
            assert rows[p+'Ac2']==('*',p+'A',p+'c2')
            assert rows[p+'L15']==('*',p+'R14',p+'R14')
            highest=d(ac)+d(G)
            assert highest>max(2*d(X),d(X)+d(ac),d(X)+d(G),2*d(G),d(p+'a4m5')+2*d(cc))
            degree[n],top[n]=highest,2*c(ac)*c(G)
    unit=packet['unit_register'];others=[(a,b) for a,b in packet['comparisons'] if (a,b)!=(unit,1)]
    maximum=max(max(d(a),d(b)) for a,b in others)
    leading=sum(((c(a) if d(a)==maximum else 0)-(c(b) if d(b)==maximum else 0))**2
                for a,b in others)
    assert leading and top[unit]
    k=packet['width'];v=k+2;nu=k+3 if packet['inline_initial'] else 2
    dd=packet['history_packet']['scale_exponent']*nu
    expected=14+19*v+20*dd-6*nu+84+8*max(dd,v)
    assert d(unit)+2*maximum==expected
    return dict(exact_degree=expected,unit_degree=d(unit),outer_residual_degree=maximum,
                history_scale_exponent=packet['history_packet']['scale_exponent'],
                length_degree=nu,nonzero_leading_evaluation=True)


def local_rewrite_audit(machine,state_copies):
    info=compiler_table(machine,state_copies=state_copies);rules=info['rules'];alphabet=info['copy_alphabet']
    rng=random.Random(1593);count=0
    for (s,read),(target,write,direction) in info['transitions'].items():
        for case in range(24):
            left=tuple(rng.choice(info['tape']) for _ in range(case%4))
            right=tuple(rng.choice(info['tape']) for _ in range((case//4)%4))
            initial=('[',)+left+(s,read)+right+(']',)
            if direction=='R':
                expected=('[',)+left+(write,target)+(right if right else ('_',))+(']',)
            elif direction=='L':
                expected=(('[',)+left[:-1]+(target,left[-1],write)+right+(']',) if left
                          else ('[',target,'_',write)+right+(']',))
            else:expected=('[',)+left+(target,write)+right+(']',)
            successors=boundary.successors(initial,rules)
            assert len(successors)==1 and successors[0][2]==expected
            selection=boundary.derivation_selection(initial,successors,alphabet,rules)
            top,bottom=boundary.selected_images(info['tiles'],selection)
            assert top==initial and bottom==expected
            count+=1
    for index,(lhs,rhs) in enumerate(rules):
        if 'halt' not in lhs:continue
        for case in range(24):
            left=('[',)+tuple(rng.choice(info['tape']) for _ in range(case%4))
            right=tuple(rng.choice(info['tape']) for _ in range((case//4)%4))+(']',)
            initial=left+lhs+right;target=left+rhs+right
            step=(index,len(left),target)
            selection=boundary.derivation_selection(initial,[step],alphabet,rules)
            assert boundary.selected_images(info['tiles'],selection)==(initial,target)
            count+=1
    return count


def framed_acceptance_audit(machine):
    """Actual accepting table runs and full GPCP words; no huge native witnesses."""
    info=compiler_table(machine);codes=info['codes'];d=info['symbol_width'];b0,b1=bit_blocks(machine)
    haltstate='u10' if machine=='15,2' else 'u5'
    prefix=('[',haltstate,'b');suffix=(']',);target=('[','halt',']')
    records=[]
    for x in (1,2,3):
        bits=bin(x)[2:].zfill(2)
        body=tuple('_' if a=='c' else a for bit in bits for a in (b0 if bit=='0' else b1))
        initial=prefix+body+suffix;word=initial;steps=[]
        while word!=target:
            choices=boundary.successors(word,info['rules']);assert choices
            step=choices[0];steps.append(step);word=step[2]
        selection=boundary.derivation_selection(initial,steps,info['copy_alphabet'],info['rules'])
        top,bottom=boundary.selected_images(info['tiles'],selection)
        assert top+('#',)+target==initial+('#',)+bottom
        Vi=boundary.code(tuple(codes[c] for c in initial+('#',)),d)
        Uf,Vf,_=boundary.dense_append(info['tiles'],selection,codes,d,(1,Vi,1))
        terminal=tuple(codes[c] for c in ('#',)+target)
        assert Vf==(1<<(d*len(terminal)))*Uf+boundary.value(terminal,d)
        records.append(dict(input=x,steps=len(steps),tiles=len(selection),
            initial_bits=Vi.bit_length(),endpoint_bits=Vf.bit_length(),
            universal_program_slice=False,native_Pell_coordinates_materialized=False))
    return records


def verify():
    rng=random.Random(1593160);records=[];example=None;identities=0;frames=0;initializations=0
    table_cases={};simulations=[];boundaries=[];compiled_tables={};acceptance={}
    for machine in TABLES:
        info=compiler_table(machine)
        compiled_tables[machine]=dict(symbol_width=info['symbol_width'],codes=info['codes'],
            copy_alphabet=info['copy_alphabet'],rules=info['rules'],numeric_tiles=info['numeric'],
            adapted_transitions=[(s,c,t,a,direction) for (s,c),(t,a,direction) in info['transitions'].items()])
        table_cases[machine]={str(copies):local_rewrite_audit(machine,copies) for copies in (False,True)}
        acceptance[machine]=framed_acceptance_audit(machine)
        assert len(transition_table(machine))=={'15,2':29,'9,3':26}[machine]
        assert len(info['tiles'])=={'15,2':97,'9,3':117}[machine]
        # Both production arities, passive rotations, and a halt already present.
        for arity in (1,2):
            prod={(1,i):((i,2) if arity==1 else (3-i,i,2)) for i in (1,2)}
            for data in ([('e',1),('a',1),('a',1)], [('a',2),('e',1),('a',2),('a',1)],
                         [('e',2),('a',1)]):
                contents,head=encoded_configuration(2,2,prod,data,machine)
                result=simulate(contents,head,machine)
                assert result['halted'] and (result['state'],result['read'])==(
                    ('u10','b') if machine=='15,2' else ('u5','b'))
                simulations.append(dict(machine=machine,arity=arity,data=data,**result))
        if machine=='9,3':
            prod={(1,i):(i,2) for i in (1,2)}
            contents,head=encoded_configuration(2,2,prod,[('e',1),('a',1)],machine)
            result=simulate(contents,head,machine)
            assert result.get('proved_right_escape')
            boundaries.append(dict(machine=machine,data=[('e',1),('a',1)],**result))
        choices=[(False,True,layout) for layout in ('contiguous','interleaved')]
        choices += [(True,copies,'auto') for copies in (False,True)]
        for optimized,copies,layout in choices:
          for inline in (False,True):
            packet=build(machine,layout=layout,inline_initial=inline,optimized=optimized,state_copies=copies)
            record=units.ledger(packet);record.update(machine=machine,optimized=optimized,
                state_copies=copies,selected_products=packet['history_packet'].get('selected_products',2*packet['tiles']),
                history_operations=packet['history_packet']['operations'],
                **degree_audit(packet))
            poly,out=units.polynomial_source(packet)
            actual=Counter('M' if op=='*' else 'A' for _,op,_,_ in poly)
            assert len(poly)==record['polynomial']['operations']
            assert actual=={'M':record['polynomial']['multiplications'],
                            'A':record['polynomial']['additions_subtractions']}
            records.append(record)
            # The whole-source unit projection audit independently restores all
            # raw residuals, including rational off-zero first-root coordinates.
            for case in range(4):
                values={n:rng.randrange(1,4) if case<3 else rng.randrange(-2,4)
                        for n in packet['parameters']+packet['auxiliaries']}
                units.audit_identity(packet,values);identities+=1
            if machine=='15,2' and optimized and not copies and inline:
                example=dict(source=packet['source'],comparisons=packet['comparisons'],
                    parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
                    polynomial_finalizer=poly[packet['operations']:],polynomial_output=out,
                    ledger=record,history_candidates=packet['history_packet']['history_candidates'])
        d=info['symbol_width'];b0,b1=bit_blocks(machine);k=d*len(b0)
        codeword=lambda w:tuple(info['codes']['_' if c=='c' else c] for c in w)
        c0,c1=(boundary.value(codeword(w),d) for w in (b0,b1))
        for case in range(128):
            n=rng.randrange(2,45);x=rng.randrange(1,1<<n)
            Q=1<<(k*n);R=(Q-1)//((1<<k)-1)
            body=c0*R+(c1-c0)*boundary.spread(x,k)
            digits=bin(x)[2:].zfill(n)
            physical=''.join(b0 if bit=='0' else b1 for bit in digits)
            assert body==boundary.value(codeword(physical),d) and 0<body<Q
            prefix=(info['codes']['['],info['codes']['u1'],1)
            suffix=(info['codes'][']'],info['codes']['#'])
            actual=(boundary.code(prefix,d)*Q+body)*(1<<(d*len(suffix)))+boundary.value(suffix,d)
            assert actual==boundary.code(prefix+codeword(physical)+suffix,d)
            frames+=1
        prod={(1,i):(i,2) for i in range(1,5)}
        params,prefix,suffix=program_parameters(4,2,prod,3,4,machine)
        for x in range(1,32):
          for padding in range(3):
            n=max(2,x.bit_length()+padding);bits=bin(x)[2:].zfill(n)
            aa=[i for bit in bits for i in ((2,1) if bit=='0' else (1,2))]
            data=[('e',1)]+[('a',i) for i in aa]+[('a',3),('a',4)]
            contents,head=encoded_configuration(4,2,prod,data,machine)
            physical=''.join(b0 if bit=='0' else b1 for bit in bits)
            actual=('[',)+tuple('_' if a=='c' else a for a in contents[:head])+('u1',)+tuple(
                '_' if a=='c' else a for a in contents[head:])+(']','#')
            assert actual==prefix+tuple('_' if a=='c' else a for a in physical)+suffix
            Q=1<<(k*n);R=(Q-1)//((1<<k)-1)
            body=c0*R+(c1-c0)*boundary.spread(x,k)
            framed=(params['program_prefix']*Q+body)*params['program_suffix_scale']+params['program_suffix_value']
            assert framed==boundary.code(tuple(info['codes'][a] for a in actual),d)
            initializations+=1
    return dict(primary_source=PRIMARY,published_tables=TABLES,compiled_tables=compiled_tables,
        table_transcription='Table16 and Table4; visual independent transcription',
        source_typo='Table16 halts on u10,b; the final paragraph of section3.5 says u10,c incorrectly.',
        records=records,local_transition_and_tile_audits=table_cases,
        published_encoded_halting_runs=simulations,block_and_framing_cases=frames,
        degenerate_one_A_boundary=boundaries,
        exact_published_initializations=initializations,
        finite_accepting_framed_tile_words=acceptance,
        full_signed_unit_identities=identities,one_complete_source=example,
        scope='Finite tests audit arithmetic and tables; universality uses the published simulation theorem and the pair-input proof in the note.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==json.loads(json.dumps(result))
    print('PASS neary_woods_explicit_universal_tm')
    for record in result['records']:
        print(record['machine'],record['layout'],record['inline_initial'],record['polynomial'],
              'witnesses',record['witnesses'],'degree',record['exact_degree'])


if __name__=='__main__':main()
