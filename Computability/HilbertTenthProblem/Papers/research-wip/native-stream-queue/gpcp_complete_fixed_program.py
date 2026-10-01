"""Complete fixed-program GPCP equations with an ordinary integer input.

The input recoder and the selected affine-pair history have independent
geometries.  Numerical sample tables recognize odd integers, not a universal
language.  The universal-interpreter loader has a separate, paid interface.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import gpcp_fixed_program_input_bridge as boundary
import pcp_uniform_affine_pair_history as history

execute = boundary.execute
scalar = history.scalar


def build(tiles, width, prefix, suffix, terminal, *, layout='auto',
          inline_initial=True, program_code=None):
    """Compile numeric tile words and a fixed generalized PCP boundary.

    program_code=None uses x directly.  'parameter' loads code*(2*x+1),
    while a positive integer C loads (2*C)*x+C.  All inputs/witnesses are
    positive integers; each fixed numeral multiplication is charged.
    """
    left = boundary.build(width, prefix, suffix, terminal)
    right = history.build_from_tiles(tiles, width, layout)
    loader = []
    parameters = ['x']
    loaded = 'x'
    if program_code == 'parameter':
        parameters += ['program_code']
        loader = [('loader_twice', '+', 'x', 'x'),
                  ('loader_odd', '+', 'loader_twice', 1),
                  ('loader_input', '*', 'program_code', 'loader_odd')]
        loaded = 'loader_input'
    elif program_code is not None:
        assert isinstance(program_code, int) and program_code > 0
        loader = [('loader_scaled', '*', 2*program_code, 'x'),
                  ('loader_input', '+', 'loader_scaled', program_code)]
        loaded = 'loader_input'
    def left_alias(value): return loaded if value == 'x' else value
    def right_alias(value):
        if isinstance(value, int): return value
        if value == 'Vinitial' and inline_initial: return 'input_bottom'
        if value in right['parameters']: return value
        return 'hist__'+value
    source = loader+[(n, op, left_alias(a), left_alias(b))
                     for n, op, a, b in left['source']]
    source += [('hist__'+n, op, right_alias(a), right_alias(b))
               for n, op, a, b in right['source']]
    left_pairs = [(left_alias(a), left_alias(b)) for a,b in left['comparisons']
                  if not (inline_initial and (a,b) == ('input_bottom','Vinitial'))]
    pairs = left_pairs+[(right_alias(a),right_alias(b)) for a,b in right['comparisons']]
    endpoints = ['Ufinal','Vfinal'] if inline_initial else list(right['parameters'])
    aux = left['auxiliaries']+endpoints+['hist__'+n for n in right['auxiliaries']]
    known = set(parameters+aux)
    assert len(known) == len(parameters)+len(aux)
    for n,op,a,b in source:
        assert op in ('*','+','-') and n not in known
        assert all(not isinstance(v,str) or v in known for v in (a,b))
        known.add(n)
    counts = Counter('M' if op == '*' else 'A' for _,op,_,_ in source)
    assert len(source) == left['operations']+right['operations']+len(loader)
    assert len(pairs) == 55-int(inline_initial)
    assert len(aux) == 3*len(tiles)+79-int(inline_initial)
    return dict(source=source, comparisons=pairs, parameters=parameters, auxiliaries=aux,
                operations=len(source), multiplications=counts['M'],
                additions_subtractions=counts['A'], equations=len(pairs), witnesses=len(aux),
                width=width, tiles=len(tiles), layout=right['layout'],
                inline_initial=inline_initial, program_code=program_code,
                loader_operations=len(loader), loaded_input=loaded,
                boundary_comparisons=len(left_pairs),
                boundary_packet=left, history_packet=right)


def polynomial_source(packet):
    return history.native.parent.sos_source(packet['source'], packet['comparisons'])


def ledger(packet):
    result = {key:packet[key] for key in ('width','tiles','layout','inline_initial',
        'program_code','loader_operations','operations','multiplications',
        'additions_subtractions','equations','witnesses')}
    e = packet['equations']
    result['polynomial'] = dict(operations=packet['operations']+3*e-1,
        multiplications=packet['multiplications']+e,
        additions_subtractions=packet['additions_subtractions']+2*e-1)
    return result


def component_values(packet, values):
    env = execute(packet['source'], values)
    left = {n:values[n] for n in packet['boundary_packet']['parameters']+
            packet['boundary_packet']['auxiliaries'] if n in values}
    left['x'] = scalar(packet['loaded_input'],env)
    left['Vinitial'] = env['input_bottom'] if packet['inline_initial'] else values['Vinitial']
    right = {n:values['hist__'+n] for n in packet['history_packet']['auxiliaries']}
    right.update({n:left[n] for n in packet['history_packet']['parameters']})
    return left,right


def independent(packet, values):
    left,right = component_values(packet,values)
    lr = boundary.independent(packet['boundary_packet'],left)
    if packet['inline_initial']:
        assert lr[-2] == 0
        lr = lr[:-2]+lr[-1:]
    return lr+history.manual(packet['history_packet'],right)[0]


def degree_check(packet):
    """Structural upper degree plus a nonzero leading homogeneous evaluation.

    A zero top evaluation retains the structural upper bound.  Hence no
    cancellation is silently declared impossible.  A nonzero SOS top proves
    attainment without expanding any enormous multivariate polynomial.
    """
    variables = packet['parameters']+packet['auxiliaries']
    degree = {n:1 for n in variables}
    top = {n:1+i%5 for i,n in enumerate(variables)}
    def d(v): return degree[v] if isinstance(v,str) else 0
    def c(v): return top[v] if isinstance(v,str) else v
    for n,op,a,b in packet['source']:
        da,db = d(a),d(b)
        if op == '*': degree[n],top[n] = da+db,c(a)*c(b)
        else:
            degree[n] = max(da,db)
            ca = c(a) if da == degree[n] else 0
            cb = c(b) if db == degree[n] else 0
            top[n] = ca+cb if op == '+' else ca-cb
    upper = max(max(d(a),d(b)) for a,b in packet['comparisons'])
    coefficients = [(c(a) if d(a)==upper else 0)-(c(b) if d(b)==upper else 0)
                    for a,b in packet['comparisons']]
    attained = sum(v*v for v in coefficients)
    assert attained > 0
    N = packet['history_packet']['scale_exponent']
    expected = (12*(packet['width']+1)*N+16 if packet['inline_initial']
                else max(24*N+16, 2*packet['width']+2))
    assert 2*upper == expected
    blob = attained.to_bytes((attained.bit_length()+7)//8,'big')
    return dict(exact_degree=2*upper, scale_exponent=N,
        leading_SOS_positive=True, leading_evaluation_bits=attained.bit_length(),
        leading_evaluation_sha256=hashlib.sha256(blob).hexdigest(),
        attaining_residuals=[i for i,c in enumerate(coefficients) if c])


def build_for_tm(tape, transitions, start, accept, *, width=None, **options):
    """Fixed-table compiler; acceptance must ignore every permitted zero padding."""
    assert len(set(tape)) == len(tape) and {'0','1','_'} <= set(tape)
    states = {start,accept}|{s for s,_ in transitions}|{s for s,_,_ in transitions.values()}
    assert start != accept and not states & (set(tape)|{'[',']','#'})
    assert not set(tape)&{'[',']','#'}
    assert all(state != accept for state,_ in transitions)
    alphabet = ('0','1')+tuple(a for a in tape if a not in ('0','1'))+('[',']','#')+tuple(sorted(states))
    assert len(alphabet) == len(set(alphabet))
    codes = {symbol:i for i,symbol in enumerate(alphabet)}
    minimum = max(4,(len(alphabet)-1).bit_length())
    width = minimum if width is None else width
    assert width >= minimum
    rules = boundary.rewriting_rules(tape,transitions,accept)
    tiles = boundary.tiles_for(alphabet,rules)
    numeric = tuple(tuple(tuple(codes[c] for c in word) for word in tile) for tile in tiles)
    prefix = tuple(codes[c] for c in ('[',start))
    suffix = tuple(codes[c] for c in (']','#'))
    terminal = tuple(codes[c] for c in ('#','[',accept,']'))
    packet = build(numeric,width,prefix,suffix,terminal,**options)
    packet['machine'] = dict(tape=tuple(tape),alphabet=alphabet,codes=codes,
        rules=rules,tiles=tiles,start=start,accept=accept)
    return packet


def odd_machine(**options):
    transitions = {(s,c):(('start' if c=='0' else 'odd'),c,'R')
                   for s in ('start','odd') for c in ('0','1')}
    transitions.update({('start','_'):('reject','_','S'),('odd','_'):('halt','_','S')})
    return build_for_tm(('0','1','_'),transitions,'start','halt',**options)


def program_fixture(packet, x, padding=0, code=1):
    """Genuine outer computation; astronomical native witnesses are placeholders."""
    machine = packet['machine'];width=packet['width']
    pc = packet['program_code']
    loaded = x if pc is None else (code if pc=='parameter' else pc)*(2*x+1)
    n = max(2,loaded.bit_length()+padding)
    initial = ('[',machine['start'])+tuple(bin(loaded)[2:].zfill(n))+(']',)
    target = ('[',machine['accept'],']');word=initial;steps=[]
    for _ in range(4*n+16):
        if word == target: break
        choices = boundary.successors(word,machine['rules'])
        if not choices: break
        steps.append(choices[0]);word=steps[-1][2]
    selection = boundary.derivation_selection(initial,steps,machine['alphabet'],machine['rules'])
    top,bottom = boundary.selected_images(machine['tiles'],selection)
    assert top+('#',)+word == initial+('#',)+bottom
    codes = machine['codes']
    loaded_word = boundary.code(tuple(codes[c] for c in initial+('#',)),width)
    rv = history.positive_outer_fixture(packet['history_packet'],selection,loaded_word)
    v = {name:1 for name in packet['parameters']+packet['auxiliaries']}
    v.update(boundary.outer_fixture(loaded,n,width))
    v.update(x=x,Ufinal=rv['Ufinal'],Vfinal=rv['Vfinal'])
    if pc == 'parameter':v['program_code']=code
    if not packet['inline_initial']:v['Vinitial']=loaded_word
    v.update({'hist__'+name:rv[name] for name in packet['history_packet']['auxiliaries']})
    env=execute(packet['source'],v)
    assert env['input_bottom'] == loaded_word
    assert all(scalar(a,env)==scalar(b,env) for a,b in packet['comparisons'][:5])
    split=packet['boundary_comparisons']
    assert all(scalar(a,env)==scalar(b,env) for a,b in packet['comparisons'][split:split+3])
    last_boundary=packet['comparisons'][split-1]
    accepts=scalar(last_boundary[0],env)==scalar(last_boundary[1],env)
    assert accepts == (word==target) == bool(loaded&1)
    assert all(v[n]>0 for n in packet['parameters']+packet['auxiliaries'])
    # A distinct dense affine implementation verifies the same endpoint.
    dense=boundary.dense_append(machine['tiles'],selection,codes,width,(1,loaded_word,1))
    assert dense == [rv['Ufinal'],rv['Vfinal'],1]
    return dict(input=x,loaded_input=loaded,padding=padding,recoder_duration=n,
                history_duration=len(selection),accepted=accepts,
                full_native_witnesses_materialized=False)


def verify():
    rng=random.Random(3504179);cases=signed=0;records=[];degrees=[]
    tiles=(((0,),(1,)),((1,0),(0,1)),((1,),(1,1)))
    for width in (4,7):
      for layout in ('contiguous','interleaved'):
       for inline in (False,True):
        for loader in (None,'parameter',4):
            packet=build(tiles,width,(2,3),(4,5),(5,2,6,4),layout=layout,
                         inline_initial=inline,program_code=loader)
            source,out=polynomial_source(packet);counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            record=ledger(packet);assert record['polynomial']['operations']==len(source)
            assert counts==dict(M=record['polynomial']['multiplications'],A=record['polynomial']['additions_subtractions'])
            for i in range(16):
                v={n:rng.randrange(1,5) if i<8 else rng.randrange(-2,3)
                   for n in packet['parameters']+packet['auxiliaries']}
                env=execute(source,v);rr=independent(packet,v)
                assert rr==[scalar(a,env)-scalar(b,env) for a,b in packet['comparisons']]
                assert env[out]==sum(r*r for r in rr)
                cases+=1;signed+=i>=8
            degrees.append(dict(record,degree_audit=degree_check(packet)))
    # With a supplied initial endpoint a very wide recoder can dominate.
    wide=build((((0,),(1,)),),100,(2,3),(4,5),(5,2,6,4),
               layout='contiguous',inline_initial=False)
    degrees.append(dict(ledger(wide),degree_audit=degree_check(wide)))
    assert degrees[-1]['degree_audit']['exact_degree']==202
    outer=[]
    for layout in ('contiguous','interleaved'):
      for inline in (False,True):
        packet=odd_machine(layout=layout,inline_initial=inline)
        records.append(dict(ledger(packet),degree_audit=degree_check(packet)))
        for x in (1,2,3):
            outer.append(program_fixture(packet,x,int(x==1)))
    loader_checks=0
    for p in range(16):
      for x in range(1,65):
        N=(1<<p)*(2*x+1)
        valuation=(N&-N).bit_length()-1
        assert valuation==p and ((N>>valuation)-1)//2==x
        loader_checks+=1
    example=odd_machine()
    return dict(status='PASS_GPCP_COMPLETE_FIXED_PROGRAM',
        projection='A positive input belongs to the fixed padded-binary machine language iff the compiled polynomial has positive integer witnesses.',
        sample_language='Positive odd integers; its 34-tile table is not universal.',
        sample_ledgers=records,source_degree_audits=degrees,
        source_checks=dict(full_residual_and_SOS=cases,signed=signed),
        genuine_outer_runs=outer,universal_loader_decode_checks=loader_checks,
        example=dict(ledger=ledger(example),parameters=example['parameters'],
            auxiliaries=example['auxiliaries'],source=example['source'],comparisons=example['comparisons']),
        universal_scope='For any fixed universal interpreter ignoring leading zero padding, build_for_tm yields one fixed table. The 3-gate parameter loader selects every r.e. language by program_code=2^p; no explicit universal interpreter table or numerical universal count is supplied.',
        limitations=['Finite checks do not replace the parametric positive-witness proofs.',
            'Native Pell witnesses are extended by component theorems, not materialized in fixtures.',
            'No improvement of the existing universal75/88 arithmetic frontier is asserted.'])


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    result=json.loads(json.dumps(result))
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
