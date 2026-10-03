#!/usr/bin/env python3
"""Exact counterexample to using the reviewed encoded Grill fragment as a padding decoder."""
import argparse
from collections import deque
import hashlib
import itertools
import json
from pathlib import Path
import types

PIN = '66c64fc95574b4d938a3a05e443215f802825677129a17e3cd38fae4150a12f3'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def load(path):
    data = path.read_bytes()
    need(hashlib.sha256(data).hexdigest() == PIN, 'reviewed encoding source pin')
    m = types.ModuleType('_encoded_padding_reference'); m.__file__ = str(path)
    exec(compile(data, str(path), 'exec'), m.__dict__)
    return m

def generation(program, word, phase):
    chunks = []
    for bit in word:
        if bit == '1':
            chunks.append('0' + '10'*program[phase])
        phase = (phase+1) % len(program)
    return ''.join(chunks), phase

def first_halt(program, word, expected):
    queue = deque(word); phase = 0; digest = hashlib.sha256()
    for t in range(expected):
        need(bool(queue), 'earlier halt than certified')
        bit = queue.popleft()
        if bit == '1':
            queue.extend('0'+'10'*program[phase])
        phase = (phase+1) % len(program)
        digest.update(f'{t+1}:{phase}:'.encode())
        digest.update(''.join(queue).encode()); digest.update(b'\n')
    need(not queue, 'queue not empty at certified first halt')
    return dict(first_halt=expected, terminal_phase=phase, full_trace_sha256=digest.hexdigest())

def verify(source):
    m = load(source); a = 84
    rules = {key:(0,0) for key in itertools.product(range(2), repeat=2)}
    program = tuple(m.compiler(rules, (1,1), a))
    E = m.encoding(0,1,a,'E'); L = m.encoding(0,1,a,'L'); R = m.encoding(0,1,a,'R')
    need(len(program)==1176 and program[:588]==program[588:], 'actual repeated program block')
    need(len(E)==len(L)==len(R)==588, 'corrected encoding lengths')
    local = []
    for phase in (0,588):
        one, after_one = generation(program,E,phase)
        pair, after_pair = generation(program,L+R,phase)
        need(one==L+R and after_one==(phase+588)%1176, 'exact E to LR block')
        need(pair==E+E and after_pair==phase, 'exact LR to EE block')
        need(m.generation(E,phase,program)==(one,after_one), 'independent first block agrees with frozen implementation')
        need(m.generation(L+R,phase,program)==(pair,after_pair), 'independent second block agrees with frozen implementation')
        local.append(dict(phase=phase,E_to_LR=True,LR_to_EE=True,E_next_phase=after_one,LR_next_phase=after_pair))
    erasure = []
    for phase in (6,594):
        need(generation(program,L+R,phase)==('0'*504,phase), 'exact shifted LR erasure block')
        erasure.append(dict(phase=phase,output_zeros=504,phase_preserved=True))
    # The four local word equalities imply an infinite sequence of nonempty
    # generations for E^k, alternating (LR)^k and E^(2k), for every k>=1.
    family = []
    for k in range(1,7):
        word=E*k; x=int(word[::-1],2); initial_phase=len(word)%1176
        need(2**len(word)>3*x and int((word+'0'*6)[::-1],2)==x, 'same ordinary input and both strong-cone widths')
        first, p1 = generation(program, word+'0'*6, 0)
        second, p2 = generation(program,first,p1)
        need(first==(L+R)*k and p1==(initial_phase+6)%1176, 'padded first generation')
        need(second=='0'*(504*k), 'shifted second generation has only zeros')
        need(generation(program,second,p2)[0]=='', 'third generation empties')
        fixture=dict(encoded_blocks=k,ordinary_input=str(x),ordinary_input_bit_length=x.bit_length(),
                     original_bit_length=len(word),padded_bit_length=len(word)+6,
                     padded_first_halt=2268*k+6,second_generation_zero_count=len(second))
        if k<=2:
            fixture['literal_FIFO']=first_halt(program,word+'0'*6,2268*k+6)
        family.append(fixture)
    kill=[]
    for padding in range(1176):
        output, phase = generation(program,L+R,(588+padding)%1176)
        if '1' not in output:
            need(output=='0'*504, 'all selected appendants are singleton zeros')
            kill.append(padding)
    need(len(kill)==474 and kill[0]==6 and 0 not in kill, 'complete second-generation erasure census')
    return dict(status='PASS_ENCODED_GRILL_PADDING_OBSTRUCTION',
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),reference_sha256=PIN,
        fixed_program=list(program),corrected_blocks=dict(E=E,L=L,R=R),
        local_word_certificates=local,erasure_word_certificates=erasure,
        family=family,second_generation_erasing_padding_residues=kill,
        claims=dict(original_nonhalting='For all k>=1, the exact local identities inductively give nonempty E^k -> (LR)^k -> E^(2k) generations.',
                    padded_halting='For all k>=1, E^k followed by six zeros halts after exactly2268*k+6 steps, preserving the ordinary binary integer.',
                    obstruction='The original encoded run and existential-padding interpretation have different halting truth for the same ordinary integer.',
                    scope='This is the reviewed corrected nonhalting two-symbol fragment, not the complete creator compiler. It refutes a direct padding-insensitive embedding of this fragment, not Grill universality or all possible input decoders. The474 residues are second-generation erasure certificates, not a classification of every residue.'))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=Path(__file__).with_name('review_grill_encoding_e.py'))
    p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path)
    a=p.parse_args();r=verify(a.source)
    if a.expect:
        need(exact(r,json.loads(a.expect.read_text())), 'saved receipt mismatch')
    if a.output:
        a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status=r['status'],local_word_certificates=r['local_word_certificates'],
                         erasing_residues=len(r['second_generation_erasing_padding_residues']),
                         first_halt=r['family'][0]['padded_first_halt']),indent=2))
