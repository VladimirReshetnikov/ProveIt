#!/usr/bin/env python3
"""Bounded independent audit of the published Grill Tag E encoding.

Transcribes only the nonhalting two-symbol fragment. No downloaded code runs;
this is not a proof of the full Genera compiler or of ordinary-input universality.
"""
import argparse
import hashlib
from itertools import product
import json
from pathlib import Path

SOURCES={
    'grill':'https://esolangs.org/w/index.php?title=Grill_Tag&oldid=181950',
    'genera':'https://esolangs.org/w/index.php?title=Genera_Tag&oldid=182460',
    'orientation_correction':'https://esolangs.org/w/index.php?title=Talk:Grill_Tag&oldid=181840',
    'creator':'https://codegolf.stackexchange.com/a/265539',
}

def require(ok,message):
    if not ok:raise ValueError(message)

def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def grill(n):
    require(type(n) is int and n>=0,'Natural grill length required')
    return '0'+'10'*n

def encoding(y,width,a,variant,published=False):
    require(type(y) is int and y in (0,1),'Two-symbol fragment only')
    require(type(width) is int and width in (0,1),'Width modulo two')
    require(a==84 and type(a) is int,'Frozen two-symbol scale')
    extra=7*a if width==0 else 0
    if variant=='E':
        return ('0'*(14*y+7)+grill(a-3)+grill(7)+
                grill(a-(2 if published else 4))+'0'*(3*a-14*y-10)+'0'*extra)
    if variant=='L':
        return '0'*(a-3)+grill(14*y+7)+grill(3)+grill(3*a-14*y-10)+'10'*extra
    if variant=='R':
        return '0'+grill(14*y+7)+grill(3)+grill(3*a-14*y-10+extra)+'0'*(a-4)
    raise ValueError('Unknown encoding')

def compiler(rules,widths,a):
    runs=[0]*(14*a);written=set()
    for position,y in product(range(2),range(2)):
        offset=7*a*position
        local=[(28*y+17,a-3),(28*y+19,7),(28*y+21,a-4),
               (28*y+a+13,a-3),(28*y+a+15,7),(28*y+a+17,a-4)]
        u,v=rules[position,y]
        local.extend([(14*y+2*a+3,14*u+7),(14*y+2*a+5,3),
           (14*y+2*a+7,3*a-14*u-10+(7*a if widths[u]==0 else 0)),
           (14*y+2*a+9,0),(14*y+2*a+11,14*v+7),(14*y+2*a+13,3),
           (14*y+2*a+15,3*a-14*v-10+(7*a if widths[v]==0 else 0))])
        for k,n in local:
            target=offset+k
            require(0<=target<len(runs) and target not in written,'Run collision or range')
            require(n>=0 and target%2==1,'Run sign or parity')
            runs[target]=n;written.add(target)
    return runs

def generation(word,phase,runs):
    # Process exactly the current generation; appendants form the next one.
    return ''.join(grill(runs[(phase+j)%len(runs)]) for j,c in enumerate(word) if c=='1'),(phase+len(word))%len(runs)

def verify():
    a=84;cases=0;bad_published=0;lengths=[];first_failure=None
    for y,width in product(range(2),range(2)):
        corrected=len(encoding(y,width,a,'E'))
        old=len(encoding(y,width,a,'E',True))
        expected=7*a*(2 if width==0 else 1)
        require(corrected==expected and old==expected+4,'Length discrepancy')
        lengths.append(dict(symbol=y,width=width,published=old,corrected=corrected,claimed=expected))
    inputs=((0,),(1,),(0,1),(1,0),(0,0,1))
    rule_keys=list(product(range(2),range(2)))
    for widths in product(range(2),repeat=2):
        for outputs in product(range(2),repeat=8):
            rules={key:outputs[2*i:2*i+2] for i,key in enumerate(rule_keys)}
            runs=compiler(rules,widths,a)
            for symbols,start in product(inputs,range(2)):
                position=start;produced=[]
                for y in symbols:
                    produced.extend(rules[position,y]);position=(position+widths[y])%2
                initial=''.join(encoding(y,widths[y],a,'E') for y in symbols)
                expected_lr=''.join(encoding(y,widths[y],a,'L' if i%2==0 else 'R') for i,y in enumerate(produced))
                actual_lr,next_phase=generation(initial,7*a*start,runs)
                require(actual_lr==expected_lr and next_phase==7*a*position,'Corrected E to LR mismatch')
                actual_e,last_phase=generation(actual_lr,next_phase,runs)
                expected_e=''.join(encoding(y,widths[y],a,'E') for y in produced)
                require(actual_e==expected_e and last_phase==next_phase,'LR to corrected E mismatch')
                published=''.join(encoding(y,widths[y],a,'E',True) for y in symbols)
                old_lr,old_phase=generation(published,7*a*start,runs)
                require(old_phase!=next_phase,'Published phase discrepancy disappeared')
                if old_lr!=expected_lr:bad_published+=1
                if first_failure is None:
                    first_failure=dict(widths=widths,rule_outputs=outputs,input_symbols=symbols,start_position=start,
                       published_length=len(published),corrected_length=len(initial),expected_phase=next_phase,
                       published_phase=old_phase,published_output_equals_expected=old_lr==expected_lr)
                cases+=1
    require(cases==10240,'Fixture census')
    return dict(status='PASS_BOUNDED_PRIMARY_SOURCE_REVIEW',helper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       sources=SOURCES,lengths=lengths,checks=dict(rule_tables=256,width_pairs=4,input_strings=5,start_positions=2,
       two_generation_fixtures=cases,corrected_word_identities=2*cases,corrected_phase_identities=2*cases,
       published_phase_failures=cases,published_output_failures=bad_published),first_failure=first_failure,
       scope='Independent nonhalting two-symbol fragment only. The a-4 correction matches the published run list and claimed widths; no full compiler, halt protocol, padding-robust ordinary input or universal arithmetic bound is proved.')

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run without -O')
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);parser.add_argument('--expect',type=Path);args=parser.parse_args()
    result=json.loads(json.dumps(verify()))
    if args.expect:require(exact(result,json.loads(args.expect.read_text())),'Receipt mismatch')
    if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':result['status'],'checks':result['checks']},sort_keys=True))
