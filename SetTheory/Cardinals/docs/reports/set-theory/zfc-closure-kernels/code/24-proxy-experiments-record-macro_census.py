#!/usr/bin/env python3
"""Replay concrete row-coverage witnesses for ZFC253, without box oracles.

Default: use the included small witness corpus.
Optional --program Prog254.v: reproduce all 8391 macro tests from the pinned
upstream register program. The script never downloads or executes that file;
it only parses its literal finite tree. Tests do not prove an unbounded TM
simulation or the machine's consistency equivalence.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, re
from make_certificate import parse

HERE=Path(__file__).resolve().parent
PROGRAM_SHA='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
PHYSICAL=(6,7,0,2,1,8,4,3,5)

def all_inputs(path):
    data=path.read_bytes()
    if hashlib.sha256(data).hexdigest()!=PROGRAM_SHA:raise ValueError('program hash')
    text=data.decode('ascii').split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',text)
    if len(nodes)!=6459:raise ValueError('tree length')
    result=[];stack=[('CN 0','')]
    while stack:
        instruction,path=stack.pop();kind,*argument=instruction.split()
        if kind=='CN':
            left,right=nodes[int(argument[0])]
            stack.extend([(right,path+'1'),(left,path+'0')])
        else:
            for positive in ([False,True] if kind=='CD' else [False]):
                result.append(dict(path=path,kind=kind,argument=int(argument[0]) if argument else None,
                                   positive=positive,gap=40))
    if len(result)!=8391:raise ValueError('expected8391 cases')
    return result

def increment(path):
    return None if '0' not in path else path[:path.rindex('0')]+'1'

def strip(bit,k,path):
    while k and path:
        if path[-1]==bit:k-=1
        path=path[:-1]
    return path

def make_tape(path,gap,registers,extra,head=0):
    cells=list(map(int,path))+[0]*(gap-len(path))+[1]
    for value in registers+extra:cells.extend([0]+[1]*(value+1))
    ones={i+head for i,bit in enumerate(cells) if bit};ones.add(head-1)
    return ones

def macro(table,case,usage):
    path,kind,arg,positive,gap=(case[k] for k in ('path','kind','argument','positive','gap'))
    registers=[0]*9;extra=[0,1,0,2]
    target_register=PHYSICAL[arg] if kind in ('CI','CD') else None
    if positive:registers[target_register]=1
    tape=make_tape(path,gap,registers,extra)
    changed=registers[:]
    if kind=='CI' or (kind=='CD' and positive):
        target_path=increment(path);changed[target_register]+=1 if kind=='CI' else -1
    elif kind=='CD':target_path=increment(strip('0',1,path))
    elif kind=='CB':target_path=increment(strip('0',arg,path))
    elif kind=='CC':target_path=strip('1',arg,path)
    else:target_path=''
    overflow=target_path is None
    target_head=-1 if overflow else 0
    expected=make_tape(target_path or '',gap+int(overflow),changed,
                       extra+([0] if kind=='CD' and positive else []),target_head)
    state=33;head=0
    for step in range(200001):
        if state==253:
            if kind!='CH':raise ValueError('unexpected halting')
            return step
        if step and state==33 and head==target_head and tape==expected:
            if kind=='CH':raise ValueError('halt site returned')
            return step
        bit=int(head in tape);usage[state,bit]+=1
        write,direction,state=table[state,bit]
        if write:tape.add(head)
        else:tape.discard(head)
        head+=1 if direction=='R' else -1
    raise ValueError('finite macro fuel exceeded')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--program',type=Path)
    parser.add_argument('--output',type=Path,default=HERE/'census_replay.json')
    args=parser.parse_args()
    table=parse(HERE/'zfc_253.tm')
    inputs=all_inputs(args.program) if args.program else json.loads((HERE/'macro_inputs.json').read_text())['inputs']
    usage=Counter();durations=[macro(table,case,usage) for case in inputs]
    if set(usage)!=set(table)-{(0,0)}:raise ValueError('expected505 runtime rows')
    blank_usage=Counter();tape=set();head=0;state=0
    for step in range(312975):
        bit=int(head in tape);blank_usage[state,bit]+=1
        write,direction,state=table[state,bit]
        if write:tape.add(head)
        else:tape.discard(head)
        head+=1 if direction=='R' else -1
    if state!=33 or head!=-17:raise ValueError('blank prefix checkpoint')
    if set(usage)|set(blank_usage)!=set(table):raise ValueError('row union')
    out={'kind':'finite concrete macro tests and blank-prefix row census; not a universal simulation proof',
         'mode':'all_pinned_program_sites' if args.program else 'included_witness_subcorpus',
         'cases':len(inputs),'total_macro_steps':sum(durations),'max_macro_steps':max(durations),
         'runtime_rows_observed':len(usage),'runtime_states_observed':len({q for q,b in usage}),
         'runtime_unobserved_rows':[[0,0]],'blank_prefix_steps':312975,
         'blank_prefix_end_state':state,'blank_prefix_end_head':head,
         'blank_only_rows':[list(k) for k in blank_usage if k not in usage],
         'union_rows_observed':len(set(usage)|set(blank_usage))}
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
