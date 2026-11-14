#!/usr/bin/env python3
"""Independent, source-free proof certificate for U222 -> U221.

A finite inductive invariant proves native state 200 only reads 0.
Replacing 200 by 209 then gives a lockstep simulation on every tape
starting in state 0, hence identical halting times and tape histories.
No inherited runtime checker or source compiler is imported.
"""
from pathlib import Path
import argparse, hashlib, json

def read(path):
    T={};starts=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):starts.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            if (q,b) in T or q < 0 or z < 0 or b not in (0,1) or w not in (0,1) or d not in ('L','R'):raise ValueError('bad row')
            T[q,b]=(w,1 if d=='R' else -1,z)
    if starts!=[0]:raise ValueError('bad initial state')
    Q={q for q,b in T}
    if set(T)!={(q,b)for q in Q for b in(0,1)}:raise ValueError('incomplete binary table')
    if {z for w,d,z in T.values()}-Q!={254}:raise ValueError('bad halt target')
    return T

def encode(T):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode('ascii')

def must(ok,why):
    if not ok:raise ValueError(why)

def known_symbol_analysis(T,radius=3):
    # Cartesian over-approximation, one two-bit mask for each nearby cell.
    # Initial state 0 permits EVERY tape, which is stronger than blank.
    offsets=range(-radius,radius+1);full=(3,)*(2*radius+1)
    facts={q:None for q,b in T};facts[0]=full;todo=[0]
    for q in todo:
        row=facts[q]
        for b in (0,1):
            if not row[radius]&(1<<b):continue
            w,d,z=T[q,b]
            if z==254:continue
            before={o:row[o+radius]for o in offsets};before[0]=1<<w
            out=tuple(before.get(o+d,3)for o in offsets)
            prev=facts[z];merged=out if prev is None else tuple(x|y for x,y in zip(prev,out))
            if merged!=prev:facts[z]=merged;todo.append(z)
    # Independent inductiveness check of the computed post-fixed point.
    must(facts[0]==full,'initial arbitrary tape excluded')
    for q,row in facts.items():
        if row is None:continue
        for b in (0,1):
            if not row[radius]&(1<<b):continue
            w,d,z=T[q,b]
            if z==254:continue
            before={o:row[o+radius]for o in offsets};before[0]=1<<w
            out=tuple(before.get(o+d,3)for o in offsets)
            must(facts[z] is not None and all(x|y==y for x,y in zip(out,facts[z])),'non-inductive fact')
    unused=[list((q,b))for q,row in sorted(facts.items())for b in(0,1)if row is None or not row[radius]&(1<<b)]
    return {'radius':radius,'initial_tape':'arbitrary','excluded_rows':unused,'facts':{str(q):{str(o):0 if row[o+radius]==1 else 1 for o in offsets if row[o+radius]!=3}for q,row in sorted(facts.items())if row is not None}}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('baseline',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--candidate',type=Path);args=ap.parse_args()
    old=read(args.baseline);Q={q for q,b in old}
    must(len(Q)==222,'baseline count')
    incoming=lambda z:sorted([[q,b,w,d,t]for(q,b),(w,d,t)in old.items()if t==z])
    must(incoming(112)==[[172,0,0,-1,112]],'112 has an unreviewed incoming row')
    must(incoming(200)==[[112,1,1,1,200]],'200 has an unreviewed incoming row')
    must(old[200,0]==old[209,0]==(0,1,157),'needed actions differ')
    must(0 not in(112,200) and 254 not in(112,200,209),'initial/halt overlap')
    # Invariant I: q=112 => tape[head+1]=0; q=200 => tape[head]=0.
    # The complete incoming-edge equalities above prove preservation.
    rho=lambda q:209 if q==200 else q
    new={(q,b):(w,d,rho(z))for(q,b),(w,d,z)in old.items()if q!=200}
    # All permissible old transitions commute with rho; (200,1) is excluded.
    for(q,b),(w,d,z)in old.items():
        if (q,b)==(200,1):continue
        must(new[rho(q),b]==(w,d,rho(z)),'lockstep diagram does not commute')
    if args.candidate:must(read(args.candidate)==new,'candidate differs from proved reduction')
    abstract=known_symbol_analysis(old)
    must(abstract['excluded_rows']==[[200,1]],'unexpected excluded-row analysis')
    newabstract=known_symbol_analysis(new)
    result={
      'status':'SOURCE_INDEPENDENT_LOCKSTEP_EQUIVALENCE_PASS',
      'initial_state':0,'initial_tapes':'ALL_BINARY_TAPES','halt_label':254,
      'baseline_sha256':hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
      'candidate_canonical_sha256':hashlib.sha256(encode(new)).hexdigest(),
      'candidate_actual_sha256':hashlib.sha256(args.candidate.read_bytes()).hexdigest() if args.candidate else None,
      'baseline_working_states':222,'candidate_working_states':221,
      'incoming_112':incoming(112),'incoming_200':incoming(200),
      'invariant':[{'state':112,'offset':1,'symbol':0},{'state':200,'offset':0,'symbol':0}],
      'state_map':{'200':209,'all_other_states':'identity'},
      'changed_retained_rows':[[q,b,*old[q,b],*a]for(q,b),a in sorted(new.items())if old[q,b]!=a],
      'deleted_state':200,'permissible_action_diagrams_checked':443,
      'preserved':'exact halting time, head positions and every tape cell at every step',
      'proof_scope':'finite inductive invariant plus deterministic lockstep simulation; ordinary mathematical proof formalizable in PA; no proof-assistant endpoint claimed',
      'baseline_abstract_analysis':abstract,'candidate_abstract_analysis':newabstract}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if 'abstract_analysis'not in k},indent=2))
if __name__=='__main__':main()
