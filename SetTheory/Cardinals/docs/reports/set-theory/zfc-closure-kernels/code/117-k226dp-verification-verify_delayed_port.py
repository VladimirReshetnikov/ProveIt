#!/usr/bin/env python3
"""Independently audit the exact K delayed-erasure port and blank startup.

This proves four open-tape local block equalities, an inductive predecessor-bit
invariant, and every blank-start checkpoint through the supplied old prefix.
The additional 169/read-1 right-neighbor premise is checked on the exact prefix;
unbounded runtime of the final table requires the separate symbolic certificate.

Python 3.10+ standard library. Run with assertions enabled.
"""
from pathlib import Path
from collections import Counter, deque
import argparse, hashlib, itertools, json, sys

START, HALT = 95, 254
SPECS = [(80,0,{-1:1},5), (169,0,{-1:0},3),
         (169,1,{-1:0,1:1},5), (91,1,{-3:0,-2:1,-1:1},9)]

def require(ok, message):
    if not ok: raise ValueError(message)

def parse(path):
    table = {}; starts = []
    for line in path.read_text().splitlines():
        if line.startswith('#! start '): starts.append(int(line[9:])); continue
        if not line or line.startswith('#'): continue
        q,b,w,d,z = line.split(); q,b,w,z = map(int,(q,b,w,z))
        require((q,b) not in table and b in (0,1) and w in (0,1) and d in ('L','R'), 'Malformed or duplicate row')
        table[q,b] = (w,1 if d=='R' else -1,z)
    states = {q for q,b in table}
    require(starts==[START], 'Wrong initial state')
    require(set(table)=={(q,b) for q in states for b in (0,1)}, 'Partial table')
    require({z for w,d,z in table.values()}-states=={HALT}, 'Wrong halt')
    return table

def invariant(t, radius=3):
    facts = {q:None for q,b in t}; facts[HALT]=None; facts[START]={}
    queue = deque([START]); queued={START}
    while queue:
        q=queue.popleft(); queued.remove(q)
        if q==HALT: continue
        for b in (0,1):
            if 0 in facts[q] and facts[q][0]!=b: continue
            w,d,z=t[q,b]
            post={k-d:v for k,v in {**facts[q],0:w}.items() if -radius<=k-d<=radius}
            new=post if facts[z] is None else {k:v for k,v in facts[z].items() if post.get(k)==v}
            if new!=facts[z]:
                facts[z]=new
                if z not in queued: queue.append(z); queued.add(z)
    checks=0
    for (q,b),(w,d,z) in t.items():
        if facts[q] is None or (0 in facts[q] and facts[q][0]!=b): continue
        post={k-d:v for k,v in {**facts[q],0:w}.items()}
        require(facts[z] is not None and all(post.get(k)==v for k,v in facts[z].items()), 'Non-inductive bit fact')
        checks+=1
    require(facts[START]=={}, 'Invariant constrains the initial tape')
    return facts,checks

def local(t,q,tape,steps):
    h=0; trace=[]
    for _ in range(steps):
        require(h in tape, 'Local block reads an arbitrary exterior cell')
        require(q!=HALT, 'Interior halt')
        b=tape[h]; w,d,z=t[q,b]
        trace.append([q,h,b,w,d,z]); tape[h]=w; h+=d; q=z
    return q,h,tape,trace

def sparse_step(t,q,h,ones):
    w,d,z=t[q,int(h in ones)]
    if w: ones.add(h)
    else: ones.discard(h)
    return z,h+d

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old',type=Path,required=True); ap.add_argument('--new',type=Path,required=True)
    ap.add_argument('--old-steps',type=int,required=True)
    ap.add_argument('--startup-reference',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True); a=ap.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    O,N=parse(a.old),parse(a.new); phi=lambda q:80 if q==169 else q
    expected={(q,b):(w,d,phi(z)) for (q,b),(w,d,z) in O.items() if q!=169}
    expected[80,0]=(0,-1,106); expected[91,1]=(1,-1,167)
    require(N==expected and len(N)==len(O)-2, 'Unexpected port edits or state census')
    facts,checks=invariant(O)
    for q,wanted in [(67,{-1:0}),(80,{-1:1,-2:0}),(91,{-1:1,-2:1,-3:0}),(169,{-1:0})]:
        require(all(facts[q].get(k)==v for k,v in wanted.items()), 'Missing predecessor fact')
    records=[]
    for q,b,guard,length in SPECS:
        cases=[]
        for bits in itertools.product((0,1),repeat=5):
            tape=dict(zip(range(-3,2),bits))
            if tape[0]!=b or any(tape[k]!=v for k,v in guard.items()): continue
            qo,ho,to,ot=local(O,q,dict(tape),1)
            qn,hn,tn,nt=local(N,phi(q),dict(tape),length)
            require((phi(qo),ho,to)==(qn,hn,tn), 'Incorrect local block')
            cases.append({'input':tape,'old_trace':ot,'new_trace':nt})
        require(bool(cases), 'Empty guard')
        records.append({'old_row':[q,b],'guard':guard,'duration':length,'cases':cases})
    exceptions={(q,b) for q,b,g,n in SPECS}; commuting=0
    for (q,b),(w,d,z) in O.items():
        if (q,b) not in exceptions:
            require(N[phi(q),b]==(w,d,phi(z)), 'Ordinary row does not commute'); commuting+=1
    qo=qn=START; ho=hn=0; so=set(); sn=set(); newsteps=0; used=Counter(); gvisits=[]
    lengths={(q,b):n for q,b,g,n in SPECS}
    for tick in range(a.old_steps):
        require((phi(qo),ho,so)==(qn,hn,sn), f'Startup mismatch at old step {tick}')
        row=qo,int(ho in so); used[row]+=1
        if row==(169,1):
            require(ho+1 in so, 'G169 fails during blank startup')
            gvisits.append({'old_time':tick,'new_time':newsteps,'head':ho})
        duration=lengths.get(row,1); qo,ho=sparse_step(O,qo,ho,so)
        for _ in range(duration): qn,hn=sparse_step(N,qn,hn,sn)
        newsteps+=duration
    require((phi(qo),ho,so)==(qn,hn,sn), 'Final startup mismatch')
    reference=json.loads(a.startup_reference.read_text())
    require((qn,hn)==(96,-5) and reference['one_cells']==sorted(sn), 'Unexpected calibrated startup endpoint')
    out={'status':'EXACT_CHECKPOINT_STARTUP_AND_OPEN_LOCAL_BLOCKS_PASS',
         'old_sha256':hashlib.sha256(a.old.read_bytes()).hexdigest(),
         'new_sha256':hashlib.sha256(a.new.read_bytes()).hexdigest(),
         'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'old_states':len(O)//2,'new_states':len(N)//2,'old_steps':a.old_steps,'new_steps':newsteps,
         'matched_checkpoints':a.old_steps+1,'commuting_rows':commuting,'local_records':records,
         'facts':{q:facts[q] for q in(67,80,91,169)},'inductive_fact_row_checks':checks,
         'G169_scope':'Every exceptional startup visit. Final-table universal runtime is certified separately.',
         'G169_startup_visits':gvisits,'special_counts':{str(row):used[row] for row in lengths},
         'endpoint_state':qn,'endpoint_head':hn,'one_cells':sorted(sn)}
    a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in('local_records','one_cells','G169_startup_visits')},indent=2))

if __name__=='__main__': main()
