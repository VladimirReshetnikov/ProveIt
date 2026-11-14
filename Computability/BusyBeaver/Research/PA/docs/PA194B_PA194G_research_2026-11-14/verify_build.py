#!/usr/bin/env python3
"""Construct PA194B by factoring the decoder through a dedicated history helper.

This establishes an exact, unbounded transfer theorem relative to the pinned
primary table. Local checks touch only two cells; outside tape cells are
universally arbitrary. Symbolic source checks retain the unchanged arithmetic
box hypotheses. No new proof-assistant theorem is claimed.
"""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'vendor'))
import compiler as c

def parse(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q,b,w,d,n = line.split()
        rows[int(q),int(b)] = (int(w), d=='R', int(n))
    return rows

def table(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'
                   for (q,b),(w,d,n) in sorted(rows.items()))

def dense(rows):
    order, index = [74], {74:0}
    for q in order:
        for bit in (0,1):
            n = rows[q,bit][2]
            if n!=254 and n not in index:
                index[n]=len(order);order.append(n)
    assert len(order)==194
    return {(index[q],b):(w,d,194 if n==254 else index[n])
            for (q,b),(w,d,n) in rows.items()}, order+[254]

def seed(rows,path):
    h0=-2
    vals=[0,0,0,0,0,0,2,0,0]+[1]*26
    expected={h0-1,h0+48}
    expected.update(h0+i for i,b in enumerate(path) if b)
    pos=h0+49
    for v in vals:
        pos+=1
        expected.update(range(pos,pos+v+1))
        pos+=v+1
    q,h,ones=74,0,set()
    special=[]
    for k in range(1,100001):
        old=q
        w,d,q=rows[q,int(h in ones)]
        (ones.add if w else ones.discard)(h)
        h+=1 if d else -1
        assert q!=254
        if old==301:
            special.append(k)
        if (q,h,ones)==(84,h0,expected):
            return {'steps':k,'head':h,'state':q,'complete_tape_equality':True,
                    'one_cells':sorted(ones),'physical_file':vals,
                    'helper_visits':len(special)}
    raise AssertionError('Startup did not reach expected seed')

def main():
    assert __debug__, 'Run without -O'
    old=parse(HERE/'inputs/pa194.native.tm')
    assert hashlib.sha256(table(old).encode()).hexdigest()=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
    incoming={q:[(s,b,w,d) for (s,b),(w,d,n) in old.items() if n==q]
              for q in (88,301)}
    assert incoming=={88:[(77,1,1,True)],301:[(87,0,0,True)]}
    assert old[88,0]==(0,True,122) and old[301,0]==(0,True,45)
    assert old[88,1]==old[301,1]==(1,True,103)
    new=dict(old)
    new[87,0]=(0,True,88)
    new[88,0]=(0,False,301)
    new[301,0]=(0,True,122)
    new[301,1]=(1,True,301)
    assert all(new[q,b]==old[q,b] for q in c.BOXSTATES for b in (0,1))
    cases=[]
    for before,history in ((88,1),(301,0)):
        for bit in (0,1):
            w,d,target=old[before,bit]
            goal=(target,1 if d else -1,{-1:history,0:w})
            q,h,tape=88,0,{-1:history,0:bit}
            trace=[]
            for steps in range(1,8):
                assert h in (-1,0), 'Proof inspected an unquantified outside cell'
                b=tape[h]
                w,d,n=new[q,b]
                trace.append([q,h,b,w,1 if d else -1,n])
                tape[h]=w;h+=1 if d else -1;q=n
                if (q,h,tape)==goal:
                    break
            else:
                raise AssertionError((before,bit))
            assert steps==({(88,0):3,(88,1):1,(301,0):5,(301,1):1}[before,bit])
            cases.append({'old_state':before,'history_bit':history,'read_bit':bit,
                          'steps':steps,'trace':trace})
    sites,instructions,contracts=c.source(c.read_grammar(HERE/'inputs/pa194.grammar.json'))
    assert len(sites)==3673 and len(contracts)==4780
    baseline=c.validate(old,contracts)
    validated=c.validate(new,contracts)
    assert baseline['ok'] and validated['ok']
    startup0=seed(old,sites[25][0]);startup=seed(new,sites[25][0])
    dense_rows,labels=dense(new)
    out=HERE/'machine';out.mkdir(exist_ok=True)
    (out/'pa194B.native.tm').write_text(table(new))
    (out/'pa194B.tm').write_text(table(dense_rows))
    (out/'pa194B.labels.json').write_text(json.dumps(labels)+'\n')
    hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file()}
    result={'working_states':194,'transitions':388,'start':0,'halt':194,
      'native_start':74,'native_halt':254,'incoming_history':incoming,
      'local_cases':cases,'maximum_local_steps':5,'unchanged_arithmetic_boxes':True,
      'source_sites':len(sites),'baseline_symbolic_runtime':baseline,
      'symbolic_runtime':validated,'baseline_startup':startup0,'startup':startup,
      'sha256':hashes,'proof_scope':'Ordinary finite-tape simulation, formalizable in PA; Python certificates and unchanged arithmetic lemmas, no new Lean endpoint.'}
    (HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('local_cases','incoming_history')},indent=2))

if __name__=='__main__':
    main()
