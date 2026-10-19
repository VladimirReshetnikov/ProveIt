#!/usr/bin/env python3
"""Independent exhaustive local proof of the 237 -> 236 fold.

Every permitted local window is checked; the source of the left-bit guard
is proved by enumerating every incoming row of the OLD literal table.
No sampled runtime profile or register-frame invariant is used.
"""
from pathlib import Path
import hashlib, itertools, json

import sys
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Run without -O/-OO: verification assertions are required.')

HERE=Path(__file__).resolve().parent
OLD=HERE/'ingredients/reassociated237_old.tm'
NEW=HERE/'zfc_reassociate236_old.tm'

def load(path):
    t={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();k=int(q),int(b)
        assert k not in t
        assert d in ('L','R') and int(b) in (0,1) and int(w) in (0,1)
        t[k]=int(w), 1 if d=='R' else -1, int(z)
    states={q for q,b in t}
    assert len(t)==2*len(states)
    assert 95 in states and 254 not in states
    assert all(z in states or z==254 for w,d,z in t.values())
    return t

def phi(q): return 182 if q==223 else q

def run(t,state,tape,n):
    tape=dict(tape);head=0;path=[state]
    for _ in range(n):
        assert head in tape,'read outside finite local window'
        w,d,state=t[state,tape[head]]
        tape[head]=w;head+=d;path.append(state)
    return state,head,tape,path

def main():
    a,b=load(OLD),load(NEW)
    assert len(a)==474 and len(b)==472
    # This predecessor statement proves the runtime tag invariant for all
    # initial tapes: the start state is neither tagged state, and every
    # entry into a tagged state moves right and writes its required tag.
    incoming={q:[{'q':s,'b':c,'w':w,'direction':d} for (s,c),(w,d,z) in a.items() if z==q]
              for q in (182,223)}
    assert incoming=={182:[{'q':76,'b':1,'w':1,'direction':1}],
                     223:[{'q':237,'b':0,'w':0,'direction':1}]}
    unchanged=0
    for (q,c),(w,d,z) in a.items():
        if q in (182,223): continue
        assert b[phi(q),c]==(w,d,phi(z)),(q,c)
        unchanged+=1
    assert unchanged==470
    paths=[];window_count=0
    for q in (182,223):
        tag=int(q==182)
        for bit in (0,1):
            possible_paths=set()
            for left2,right1,right2 in itertools.product((0,1),repeat=3):
                tape={-2:left2,-1:tag,0:bit,1:right1,2:right2}
                oq,oh,ot,op=run(a,q,tape,1)
                nq,nh,nt,np=run(b,phi(q),tape,3)
                assert (phi(oq),oh,ot)==(nq,nh,nt)
                assert nt==tape,'every exceptional path preserves every tape bit'
                assert oh==1 and nh==1
                possible_paths.add(tuple(np));window_count+=1
            assert len(possible_paths)==1
            paths.append({'old_state':q,'read':bit,'left_tag':tag,'old_steps':1,'new_steps':3,'new_path':list(possible_paths.pop())})
    result={'status':'PASS_ALL_BINARY_INITIAL_TAPES_FROM_95',
            'old_sha256':hashlib.sha256(OLD.read_bytes()).hexdigest(),
            'new_sha256':hashlib.sha256(NEW.read_bytes()).hexdigest(),
            'old_states':237,'new_states':236,'incoming_tag_proof':incoming,
            'ordinary_rows_commute':unchanged,'exceptional_rows':4,
            'exhaustive_windows_checked':window_count,'paths':paths,
            'clock':'tau(t) = t + 2 * #{i<t: old_state(i) in {182,223}}',
            'clock_bounds':'t <= tau(t) <= 3*t',
            'conclusion':'Old and new halt from the same binary initial tape iff the other halts; the state map fixes start95 and halt254.',
            'scope':'Exact finite local certificate plus incoming-edge induction. No empirical-profile assumption.'}
    (HERE/'local_fold_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
