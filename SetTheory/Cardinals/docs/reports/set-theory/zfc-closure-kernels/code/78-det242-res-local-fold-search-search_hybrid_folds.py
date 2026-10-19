#!/usr/bin/env python3
"""Search one-state hybrid folds with universally checked local simulations.

The old machine's invariant is a sound fixed point over finite tape windows
and arbitrary initial tape at state95. For each pair(a,b) and a two-bit row
choice, redirect b to a. At every admitted old entry to a or b, check that
one old step is simulated by1..K new steps under the state map b->a, with
exact head and whole-tape equality. Paths may not inspect outside the known
window. Every untouched exterior cell is arbitrary. All other old rows
commute with the state map by literal table construction.

Successful candidates have a relative halting proof, with no finite-run
sampling premise. Unsuccessful candidates are rejected only by this
particular invariant and local proof bound; no lower bound is claimed.
"""
from pathlib import Path
import itertools,pickle,json,time,sys,random,hashlib
from window_invariant import read_table

def search(base,inv,K):
    table=read_table(base);L,R,reached=pickle.loads(inv.read_bytes())
    states=sorted(reached);rng=random.Random(20261018)
    # Independently validate the loaded finite invariant, so candidate
    # proofs do not rely merely on trusting an earlier search output.
    assert L>=1 and R>=1
    width=L+R+1;size=1<<width;bits_mask=size-1
    assert set(reached)=={q for q,b in table}
    assert all(reached[95]) and all(len(x)==size for x in reached.values())
    invariant_checks=0
    for q in states:
        for v,yes in enumerate(reached[q]):
            if not yes:continue
            invariant_checks+=1
            w,d,t=table[q,(v>>L)&1]
            if t not in reached:continue
            u=(v&~(1<<L))|(w<<L)
            if d==1:lo=u>>1;hi=lo|(1<<(width-1))
            else:lo=(u<<1)&bits_mask;hi=lo|1
            assert reached[t][lo] and reached[t][hi]
    allowed={q:[v for v,yes in enumerate(reached[q])if yes]for q in states}
    for values in allowed.values():rng.shuffle(values)
    one_step={}
    for q in states:
        rows=[]
        for v in allowed[q]:
            w,d,t=table[q,(v>>L)&1]
            target=(v&~(1<<L))|(w<<L)
            rows.append((v,t,d,target))
        one_step[q]=rows
    def check(new,entry,v,target_q,target_h,target_tape):
        q,h,tape=entry,0,v
        for k in range(1,K+1):
            if h < -L or h>R or(q,(tape>>(h+L))&1)not in new:return 0
            w,d,t=new[q,(tape>>(h+L))&1]
            tape=(tape&~(1<<(h+L)))|(w<<(h+L));h+=d;q=t
            if(q,h,tape)==(target_q,target_h,target_tape):return k
        return 0
    began=time.monotonic();trials=0;survivors=[]
    for a,b in itertools.combinations(states,2):
        for mask in range(4):
            trials+=1
            new={key:(w,d,a if t==b else t)for key,(w,d,t)in table.items()if key[0]!=b}
            for s in(0,1):
                w,d,t=table[b if mask&(1<<s)else a,s]
                new[a,s]=(w,d,a if t==b else t)
            passed=True;tested=0;maximum=0
            for q in(a,b):
                for v,t,h,tt in one_step[q]:
                    clock=check(new,a,v,a if t==b else t,h,tt)
                    if not clock:passed=False;break
                    tested+=1;maximum=max(maximum,clock)
                if not passed:break
            if passed:
                for(q,s),(w,d,t)in table.items():
                    if q not in(a,b):
                        assert new[q,s]==(w,d,a if t==b else t)
                record={'retained':a,'deleted':b,'mask':mask,
                        'checked_windows':tested,'max_new_clock':maximum,
                        'state_map':f'f({b})={a}; f(q)=q otherwise',
                        'new_start':a if b==95 else 95}
                survivors.append(record);print(json.dumps(record),flush=True)
    return {'status':'COMPLETE_IN_STATED_LOCAL_PROOF_FAMILY',
            'baseline_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),
            'window_left':L,'window_right':R,'initial_state':95,
            'initial_tape':'arbitrary','local_new_step_bound':K,
            'inductive_invariant_contexts_checked':invariant_checks,
            'invariant_initialization_and_closure':'PASS',
            'invariant_pickle_sha256':hashlib.sha256(inv.read_bytes()).hexdigest(),
            'hybrid_fold_trials':trials,'survivors':survivors,
            'seconds':time.monotonic()-began,
            'scope':'Exact whole-tape one-to-bounded-many step simulation under an inductive finite-window invariant. Rejection is not a state lower bound.'}

if __name__=='__main__':
    here=Path(__file__).parent
    inv=here/(sys.argv[1]if len(sys.argv)>1 else'invariant_L8_R2.pkl')
    K=int(sys.argv[2])if len(sys.argv)>2 else 12
    result=search(here/'base.tm',inv,K)
    (here/'hybrid_fold_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
