#!/usr/bin/env python3
"""Demand-driven two-action state folds; bounded diagrams, not lower bounds.

An unassigned action is explored only when a tested trajectory reads it.
Failure before that read rejects every completion of the partial table.
The unchanged independent checker alone certifies any complete survivor.
"""
from pathlib import Path
import argparse, gzip, hashlib, importlib.util, itertools, json, sys, time

P = Path(__file__).resolve().parent.parent / 'k219-continuation-search'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p, x): p.write_text(json.dumps(x, indent=2) + '\n')
def load(p, name):
    spec = importlib.util.spec_from_file_location(name, p)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
shared = load(P / 'search_v3.py', 'shared')
INPUTS = json.loads((P / 'inputs.json').read_text())
checker = shared.load_checker((P / INPUTS['universal_checker']['path']).resolve())

class Deadline(Exception): pass

class PartialFilter:
    def __init__(self, old, inv, keep, drop, radius, fuel):
        self.old, self.keep, self.drop, self.radius, self.fuel = old, keep, drop, radius, fuel
        self.phi = lambda q: keep if q == drop else q
        self.new = {(q,b):(w,d,self.phi(z)) for (q,b),(w,d,z) in old.items() if q != drop}
        self.new[keep,0] = self.new[keep,1] = None
        self.cache = {}
        self.patterns = {}
        for q in (keep, drop):
            for b in (0,1):
                a = sorted(m for m in inv[q] if ((m >> radius) & 1) == b)
                self.patterns[q,b] = [a[0],a[-1],*a[1:-1]] if len(a)>2 else a

    def check(self):
        old, new, phi, r, f, keep = self.old,self.new,self.phi,self.radius,self.fuel,self.keep
        for q in (keep,self.drop):
            for b in (0,1):
                w,d,z = old[q,b]
                if new[keep,b] == (w,d,phi(z)): continue
                for word in self.patterns[q,b]:
                    key = (q,word)
                    if key not in self.cache:
                        oq,oh,om = q,0,word; goals=set(); old_halts=False
                        for tick in range(f):
                            if oq==254 or not -r<=oh<=r: break
                            ob=(om>>(oh+r))&1; ow,od,oq=old[oq,ob]
                            om=(om&~(1<<(oh+r)))|(ow<<(oh+r)); oh+=od
                            goals.add((phi(oq),oh,om)); old_halts |= oq==254
                        self.cache[key] = goals,old_halts
                    goals,old_halts=self.cache[key]
                    nq,nh,nm=keep,0,word; visited=set(); joined=False
                    reason='no_join_within_filter_fuel'
                    for tick in range(f):
                        if nq==254 or not -r<=nh<=r:
                            reason='new_exits_window_before_join'; break
                        conf=(nq,nh,nm)
                        if conf in visited: reason='new_repeats_before_join'; break
                        visited.add(conf)
                        nb=(nm>>(nh+r))&1; action=new[nq,nb]
                        if action is None:
                            assert nq==keep
                            return 'need',nb
                        nw,nd,nq=action
                        nm=(nm&~(1<<(nh+r)))|(nw<<(nh+r)); nh+=nd
                        if nq==254:
                            joined=old_halts; reason='new_halt_without_old_halt'; break
                        if (nq,nh,nm) in goals: joined=True; break
                    if not joined:
                        return 'reject',{'old_row':[q,b], 'window':word, 'reason':reason}
        return 'pass',None

def synthesize(pf, actions, deadline, reject, accept):
    stat={'partial_checks':0,'rejection_leaves':0,'covered_rejections':0,'survivors':0,
          'pruned_by_assigned_count':{'0':0,'1':0,'2':0},'expected_complete_tables':len(actions)**2}
    def walk():
        if time.monotonic()>=deadline: raise Deadline()
        stat['partial_checks']+=1
        outcome, data=pf.check()
        assigned=[pf.new[pf.keep,b] for b in (0,1)]
        depth=sum(a is not None for a in assigned)
        if outcome=='reject':
            n=len(actions)**(2-depth)
            stat['rejection_leaves']+=1; stat['covered_rejections']+=n
            stat['pruned_by_assigned_count'][str(depth)]+=1
            reject({'rows':assigned,'completions':n,'failure':data}); return
        if outcome=='pass':
            # If a branch is never needed, enumerate its concrete completions.
            pending=next((b for b in (0,1) if assigned[b] is None),None)
            if pending is None:
                stat['survivors']+=1; accept(pf.new.copy()); return
            data=pending
        assert data in (0,1) and pf.new[pf.keep,data] is None
        for a in actions:
            pf.new[pf.keep,data]=a; walk()
        pf.new[pf.keep,data]=None
    try:
        walk(); stat['status']='COMPLETE'
        assert stat['covered_rejections']+stat['survivors']==stat['expected_complete_tables']
    except Deadline: stat['status']='INCOMPLETE_DEADLINE'
    return stat

def controls():
    old={(0,0):(0,1,1),(0,1):(1,1,2),(1,0):(0,1,3),(1,1):(1,1,3),
         (2,0):(0,1,4),(2,1):(1,1,4),(4,0):(0,-1,5),(4,1):(1,-1,5),
         (5,0):(0,1,3),(5,1):(1,1,3),(3,0):(0,1,3),(3,1):(1,1,254)}
    radius=3; fuel=97; inv=checker.domain(old,0,radius)
    pf=PartialFilter(old,inv,1,2,radius,fuel)
    actions=list(itertools.product((0,1),(-1,1),[0,1,3,4,5,254]))
    hits=[]; rejected=[]
    stat=synthesize(pf,actions,time.monotonic()+20,rejected.append,
                    lambda n:hits.append((n[1,0],n[1,1])))
    assert stat['status']=='COMPLETE'
    exhaustive=[]; cache={}
    for a0,a1 in itertools.product(actions,repeat=2):
        pf.new[1,0]=a0;pf.new[1,1]=a1
        fail=shared.local_filter(old,pf.new,inv,1,2,cache,fuel,radius)
        direct,_=pf.check()
        assert (direct=='pass')==(fail is None)
        if fail is None: exhaustive.append((a0,a1))
    assert sorted(hits)==sorted(exhaustive) and ((0,1,3),(1,1,3)) in hits
    pf.new[1,0]=(0,1,3);pf.new[1,1]=(1,1,3)
    good=checker.check(old,pf.new,0,0,1,2,radius,fuel,inv)
    pf.new[1,0]=(0,1,254)
    try: checker.check(old,pf.new,0,0,1,2,radius,fuel,inv)
    except ValueError as exc: bad=str(exc)
    else: raise AssertionError('Negative control accepted')
    return {'status':'PASS','all_complete_tables':len(actions)**2,'survivors':len(hits),
            'synthesis':stat,'independent_positive':good,'independent_negative':bad,
            'scope':'Exact agreement with exhaustive prior filter on all 576 synthetic tables; independent known 3/1 merge and early-halt negative control only.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seconds',type=int,default=110)
    ap.add_argument('--pairs',default='66:198')
    a=ap.parse_args(); assert __debug__ and 1<=a.seconds<=110
    a.output.mkdir(parents=True,exist_ok=False)
    paths=[Path(__file__),P/'search_v3.py',Path(checker.__file__),P/'inputs.json']
    paths += [(P/d['path']).resolve() for d in INPUTS['seeds']]
    pins={str(p):sha(p) for p in paths}
    for d in INPUTS['seeds']+[INPUTS['universal_checker']]:
        assert sha((P/d['path']).resolve())==d['sha256']
    for p in paths: (a.output/p.name).write_bytes(p.read_bytes())
    dump(a.output/'controls.json',controls())
    pairs=[tuple(map(int,p.split(':'))) for p in a.pairs.split(',')]
    assert len(pairs)==len(set(pairs)) and all(x!=y and x!=254 and y!=254 for x,y in pairs)
    started=time.monotonic(); deadline=started+a.seconds; results=[]; hits=[]; stopped=False
    with gzip.open(a.output/'rejections.jsonl.gz','wt') as log:
        for sd in INPUTS['seeds']:
            old,start=checker.read((P/sd['path']).resolve()); inv=checker.domain(old,start,7)
            for keep,drop in pairs:
                pf=PartialFilter(old,inv,keep,drop,7,97)
                actions=list(itertools.product((0,1),(-1,1),sorted({q for q,b in pf.new}|{254})))
                assert len(actions)==876
                def reject(record):
                    log.write(json.dumps({'seed':sd['name'],'keep':keep,'drop':drop,**record},separators=(',',':'))+'\n')
                def accept(n):
                    hid=len(hits); out=a.output/f'hit-{hid:03d}';out.mkdir()
                    ns=keep if start==drop else start
                    (out/'candidate.native.tm').write_bytes(shared.encode(n,ns))
                    try:
                        proof=checker.check(old,n,start,ns,keep,drop,7,97)
                        bad=n.copy();bad[ns,0]=(0,1,254)
                        try: checker.check(old,bad,start,ns,keep,drop,7,97)
                        except ValueError as exc: proof['negative_control']={'status':'REJECTED','reason':str(exc)}
                        else: raise ValueError('Negative initial-halt control accepted')
                    except ValueError as exc: proof={'status':'INDEPENDENT_CHECKER_REJECTED','reason':str(exc)}
                    dump(out/'proof.json',proof)
                    hits.append({'seed':sd['name'],'keep':keep,'drop':drop,'rows':[n[keep,0],n[keep,1]],'proof':str(out/'proof.json'),'status':proof['status']})
                    print('HIT',json.dumps(hits[-1]),flush=True)
                    if len(hits)>=4: raise Deadline()
                stat=synthesize(pf,actions,deadline,reject,accept)
                stat.update(seed=sd['name'],keep=keep,drop=drop)
                results.append(stat);print('PAIR',json.dumps(stat),flush=True)
                if stat['status']!='COMPLETE':stopped=True;break
            if stopped:break
    assert all(sha(Path(p))==h for p,h in pins.items())
    result={'status':'INCOMPLETE_LIMIT' if stopped else 'COMPLETE_BOUNDED_SEARCH','pairs':pairs,
            'elapsed_seconds':time.monotonic()-started,'shared_wall_seconds':a.seconds,
            'results':results,'hits':hits,'source_pins':pins,'rejections_sha256':sha(a.output/'rejections.jsonl.gz'),
            'scope':'All independent write/direction/remaining-target choices for both merged rows of specified pairs, on both seeds. All other rows mapped unchanged. Radius7/fuel97 all-initial-tape filter. Rejection before an unassigned action discards all its completions. Finite failures are not semantic counterexamples or lower bounds; checker successes alone certify relative halting equivalence.'}
    dump(a.output/'result.json',result);print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
