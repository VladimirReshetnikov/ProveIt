#!/usr/bin/env python3
"""Test finite positive reference blocks instead of a single reference step.

Every accepted target is reached by 1..block_limit exact source instructions
from the current guarded source site. The source arithmetic along that block
has an affine effect decided uniformly by the current unbounded phase masks.
Complete physical frames and nine primary effects are compared; spares retain
the existential valid-suffix contract of multieffect.py. This is an executable
ordinary certificate search, not a kernel proof or a smaller-machine claim.
"""
from __future__ import annotations
import argparse
from collections import Counter,defaultdict
from functools import lru_cache
import hashlib,json,sys,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'binary_experiments'))
sys.path.insert(0,str(ROOT/'upstream/Computability/BusyBeaver/Research/ZFC'))
import common as c
import multieffect as effects
import permutation252_phase_analysis as phase

BOX_STATES={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
PROTECTED={(str(q),b) for q in BOX_STATES for b in (0,1)}-{('3',0)}
CURRENT_BOUNDS=None

def bounds(branch,r):
    assert CURRENT_BOUNDS is not None
    return CURRENT_BOUNDS[r]

def mask_bounds(mask):
    assert mask
    lo=0 if mask&1 else 1 if mask&2 else 2
    hi=None if mask&4 else 1 if mask&2 else 0
    return lo,hi

class Frontier:
    def __init__(self,frames,metadata,halting_source_steps=None):
        self.frames=frozenset(frames)
        self.metadata=metadata
        self.halting_source_steps=halting_source_steps
        self.matched=None
    def __eq__(self,other):
        if isinstance(other,tuple) and other in self.frames:
            self.matched=other
            return True
        return False

def configure(limit):
    raw=(ROOT/'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==phase.PROG_SHA
    sites,cases,targets,first=phase.program_graph(raw)
    values,enabled,pops,edges=phase.phase_analysis(sites,cases,targets,first)
    assert len(cases)==len(c.CASES)
    lookup={p:i for i,(p,op,r) in enumerate(sites)}
    @lru_cache(None)
    def decode(pc):
        q,path=0,''
        while True:
            bit=pc[len(path)] if len(path)<len(pc) else '0';path+=bit
            op,*args=c.NODES[q][int(bit)].split()
            if op=='CN':q=int(args[0]);continue
            assert '1' not in pc[len(path):]
            return path,op,int(args[0]) if args else None
    frontiers=[];constraints=[];reason_counts=Counter()
    for i,(site,path,op,r,zero) in enumerate(cases):
        assert (path,op,r,zero)==c.CASES[i][:4]
        if not enabled[i]:frontiers.append(None);constraints.append(None);continue
        masks=list(values[site])
        if op=='CD':masks[r]=1 if zero else masks[r]&~1
        physical=[None]*9
        for logical,physical_id in enumerate(c.PHYS):physical[physical_id]=mask_bounds(masks[logical])
        constraints.append(tuple(physical))
        delta=[0]*9;gap=40;pc=path;frames={};records=[];seen=set();halting_source_steps=None
        first_op=True
        for reference_steps in range(1,limit+1):
            consumed,kind,register=decode(pc)
            positive=False
            if kind=='CH':
                reason_counts['halt_frontier']+=1
                halting_source_steps=reference_steps
                break
            if kind in ('CI','CD'):
                pr=c.PHYS[register];lo,hi=physical[pr]
                assert lo+delta[pr]>=0
                if kind=='CI':delta[pr]+=1
                elif hi is not None and hi+delta[pr]==0:positive=False
                elif lo+delta[pr]>=1:positive=True;delta[pr]-=1
                else:reason_counts['unknown_guard']+=1;break
            if kind=='CI' or kind=='CD' and positive:nxt=c.inc(consumed)
            elif kind=='CD':nxt=c.inc(c.strip(consumed,'0',1))
            elif kind=='CB':nxt=c.inc(c.strip(consumed,'0',register))
            elif kind=='CC':nxt=c.strip(consumed,'1',register)
            else:raise AssertionError(kind)
            if nxt is None:gap+=1;nxt=''
            pc=nxt.rstrip('0')
            right=[('b',int(b)) for b in pc]+[('r',0,1,gap-len(pc)),('b',1),('box',('plain',effects.encode(tuple(delta))))]
            target=c.strict.canon([('b',1)],right)
            if first_op:
                assert target==c.CASES[i][5],('first_step',i)
                first_op=False
            record={'source_steps':reference_steps,'pc':pc,'gap_constant':gap,'primary_delta':delta.copy(),
                    'next_source_leaf':list(decode(pc))}
            frames.setdefault(target,record);records.append(record)
            signature=(pc,gap,tuple(delta))
            if signature in seen:reason_counts['repeated_state']+=1;break
            seen.add(signature)
        else:reason_counts['block_limit']+=1
        frontiers.append(Frontier(frames,records,halting_source_steps))
    effects.install();effects.bounds=bounds
    return frontiers,constraints,enabled,reason_counts

class Tracking(dict):
    def __init__(self,rows):super().__init__(rows);self.used=set()
    def __getitem__(self,key):self.used.add(key);return super().__getitem__(key)

def check_one(table,i,frontiers,constraints,fuel):
    global CURRENT_BOUNDS
    CURRENT_BOUNDS=constraints[i]
    p,op,r,z,branch,target=c.CASES[i];frontier=frontiers[i]
    try:
        frontier.matched=None
        rules,literal=c.strict.run(table,p,branch,frontier,halt=op=='CH',fuel=fuel)
        assert literal>0
        matched_steps=(None if frontier.matched is None else next(rec['source_steps'] for rec in frontier.metadata
            if c.strict.canon([('b',1)],[('b',int(b)) for b in rec['pc']]+[('r',0,1,rec['gap_constant']-len(rec['pc'])),('b',1),('box',('plain',effects.encode(tuple(rec['primary_delta']))))])==frontier.matched))
        return True,sum(rules.values()),matched_steps,None
    except KeyError as error:
        # strict.run's nonhalting mode reaches the actual terminal after its
        # final write/move, then tries to read a row of254. Since the initial
        # state is96 and no box oracle targets254, this certifies positive
        # literal binary progress. Accept it only with an exact positive
        # source prefix ending in CH; unknown/missing nonterminal rows reject.
        key=error.args[0] if error.args else None
        if key in (('254',0),('254',1)) and frontier.halting_source_steps is not None:
            return True,0,frontier.halting_source_steps,None
        return False,0,None,str(error)
    except AssertionError as error:return False,0,None,str(error)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--block-limit',type=int,default=64)
    p.add_argument('--fuel',type=int,default=1000)
    p.add_argument('--deleted',nargs='*',default=None)
    p.add_argument('--seconds',type=float,default=600)
    a=p.parse_args();start=time.monotonic();a.output.mkdir(parents=True,exist_ok=True)
    frontiers,constraints,enabled,end_reasons=configure(a.block_limit)
    admitted=[i for i,x in enumerate(enabled) if x];usage=defaultdict(list);baseline_steps=Counter()
    for i in admitted:
        traced=Tracking(c.T);ok,cost,steps,reason=check_one(traced,i,frontiers,constraints,a.fuel)
        assert ok,('baseline',i,reason)
        baseline_steps[steps]+=1
        for q in {q for q,b in traced.used}:usage[q].append((cost,i))
    for q in usage:usage[q].sort()
    states=sorted({q for q,b in c.T},key=int)
    protected_targets={c.T[k][2] for k in PROTECTED}
    eligible=[q for q in states if q not in protected_targets|{'96'} and all((q,b) not in PROTECTED for b in (0,1))]
    assert len(eligible)==221
    if a.deleted is not None:eligible=[q for q in eligible if q in a.deleted]
    results={'scope':__doc__,'block_limit':a.block_limit,'symbolic_fuel':a.fuel,
             'baseline_cases':len(admitted),'baseline_matched_source_steps':dict(baseline_steps),
             'frontier_stop_reasons':dict(end_reasons),'source_target_count_histogram':dict(Counter(len(f.frames) for f in frontiers if f is not None)),
             'planned':len(eligible)*251,'completed':0,'checks':0,'multi_step_matches':0,
             'survivors':[],'rejections':Counter(),'failures':[],'completed_all':False}
    print(json.dumps({k:v for k,v in results.items() if k not in ('scope','failures')}),flush=True)
    stopped=False
    with (a.output/'journal.jsonl').open('w') as journal:
        for n,dead in enumerate(eligible):
            for replacement in states:
                if replacement==dead:continue
                if time.monotonic()-start>a.seconds:stopped=True;break
                table=c.fold(c.T,dead,replacement)
                assert all(table[k]==c.T[k] for k in PROTECTED)
                failure=None;long_matches=[]
                ids=[i for cost,i in usage[dead]]
                for i in ids:
                    ok,cost,steps,reason=check_one(table,i,frontiers,constraints,a.fuel);results['checks']+=1
                    if not ok:failure=[i,reason];break
                    if steps is not None and steps>1:long_matches.append([i,steps]);results['multi_step_matches']+=1
                if failure is None:
                    for i in admitted:
                        ok,cost,steps,reason=check_one(table,i,frontiers,constraints,a.fuel);results['checks']+=1
                        if not ok:failure=[i,reason];break
                        if steps is not None and steps>1:long_matches.append([i,steps]);results['multi_step_matches']+=1
                results['completed']+=1
                record={'deleted':int(dead),'replacement':int(replacement),'failure':failure,'long_matches':long_matches}
                journal.write(json.dumps(record)+'\n')
                if failure is None:
                    results['survivors'].append(record)
                    raw='#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1])))
                    (a.output/f'candidate_{dead}_{replacement}.tm').write_text(raw)
                    print('SURVIVOR',dead,replacement,flush=True)
                else:
                    reason=failure[1];results['rejections'][reason.split("'",2)[1] if "'" in reason else reason]+=1
            if n%20==0:print('PROGRESS',n,dead,results['completed'],results['checks'],len(results['survivors']),round(time.monotonic()-start,2),flush=True)
            if stopped:break
    results['completed_all']=not stopped;results['seconds']=time.monotonic()-start
    results['rejections']=dict(results['rejections']);results['macro_counts']=dict(effects.STATS)
    results['journal_sha256']=hashlib.sha256((a.output/'journal.jsonl').read_bytes()).hexdigest()
    (a.output/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({k:v for k,v in results.items() if k not in ('scope','failures','macro_counts')}),flush=True)
if __name__=='__main__':main()
