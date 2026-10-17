#!/usr/bin/env python3
"""Diagnose complete plain-box cutpoints in recorded rejected binary folds.

This is a bounded symbolic trace diagnostic, not a loop certificate or a
proof that a mutation is impossible. It uses the inherited literal/affine
executor unchanged except for a read-only observer inserted by AST. Unknown
decrement guards can either stop the trace or select the positive branch by
explicitly intersecting its symbolic input interval. A selected branch does
not certify the complementary inputs.
"""
from __future__ import annotations
import argparse, ast, copy, hashlib, inspect, json, sys, time
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'binary_experiments'))
sys.path.insert(0,str(ROOT/'compiler_experiments'))
import common as c
import multieffect as effects
import reference_block_folds as source

ACTIVE=None

class StopTrace(Exception):
    def __init__(self,kind,record):self.kind=kind;self.record=record

def _initial():
    if ACTIVE.initial is not None:return copy.deepcopy(ACTIVE.initial)
    pc=ACTIVE.pc
    return '96',False,[('b',1)],[('b',int(b)) for b in pc]+[
        ('r',0,1,40-len(pc)),('b',1),('box',('plain',None))]

def _observe(q,onleft,left,right,literal_steps,rule_count):
    ACTIVE.observe(q,onleft,left,right,literal_steps,rule_count)

def _oracle(q,branch,state):return ACTIVE.oracle(q,branch,state)

def make_executor():
    tree=ast.parse(inspect.getsource(c.strict.run));fn=tree.body[0]
    assert isinstance(fn,ast.FunctionDef) and fn.name=='run'
    assert [x.targets[0].id for x in fn.body[:4]]==['q','onleft','left','right']
    fn.body[:4]=ast.parse('q,onleft,left,right=_initial()').body
    loops=[x for x in fn.body if isinstance(x,ast.For)]
    assert len(loops)==1
    loops[0].body[:0]=ast.parse('_observe(q,onleft,left,right,literal_steps,rule_count)').body
    namespace=dict(c.strict.__dict__)
    namespace.update(_initial=_initial,_observe=_observe,oracle=_oracle)
    exec(compile(ast.fix_missing_locations(tree),'<observed original strict.run>','exec'),namespace)
    return namespace['run']

RUN=make_executor()

def erased_shape(q,onleft,left,right):
    if not right or right[-1][0]!='box' or right[-1][1][0]!='plain':return None
    l,r=c.strict.canon(left,right)
    return q,onleft,l,r[:-1]+(('box',('plain',None)),)

class Analyzer:
    def __init__(self,table,index,constraints,target,policy='stop',initial=None,cutpoint_stop=True):
        self.table=table;self.index=index;self.pc=c.CASES[index][0]
        self.branch=c.CASES[index][4];self.target=target
        self.intervals=[list(x) for x in constraints]
        self.policy=policy;self.initial=initial;self.cutpoint_stop=cutpoint_stop
        self.seen={};self.guards=[];self.box_events=[];self.literal=0;self.observations=0
        self.dispatches=0;self.plain_boundaries=0;self.selected_guards=0
        self.first_recurrence=None
    def oracle(self,q,branch,state):
        def bounds(_branch,r):return self.intervals[r]
        effects.bounds=bounds
        if state[0]=='mark' and q=='43':
            r=state[1];delta=effects.vector(state[2] if len(state)==3 else None)
            lo,hi=self.intervals[r];value_lo=lo+delta[r]
            assert value_lo>=0
            selected=False
            if hi is not None and hi+delta[r]==0:zero=True
            elif value_lo>=1:zero=False
            elif self.policy=='positive':
                self.intervals[r][0]=1-delta[r]
                assert hi is None or self.intervals[r][0]<=hi
                zero=False;selected=True;self.selected_guards+=1
            else:
                raise AssertionError(('undetermined sequential guard',r,delta,branch))
            self.guards.append({'register':r,'zero':zero,'offset':list(delta),
                                'selected':selected,'initial_bounds':[list(x) for x in self.intervals]})
        answer=effects.oracle(q,branch,state)
        if answer is not None:
            self.box_events.append({'entry':q,'before':state,'exit':answer[0],'after':answer[1]})
        return answer
    def observe(self,q,onleft,left,right,literal_steps,rule_count):
        self.literal=literal_steps;self.observations+=1
        # Do not preempt a legitimate completed source target.
        if literal_steps>0 and q=='96' and not onleft and c.strict.canon(left,right)==self.target:return
        dispatch=q=='96' and not onleft
        boundary=len(right)==1 and right[0][0]=='box'
        if not (dispatch or boundary):return
        key=erased_shape(q,onleft,left,right)
        if key is None:return
        self.dispatches+=dispatch;self.plain_boundaries+=boundary
        delta=effects.vector(right[-1][1][1])
        current={'delta':list(delta),'literal_steps':literal_steps,
                 'rules':dict(rule_count),'guard_index':len(self.guards),
                 'box_index':len(self.box_events),'symbolic_iteration':self.observations,
                 'initial_bounds':[list(x) for x in self.intervals],
                 'configuration':(q,onleft,copy.deepcopy(left),copy.deepcopy(right))}
        before=self.seen.get(key)
        if before is None:self.seen[key]=current;return
        if literal_steps<=before['literal_steps']:return
        shift=tuple(b-a for a,b in zip(before['delta'],delta))
        negatives=[i for i,x in enumerate(shift) if x<0]
        eligible=len(negatives)==1 and shift[negatives[0]]==-1
        kind='countdown_shape' if eligible else 'zero_primary_cycle' if not any(shift) else 'other_primary_cycle'
        record={'kind':kind,'shape':key,'shift':shift,
                'counter':negatives[0] if eligible else None,
                'before':before,'after':current,
                'guards':self.guards[before['guard_index']:],
                'box_events':self.box_events[before['box_index']:],
                'positive_literal_steps':literal_steps-before['literal_steps']}
        if self.first_recurrence is None:self.first_recurrence=record
        if self.cutpoint_stop:raise StopTrace(kind,record)
    def run(self,fuel=1000):
        global ACTIVE
        ACTIVE=self
        try:
            rules,literal=RUN(self.table,self.pc,self.branch,self.target,
                              halt=c.CASES[self.index][1]=='CH',fuel=fuel)
            kind='source_target';record={'rules':dict(rules),'literal_steps':literal}
        except StopTrace as e:kind=e.kind;record=e.record
        except (AssertionError,KeyError) as e:
            kind='blocked';record={'error':str(e)}
        return {'status':kind,'record':record,'observations':self.observations,
                'literal_steps':self.literal,'plain_boundary_observations':self.plain_boundaries,
                'dispatch_observations':self.dispatches,'selected_positive_guards':self.selected_guards,
                'final_initial_bounds':self.intervals}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--journal',type=Path,default=ROOT/'loop_experiments/final/journal.jsonl')
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--policy',choices=('stop','positive'),default='positive')
    p.add_argument('--fuel',type=int,default=1000)
    p.add_argument('--limit',type=int,default=None)
    p.add_argument('--examples',type=int,default=3)
    a=p.parse_args();a.journal=a.journal.resolve();a.output.mkdir(parents=True,exist_ok=True);start=time.monotonic()
    frontiers,constraints,enabled,_=source.configure(64)
    rows=[json.loads(x) for x in a.journal.read_text().splitlines()]
    selected=[r for r in rows if r['failure'] and (r['failure'][1]=='symbolic fuel exhausted'
                 or 'undetermined sequential guard' in r['failure'][1])]
    if a.limit is not None:selected=selected[:a.limit]
    counts=Counter();errors=Counter();examples={};candidates=[];total_observations=0
    with (a.output/'journal.jsonl').open('w') as out:
        for n,r in enumerate(selected):
            index=r['failure'][0]
            analyzer=Analyzer(c.fold(c.T,str(r['deleted']),str(r['replacement'])),index,
                              constraints[index],frontiers[index],a.policy)
            result=analyzer.run(a.fuel);counts[result['status']]+=1
            total_observations+=result['observations']
            if result['status']=='blocked':errors[result['record']['error'].split("'",2)[1]
                if "'" in result['record']['error'] else result['record']['error']]+=1
            identity={'deleted':r['deleted'],'replacement':r['replacement'],'case':index,
                      'path':c.CASES[index][0],'original_failure':r['failure'][1]}
            compact={**identity,**{k:v for k,v in result.items() if k!='record'}}
            if result['status'] in ('countdown_shape','zero_primary_cycle','other_primary_cycle'):
                compact['shift']=result['record']['shift']
                compact['cycle_literal_steps']=result['record']['positive_literal_steps']
            else:compact['record']=result['record']
            out.write(json.dumps(compact,separators=(',',':'))+'\n')
            bucket=examples.setdefault(result['status'],[])
            if len(bucket)<a.examples:bucket.append({**identity,**result})
            if result['status']=='countdown_shape':
                candidates.append({**identity,**result})
                if len(candidates)<=3:print('COUNTDOWN',identity,result['record']['shift'],flush=True)
            if (n+1)%5000==0:print('PROGRESS',n+1,dict(counts),round(time.monotonic()-start,2),flush=True)
    journal_name=str(a.journal.relative_to(ROOT)) if a.journal.is_relative_to(ROOT) else str(a.journal)
    summary={'scope':__doc__,'input_journal':journal_name,
             'input_journal_sha256':hashlib.sha256(a.journal.read_bytes()).hexdigest(),
             'policy':a.policy,'fuel':a.fuel,'selected':len(selected),'counts':dict(counts),
             'blocked_reasons':dict(errors),'symbolic_observations':total_observations,
             'examples':examples,'countdown_candidates':candidates,
             'journal_sha256':hashlib.sha256((a.output/'journal.jsonl').read_bytes()).hexdigest(),
             'seconds':time.monotonic()-start}
    (a.output/'results.json').write_text(json.dumps(summary,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k not in ('scope','examples','countdown_candidates')}),flush=True)

if __name__=='__main__':main()
