#!/usr/bin/env python3
"""Universally replay narrow countdown bodies and their separate zero exits.

Each accepted body is checked by the inherited exact literal/scan rules and
unchanged protected box contracts for arbitrary current registers satisfying
an explicitly preserved interval invariant. The final positive iteration is
included. Source comparison requires complete dispatch shape and equality of
all affine primary rows; it is separate from certifying a binary loop.
"""
from __future__ import annotations
import argparse, copy, hashlib, json, sys, time
from collections import Counter
from pathlib import Path
import trace_cutpoints as t

ROOT=t.ROOT;c=t.c;effects=t.effects

def tuples(x):return tuple(tuples(y) for y in x) if isinstance(x,(list,tuple)) else x

def effect_of(state):
    if state[0]=='plain':return effects.vector(state[1])
    assert state[0]=='mark'
    return effects.vector(state[2] if len(state)==3 else None)

def invariant(record):
    """Infer only lower bounds and fixed values on unchanged noncounters."""
    r=record['counter'];d=record['shift'];start=record['before']['delta']
    assert d[r]==-1 and all(x>=0 for i,x in enumerate(d) if i!=r)
    bounds=[[0,None] for _ in range(9)]
    def minimum(i,k):
        if i==r:
            assert 1>=k,('counter requirement excludes last positive iteration',k)
        else:
            bounds[i][0]=max(bounds[i][0],k)
            assert bounds[i][1] is None or bounds[i][0]<=bounds[i][1],('inconsistent invariant',i)
    for event in record['box_events']:
        offset=effect_of(tuples(event['before']))
        for i,x in enumerate(offset):minimum(i,start[i]-x)
    for guard in record['guards']:
        i=guard['register'];prefix=guard['offset'][i]-start[i]
        if guard['zero']:
            assert i!=r,('counter zero guard inside uniform positive cycle',prefix)
            assert d[i]==0,('zero guard on growing register',i,d[i])
            value=-prefix;assert value>=0
            bounds[i][1]=value if bounds[i][1] is None else min(bounds[i][1],value)
            minimum(i,value)
        else:minimum(i,1-prefix)
    for i,(lo,hi) in enumerate(bounds):
        assert lo>=0 and (hi is None or hi>=lo)
        assert i==r or hi is None or d[i]==0
    # J has no lower restriction on the counter: it includes its zero boundary.
    assert bounds[r]==[0,None]
    return bounds

def configuration(record):
    q,onleft,left,right=tuples(record['before']['configuration'])
    assert right[-1][0]=='box' and right[-1][1][0]=='plain'
    return q,onleft,list(left),list(right[:-1]) + [('box',('plain',None))]

def clean_frame(q,onleft,left,right):
    if q!='96' or onleft:return None
    l,r=c.strict.canon(left,right)
    if l!=((1,0,1),) or len(r)<3:return None
    if r[-1][0]!='box' or r[-1][1][0]!='plain':return None
    if r[-2]!=(1,0,1) or r[-3][0:2]!=(0,1):return None
    if any(seg[0] not in (0,1) or seg[1]!=0 for seg in r[:-3]):return None
    pc=''.join(str(seg[0])*seg[2] for seg in r[:-3]);gap=len(pc)+r[-3][2]
    if gap<40:return None
    return {'pc':pc,'gap_constant':gap,'primary_delta':list(effects.vector(r[-1][1][1])),
            'canonical_tape':(l,r)}

class Replay(t.Analyzer):
    def __init__(self,table,index,bounds,initial,mode,key,shift):
        super().__init__(table,index,bounds,(),policy='stop',initial=initial)
        self.mode=mode;self.key=key;self.shift=shift;self.dirty_dispatch=None;self.seen_zero={}
    def observe(self,q,onleft,left,right,literal_steps,rule_count):
        self.literal=literal_steps;self.observations+=1
        key=t.erased_shape(q,onleft,left,right)
        if literal_steps==0:return
        if q=='254':raise t.StopTrace('actual_halt',{'literal_steps':literal_steps})
        if self.mode=='positive':
            if key==self.key:
                delta=effects.vector(right[-1][1][1]);assert delta==self.shift,('body shift mismatch',delta,self.shift)
                raise t.StopTrace('positive_body_verified',{'primary_delta':delta,'literal_steps':literal_steps,
                    'rules':dict(rule_count),'guards':self.guards,'box_events':self.box_events})
        else:
            frame=clean_frame(q,onleft,left,right)
            if frame is not None:
                frame.update(literal_steps=literal_steps,rules=dict(rule_count),guards=self.guards,box_events=self.box_events)
                raise t.StopTrace('clean_zero_exit_verified',frame)
            if key is not None and q=='96' and not onleft:
                if self.dirty_dispatch is None:self.dirty_dispatch=key
            if key is not None and (q=='96' and not onleft or len(right)==1):
                delta=effects.vector(right[-1][1][1]);whole=(key,delta)
                if whole in self.seen_zero and literal_steps>self.seen_zero[whole]:
                    raise t.StopTrace('repeated_zero_exit_configuration',{'shape':key,'primary_delta':delta})
                self.seen_zero.setdefault(whole,literal_steps)

def contained(inner,outer):
    return all(lo>=a and (b is None or hi is not None and hi<=b)
               for (lo,hi),(a,b) in zip(inner,outer))

def reduced_matrix(rows,bounds):
    ans=[]
    for row in rows:
        out=list(row)
        for i,(lo,hi) in enumerate(bounds):
            if hi==lo:out[-1]+=out[i]*lo;out[i]=0
        ans.append(tuple(out))
    return tuple(ans)

def check_one(candidate,original_bounds,fuel):
    record=candidate['record'];identity={k:candidate[k] for k in ('deleted','replacement','case','path')}
    try:J=invariant(record)
    except AssertionError as e:return {**identity,'status':'invariant_rejected','reason':str(e)}
    table=c.fold(c.T,str(candidate['deleted']),str(candidate['replacement']))
    assert all(table[k]==c.T[k] for k in t.source.PROTECTED)
    initial=configuration(record);key=t.erased_shape(*initial);shift=tuples(record['shift']);r=record['counter']
    assert key==tuples(record['shape'])
    positive_bounds=copy.deepcopy(J);positive_bounds[r]=[1,None]
    pos=Replay(table,candidate['case'],positive_bounds,initial,'positive',key,shift).run(fuel)
    result={**identity,'invariant':J,'counter':r,'cycle_shift':shift,'positive_body':pos}
    if pos['status']!='positive_body_verified':result['status']='positive_replay_rejected';return result
    zero_bounds=copy.deepcopy(J);zero_bounds[r]=[0,0]
    zero_replayer=Replay(table,candidate['case'],zero_bounds,initial,'zero',key,shift)
    zero=zero_replayer.run(fuel);result['zero_exit']=zero
    if zero_replayer.dirty_dispatch is not None:result['first_dirty_dispatch']=zero_replayer.dirty_dispatch
    if zero['status']!='clean_zero_exit_verified':result['status']='zero_exit_rejected';return result
    # The rule below is universal for J and preserves the entire interface.
    # Its application to the originally guarded source case needs a valid prefix.
    before=record['before'];start=before['delta']
    current_bounds=[(lo+start[i],None if hi is None else hi+start[i])
                    for i,(lo,hi) in enumerate(original_bounds)]
    coverage=contained(original_bounds,before['initial_bounds']) and contained(current_bounds,J)
    result['prefix_covers_original_case']=coverage
    result['prefix_primary_delta']=start
    output=[];z=zero['record']['primary_delta']
    for i in range(9):
        row=[int(j==i)+shift[i]*int(j==r) for j in range(9)]
        assert all(x>=0 for x in row)
        output.append(row+[start[i]+shift[i]*start[r]+z[i]])
    result['composed_primary_rows']=output
    result['status']='binary_countdown_and_clean_exit_verified'
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--fuel',type=int,default=1000)
    a=p.parse_args();a.input=a.input.resolve();a.output.mkdir(parents=True,exist_ok=True);start=time.monotonic()
    raw=json.loads(a.input.read_text());candidates=raw['countdown_candidates']
    _,constraints,_,_=t.source.configure(64)
    results=[check_one(x,constraints[x['case']],a.fuel) for x in candidates]
    live=[x for x in results if x['status']=='binary_countdown_and_clean_exit_verified']
    sys.path.insert(0,str(ROOT/'loop_experiments'))
    import affine_reference_loops as loops
    reference=loops.raw_targets([x['case'] for x in live]+[2])
    (a.output/'matrix_reference_targets.json').write_text(json.dumps(reference,indent=2)+'\n')
    for x in live:
        bounds=constraints[x['case']];targets=reference['cases'][x['case']]['targets']
        frame=x['zero_exit']['record'];matrix=reduced_matrix(x['composed_primary_rows'],bounds)
        pc_hits=[y for y in targets if y['pc']==frame['pc'] and y['gap_constant']==frame['gap_constant']]
        matches=[y for y in pc_hits if reduced_matrix(y['register_affine_rows'],bounds)==matrix]
        x['matching_pc_gap_source_targets']=len(pc_hits)
        x['matching_full_matrix_source_targets']=matches
    counts=Counter(x['status'] for x in results)
    zero_reasons=Counter(x['zero_exit']['status'] for x in results if x['status']=='zero_exit_rejected')
    survivors=[x for x in live if x['prefix_covers_original_case'] and x['matching_full_matrix_source_targets']]
    input_name=str(a.input.relative_to(ROOT)) if a.input.is_relative_to(ROOT) else str(a.input)
    summary={'scope':__doc__,'input':input_name,
             'input_sha256':hashlib.sha256(a.input.read_bytes()).hexdigest(),
             'fuel':a.fuel,'candidates':len(candidates),'counts':dict(counts),
             'zero_exit_rejection_counts':dict(zero_reasons),
             'prefix_coverage_count':sum(x['prefix_covers_original_case'] for x in live),
             'complete_source_match_count':sum(bool(x['matching_full_matrix_source_targets']) for x in live),
             'first_contract_survivors':survivors,'results':results,
             'seconds':time.monotonic()-start}
    (a.output/'results.json').write_text(json.dumps(summary,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k not in ('scope','results','first_contract_survivors')}),flush=True)
    if survivors:print('FIRST CONTRACT SURVIVORS',[(x['deleted'],x['replacement'],x['case']) for x in survivors],flush=True)

if __name__=='__main__':main()
