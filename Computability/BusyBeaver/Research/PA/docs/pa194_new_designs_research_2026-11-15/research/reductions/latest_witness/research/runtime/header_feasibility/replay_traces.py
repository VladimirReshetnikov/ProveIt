#!/usr/bin/env python3
"""Independently replay finite rejection traces for the fixed 193 runtime core."""
from pathlib import Path
import argparse, collections, hashlib, json, sys

def main():
    p=argparse.ArgumentParser();p.add_argument('packet',type=Path);a=p.parse_args()
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
    rows={}
    for line in (a.packet/'runtime193.native.tm').read_text().splitlines():
        q,b,w,d,t=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
    states={q for q,b in rows};assert len(states)==193 and len(rows)==386
    assert {t for w,d,t in rows.values()}-states=={254}
    reports=json.loads((a.packet/'runtime193_blank_traces.json').read_text())
    assert len(reports)==193 and {r['start'] for r in reports}==states
    counts=collections.Counter();maxsteps=boundary_visits=maximum_boundary_ones=maximum_support_span=0
    for r in reports:
        q=r['start'];head=0;ones=set();boundaries=0;boundary_ones=span=0
        for row in r['trace']:
            assert row[:3]==[q,head,int(head in ones)]
            assert tuple(row[3:])==rows[q,int(head in ones)]
            if q==84:boundaries+=1;boundary_ones=max(boundary_ones,len(ones))
            span=max(span,max(ones)-min(ones)+1 if ones else 0)
            w,d,q=row[3:];(ones.add if w else ones.discard)(head);head+=d
        if q==84:boundaries+=1;boundary_ones=max(boundary_ones,len(ones))
        span=max(span,max(ones)-min(ones)+1 if ones else 0)
        assert (q,head,sorted(ones))==(r['q'],r['head'],r['ones'])
        assert len(r['trace'])==r['steps']
        assert (boundaries,boundary_ones,span)==(r['boundary_visits'],r['maximum_boundary_ones'],r['maximum_preterminal_support_span'])
        if r['status']=='HALT':assert q==254
        else:
            assert r['status']=='RAY' and head not in ones and q!=84
            w,d,t=rows[q,0];assert t==q
            assert not ones or d<0 and head<min(ones) or d>0 and head>max(ones)
            # Each further step reads a fresh exterior zero, writes behind the
            # head, and stays in q. Hence the control never returns to84.
        counts[r['status']]+=1;maxsteps=max(maxsteps,r['steps']);boundary_visits+=boundaries
        maximum_boundary_ones=max(maximum_boundary_ones,boundary_ones);maximum_support_span=max(maximum_support_span,span)
    assert counts=={'HALT':2,'RAY':191} and maxsteps==93
    assert boundary_visits==10 and maximum_boundary_ones==4 and maximum_support_span==8
    assert maximum_boundary_ones<12 # Two markers plus10 nonempty unary blocks.
    result=dict(status='PASS',working_controls=193,blank_starts=193,counts=dict(counts),maximum_trace_steps=maxsteps,boundary_visits=boundary_visits,maximum_boundary_ones=maximum_boundary_ones,maximum_preterminal_support_span=maximum_support_span,minimum_ones_in_any_canonical_frame=12,table_sha256=hashlib.sha256((a.packet/'runtime193.native.tm').read_bytes()).hexdigest(),scope='Fixed table, all blank start controls. All possible boundary visits are covered. No canonical frame at any header or source site is reached. No statement about other bootstrap rewrites or arbitrary 193-state machines.')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
