#!/usr/bin/env python3
"""Indexed exact strict-schema + all-natural partial-injection validator.
No compiler code imported and no CA gates allocated. Guard AST is finite JSON.
"""
import json,hashlib
from pathlib import Path
from collections import defaultdict,Counter
ROOT=Path(__file__).resolve().parent

def require(ok,msg):
    if not ok:raise ValueError(msg)
def obj(x,keys):require(type(x) is dict and all(type(k) is str for k in x) and set(x)==set(keys),'Object keys/types')
def integer(x):require(type(x) is int,'Exact integer required')
def string(x):require(type(x) is str,'Exact string required')
def nodup(pairs):
    d={}
    for k,v in pairs:require(k not in d,'Duplicate JSON key');d[k]=v
    return d

def validate(s):
    obj(s,['schema','controls','start','halt','class_cut','branches']);string(s['schema']);require(s['schema']=='reversible-two-counter-v1','Schema')
    require(type(s['controls']) is list and type(s['branches']) is list,'Lists required')
    for q in s['controls']:string(q)
    states=set(s['controls']);require(len(states)==len(s['controls']),'Duplicate control');string(s['start']);string(s['halt']);require(s['start'] in states and s['halt'] in states,'Start/halt')
    J=s['class_cut'];integer(J);require(J>=0,'Nonnegative cut')
    names=set();outs=defaultdict(list);ins=defaultdict(list);hist=Counter()
    def parse(g,idx,delta):
        require(type(g) is dict and 'op' in g,'Guard object');op=g['op'];string(op)
        if op=='true':obj(g,['op'])
        elif op in ('eq','gt'):
            obj(g,['op','counter','value']);i=g['counter'];k=g['value'];integer(i);integer(k);require(i in (0,1) and k>=0,'Guard atom');require(k<=J and k+(delta if i==idx else 0)<=J,'Cut')
        elif op in ('and','or'):
            obj(g,['op','args']);require(type(g['args']) is list,'Guard list')
            for h in g['args']:parse(h,idx,delta)
        elif op=='not':obj(g,['op','arg']);parse(g['arg'],idx,delta)
        else:raise ValueError('Guard operator')
    def ev(g,c):
        op=g['op']
        if op=='true':return True
        if op=='eq':return c[g['counter']]==g['value']
        if op=='gt':return c[g['counter']]>g['value']
        if op=='not':return not ev(g['arg'],c)
        return all(ev(h,c) for h in g['args']) if op=='and' else any(ev(h,c) for h in g['args'])
    for e in s['branches']:
        obj(e,['name','source','target','side','delta','guard'])
        for key in ('name','source','target'):string(e[key])
        require(e['name'] not in names,'Duplicate branch');names.add(e['name']);require(e['source'] in states and e['target'] in states,'Unknown target');require(e['source']!=s['halt'],'Halt outgoing')
        d=e['delta'];side=e['side'];integer(d);integer(side);require(d in (-1,0,1) and side in (-1,1),'Action');idx=(side+1)//2;parse(e['guard'],idx,d)
        domain=[];image=[]
        for a in range(J+2):
            for b in range(J+2):
                c=[a,b];ok=ev(e['guard'],c);require(not ok or c[idx]+d>=0,'Negative image');domain.append(ok);c[idx]-=d;image.append(min(c)>=0 and ev(e['guard'],c))
        outs[e['source']].append(domain);ins[e['target']].append(image);hist[d]+=1
    for maps,kind in [(outs,'domain'),(ins,'image')]:
        for q,ts in maps.items():
            require(all(sum(t[j] for t in ts)<=1 for j in range((J+2)**2)),kind+' overlap at '+q)
    require(not ins[s['start']],'Initial control has incoming row')
    return dict(controls=len(states),branches=len(names),class_cut=J,class_pairs=(J+2)**2,moving_rows=hist[1]+hist[-1],zero_update_rows=hist[0],no_incoming_start=True,no_outgoing_halt=True)

if __name__=='__main__':
    data=(ROOT/'source.json').read_bytes();s=json.loads(data,object_pairs_hook=nodup);result=validate(s)
    result=dict(status='passed',source_sha256=hashlib.sha256(data).hexdigest(),checks=result,scope='All natural counter pairs via exact finite source/image classes; independent indexed validator, not execution of eager compile_source')
    (ROOT/'schema-injection-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
