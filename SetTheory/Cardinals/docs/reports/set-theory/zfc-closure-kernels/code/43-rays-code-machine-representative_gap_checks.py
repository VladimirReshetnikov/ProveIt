#!/usr/bin/env python3
"""Literal finite traces for selected short-gap contracts.

These prepared-tape examples compare the first subsequent complete dispatch
frame with the stipulated instruction target.  A mismatch is an obstruction
to the usual per-instruction interpretation, not a nonhalting result, and
does not exclude some later accidental visit to the target configuration.
Uses the attributed source35 parser/encoder and independently steps every
binary table row (no box summaries in the literal traces).
"""
from pathlib import Path
import argparse, collections, hashlib, json
from exact_gap_audit import load_source,HERE

def trace(mod,c,g,regs,spares,limit=20000):
    p=c['path'];op=c['op'];r=c['physical'];branch=c['branch']
    ns=mod.executor();p2,_=mod.expected(ns,p,op,r,branch,g)
    newregs=regs.copy();newspares=spares.copy();newg=g;newh=0
    if op=='CI':newregs[r]+=1
    elif op=='CD' and branch=='p':newregs[r]-=1;newspares.append(0)
    if p2 is None:p2='';newg+=1;newh=-1
    initial=mod.paint(p,g,regs,spares);ones=initial.copy()
    target={x+newh for x in mod.paint(p2,newg,newregs,newspares)}
    table=mod.rows();q=96;h=0;visits=0;digest=hashlib.sha256()
    expected={'p':p2,'gap':newg,'regs':newregs,'spares':newspares,'head':newh,'ones':sorted(target)}
    base={'case':c['case'],'gap':g,'op':op,'physical_register':r,'branch':branch,
          'input':{'p':p,'regs':regs,'spares':spares,'ones':sorted(initial)},'expected':expected}
    for t in range(limit+1):
        if t and q==96:
            visits+=1
            parsed=mod.parse_frame({'t':t,'h':h,'relative':sorted(x-h for x in ones)})
            if h==newh and ones==target:
                return base|{'reason':'exact_target','microsteps':t,'dispatch_visits':visits,
                             'actual':parsed,'actual_ones':sorted(ones),'trace_sha256':digest.hexdigest()}
            if parsed is not None:
                return base|{'reason':'different_complete_frame','microsteps':t,'dispatch_visits':visits,
                             'actual':parsed,'actual_ones':sorted(ones),'trace_sha256':digest.hexdigest()}
        if q==254 or t==limit:
            return base|{'reason':'halt' if q==254 else 'fuel','microsteps':t,'q':q,'h':h,
                         'actual_ones':sorted(ones),'trace_sha256':digest.hexdigest()}
        bit=int(h in ones);w,d,q2=table[q,bit]
        digest.update(f'{q},{h},{bit},{w},{d},{q2}\n'.encode())
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1;q=q2

def main():
    if not __debug__:raise SystemExit('Run without -O.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source35',type=Path,default=HERE.parent/'source35_runtime252_short_gap.py')
    ap.add_argument('--upstream',type=Path,default=HERE/'upstream')
    ap.add_argument('--census',type=Path,default=HERE/'runtime252_exact_gaps.json')
    ap.add_argument('--output',type=Path,default=HERE/'runtime252_representative_gaps.json')
    a=ap.parse_args();mod=load_source(a.source35,a.upstream)
    census=json.loads(a.census.read_text())
    selected=[]
    for gap in (32,35):
        cases=next(x['cases'] for x in census['gaps'] if x['gap']==gap)
        reasons=['box touched in state 73','box touched in state 43','box touched in state 42'] if gap==32 else ['box touched in state 73']
        for reason in reasons:selected.append((gap,next(x for x in cases if x['reason']==reason)))
    traces=[]
    for gap,c in selected:
        for n in (0,1,2,4):
            regs=[n]*9
            if c['op']=='CD':regs[c['physical']]=0 if c['branch']=='z' else max(1,n)
            traces.append(trace(mod,c,gap,regs,[0,1,0]))
        traces.append(trace(mod,c,36,[1]*9 if c['op']!='CD' else [0 if i==c['physical'] else 1 for i in range(9)],[0,1,0]))
    # Reproduce source35's prior affine false alarm on the actual reached data.
    start=mod.blank_checkpoint();affine=mod.accelerate(start,1000,exact_gap=False)
    assert affine['reason']=='failed_local_contract' and affine['state']['rm_step']==641
    old=mod.literal_failure(affine)
    assert old['reason']=='literal_correct_instruction' and old['microsteps']==2794
    result={'scope':__doc__,'prepared_traces':traces,'prior_source35_affine_false_alarm':{
                'rm_step':641,'literal_microsteps':2794,'reason':old['reason'],
                'state':affine['state']},
            'counts':dict(collections.Counter(x['reason'] for x in traces))}
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result['counts']))
    for x in traces:
        print(json.dumps({'gap':x['gap'],'case':x['case'],'register_values':x['input']['regs'],
              'reason':x['reason'],'microsteps':x['microsteps'],
              'actual':{k:v for k,v in x.get('actual',{}).items() if k!='spares'}}))

if __name__=='__main__':main()
