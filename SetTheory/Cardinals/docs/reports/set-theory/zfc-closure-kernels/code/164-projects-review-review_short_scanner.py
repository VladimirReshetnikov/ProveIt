#!/usr/bin/env python3
"""Independent concrete review of shortening the K217 zero scanner.

This is a finite literal counterexample to primitive refinement, plus an exact
source-reachability witness. It does not by itself refute Con(ZFC) equivalence.
"""
from pathlib import Path
import argparse, hashlib, json, sys

PHY=(6,2,0,4,3,7,8,5,1)


def read(path):
    t={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert (q,b) not in t and b in(0,1) and w in(0,1) and d in('L','R')
        t[q,b]=w,1 if d=='R' else -1,z
    return t


def frame(pc,regs,spares,gap):
    physical=[0]*9
    for i,p in enumerate(PHY):physical[p]=regs[i]
    support={-1,64+gap}|{i for i,b in enumerate(pc) if b=='1'}
    pos=65+gap
    for x in physical+spares:
        pos+=1;support.update(range(pos,pos+x+1));pos+=x+1
    return support


def inc(pc):
    if not pc:return '',1
    x=int(pc,2)+1
    return format(x%(1<<len(pc)),f'0{len(pc)}b'),int(x==(1<<len(pc)))


def strip(pc,bit,count):
    if count==0:return pc
    for i in range(len(pc)-1,-1,-1):
        if pc[i]==bit:
            count-=1
            if count==0:return pc[:i]
    return ''


def clean(q,h,o):
    if q!=84 or h-1 not in o or any(x<h-1 for x in o):return False
    right=sorted(x for x in o if x>=h+52)
    if not right or right[0]<h+64:return False
    p=right[0]+1;last=max(o);blocks=0
    while p<last:
        if p in o or p+1 not in o:return False
        p+=1
        while p in o:p+=1
        blocks+=1
    return p==last+1 and blocks>=10


def sparse(t,support,limit=2000000):
    o=set(support);q=84;h=0;trace=[]
    for tick in range(limit):
        b=int(h in o);w,d,z=t[q,b]
        trace.append([tick,q,h,b,w,d,z])
        if w:o.add(h)
        else:o.discard(h)
        h+=d;q=z
        if q==254 or clean(q,h,o):
            return {'steps':tick+1,'state':q,'head':h,'support':sorted(o),'trace':trace}
    return {'steps':limit,'state':q,'head':h,'support':sorted(o),'trace':trace,'bound_reached':True}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,help='Directory with k217.native.tm and sites217.json')
    ap.add_argument('--table',type=Path,help='Explicit native table path, overrides --baseline')
    ap.add_argument('--sites',type=Path,help='Explicit source sites path, overrides --baseline')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--full-trace',action='store_true',help='Include all literal microstep traces')
    args=ap.parse_args()
    assert __debug__ and not sys.flags.optimize
    if args.baseline is None and (args.table is None or args.sites is None):
        ap.error('Supply --baseline or both --table and --sites')
    path=args.table or args.baseline/'k217.native.tm'
    sites_path=args.sites or args.baseline/'sites217.json'
    raw=path.read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088'
    old=read(path);new=dict(old)
    assert old[34,0]==(0,-1,50)
    assert old[50,0]==(0,-1,75)
    new[34,0]=(0,-1,75)
    del new[50,0];del new[50,1]
    assert all(z!=50 for w,d,z in new.values())
    sites_raw=sites_path.read_bytes()
    assert hashlib.sha256(sites_raw).hexdigest()=='9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655'
    sites=json.loads(sites_raw)
    lookup={p:i for i,(p,_,_) in enumerate(sites)}
    def locate(pc):
        for k in range(1,1+max(map(len,lookup))):
            p=(pc+'0'*64)[:k]
            if p in lookup:
                assert '1' not in pc[k:]
                return lookup[p]
        raise ValueError('No leaf')
    regs=[3,0,0,0,3,0,0,0,0];spares=[1]*130;gap=80;head=-5;pc='';history=[]
    for step in range(100000):
        ordinal=locate(pc);site=sites[ordinal];p,op,r=site
        history.append([ordinal,regs.copy()])
        if ordinal==40 and regs[r]==0:break
        assert op!='CH'
        delta=0;shift=0
        if op=='CI':
            regs[r]+=1;spares.append(1);pc,shift=inc(p)
        elif op=='CD' and regs[r]>0:
            regs[r]-=1;delta=1;pc,shift=inc(p)
        elif op in('CD','CB'):pc,shift=inc(strip(p,'0',r if op=='CB' else 1))
        elif op=='CC':pc=strip(p,'1',r)
        else:raise ValueError(site)
        gap+=delta+shift;head-=shift
    else:raise ValueError('No witness in source simulation bound')
    assert step==1474 and regs==[7,0,0,0,4,0,0,0,0]
    assert frame(pc,regs,spares,gap)==frame(site[0],regs,spares,gap)
    initial=frame(site[0],regs,spares,gap)
    successor,shift=inc(strip(site[0],'0',1))
    wanted={x-shift for x in frame(successor,regs,spares,gap+shift)}
    runs={k:sparse(t,initial) for k,t in [('accepted',old),('shortened',new)]}
    confusion=[]
    for i,row in enumerate(runs['accepted']['trace']):
        if row[1]==50 and row[3]==1:
            confusion.append(runs['accepted']['trace'][max(0,i-8):i+3])
    for v in runs.values():
        v['matches_expected']=v['state']==84 and v['head']==-shift and set(v['support'])==wanted
        v['trace_sha256']=hashlib.sha256(json.dumps(v['trace'],separators=(',',':')).encode()).hexdigest()
        o=set(v['support']);h=v['head']
        current_pc=''.join(str(int(x in o)) for x in range(h,h+52)).rstrip('0')
        marker=min(x for x in o if x>=h+52);p=marker+1;blocks=[]
        while p<max(o):
            assert p not in o and p+1 in o
            p+=1;start=p
            while p in o:p+=1
            blocks.append(p-start-1)
        v['decoded_frame']={'pc_prefix':current_pc,'next_source_ordinal':locate(current_pc),
                            'registers':[blocks[j] for j in PHY],
                            'gap_extra':marker-h-64,'spares_count':len(blocks)-9}
        v['support_symmetric_difference_from_expected']=sorted(o^wanted)
        if not args.full_trace:del v['trace']
    assert runs['accepted']['matches_expected']
    assert not runs['shortened']['matches_expected']
    out={'status':'REACHABLE_SOURCE_FRAME_REFINEMENT_COUNTEREXAMPLE',
         'scope':'Literal sparse-tape counterexample at a frame reached by the accepted source execution. No assertion that the shortened machine reaches this same frame from blank; no impossibility claim about its halting equivalence.',
         'baseline_sha256':hashlib.sha256(raw).hexdigest(),
         'sites_sha256':hashlib.sha256(sites_raw).hexdigest(),
         'mutation':{'delete_state':50,'new_row_34_0':[0,'L',75]},
         'source_steps_from_initial_dispatch':step,'site_index':40,'site':site,
         'source_frame':{'registers':regs,'spares':spares,'gap_extra':gap,'absolute_head':head,'pc':pc},
         'initial_one_cells_relative_to_head':sorted(initial),'expected_successor':successor,
         'expected_head':-shift,'expected_one_cells':sorted(wanted),
         'source_execution_sha256':hashlib.sha256(json.dumps(history,separators=(',',':')).encode()).hexdigest(),
         'confusing_scan_fragments':confusion,'runs':runs}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in('initial_one_cells_relative_to_head','expected_one_cells','runs','source_frame','confusing_scan_fragments')},indent=2))
    print('frame', {'regs':regs,'gap':gap,'spares_count':len(spares),'head':head})
    for k,v in runs.items():print(k,{x:y for x,y in v.items() if x not in('trace','support')})

if __name__=='__main__':main()
