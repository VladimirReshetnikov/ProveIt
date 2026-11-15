#!/usr/bin/env python3
"""Independent all-start blank screen of the 55 catalogued 193-state graphs.

Finite halts, exact configuration cycles, and monotone outward rays are certified
directly. Step caps remain unresolved; no consistency property is inferred from
a long finite execution. The outward-ray rule needs a fresh blank frontier and
a zero-input state cycle whose moves all point outwards.
"""
from pathlib import Path
import argparse,collections,csv,json
from census import parse_text,canon

HERE=Path(__file__).resolve().parent

def zero_ray(rows,states,halt,q,d):
    seen=set();path=[]
    while q not in seen:
        if q==halt:return None
        seen.add(q);path.append(q)
        w,move,q=rows[q,0]
        if move!=d:return None
    return {'direction':d,'path_states':path,'cycle_entry':q}

def run(table,start,rays,limit=100000):
    rows,states,halt,*_=table
    q=start;head=0;ones=set();lo=1;hi=-1;seen={}
    for step in range(limit+1):
        if q==halt:return {'status':'halt','steps':step,'head':head,'ones':len(ones)}
        if head>hi and rays[q,'R'] is not None:
            return {'status':'outward_ray','steps':step,'head':head,'ones':len(ones),'ray':rays[q,'R']}
        if head<lo and rays[q,'L'] is not None:
            return {'status':'outward_ray','steps':step,'head':head,'ones':len(ones),'ray':rays[q,'L']}
        # Exact full-tape configurations, retaining the complete finite support.
        if len(ones)<=64:
            config=(q,head,frozenset(ones))
            if config in seen:
                return {'status':'exact_cycle','steps':step,'cycle_start':seen[config],'period':step-seen[config],'head':head,'ones':len(ones)}
            if len(seen)<20000:seen[config]=step
        if step==limit:
            return {'status':'cap','steps':step,'state':q,'head':head,'ones':len(ones)}
        lo=min(lo,head);hi=max(hi,head)
        w,d,q=rows[q,int(head in ones)]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R' else -1

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--corpus',type=Path,default=HERE/'corpus193');ap.add_argument('--out',type=Path,default=HERE/'screen193.json');args=ap.parse_args()
    out=[];tables=[]
    ns=sorted(args.corpus.glob('*.tm'));assert len(ns)==55
    for i,n in enumerate(ns):
        t=parse_text(n.read_bytes());assert t and len(t[1])==193
        hs=[canon(t,q) for q in t[1]]
        actual=min(h for h,count in hs if count==193)
        assert actual==n.stem,(n,actual)
        row=[]
        rays={(q,d):zero_ray(t[0],t[1],t[2],q,d) for q in t[1] for d in ('L','R')}
        for q in sorted(t[1]):
            r=run(t,q,rays);out.append({'table_class':actual,'start':q,**r});row.append(r['status'])
        tables.append({'table_class':actual,'states':193,'outcomes':dict(collections.Counter(row))})
        print(i+1,'/ 55',tables[-1]['outcomes'],flush=True)
    summary={'tables':len(tables),'all_starts':len(out),'step_limit':100000,'outcomes':dict(collections.Counter(r['status'] for r in out)),
        'qualification':'All working states tried as blank starts. This tests no alternative nonblank seed. A cap is unresolved. Certified easy nonhalting is not a PA-consistency calibration.',
        'cap_runs':[r for r in out if r['status']=='cap']}
    args.out.parent.mkdir(exist_ok=True,parents=True)
    args.out.write_text(json.dumps({'summary':summary,'tables':tables,'runs':out},indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
