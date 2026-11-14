#!/usr/bin/env python3
"""Search two-cell scratch-history folds with exact finite local simulations.

Every entry to either merged state must move right and write a fixed bit.
The incoming write may be changed to encode the old control; the replacement
must restore the original bit before simulating that control's transition.
The search does not inspect or assume the blank trajectory.
"""
from pathlib import Path
from collections import defaultdict
import argparse, hashlib, itertools, json, time

def read(path):
    rows={}
    for ln in path.read_text().splitlines():
        q,b,w,d,n=ln.split()
        rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
    return rows

def canonical(rows):
    controls={q for q,b in rows}
    roots=[]
    for start in controls:
        seen={start};order=[start]
        for q in order:
            for b in (0,1):
                t=rows[q,b][2]
                if t in controls and t not in seen:seen.add(t);order.append(t)
        if len(seen)==len(controls):roots.append(start)
    if not roots:return None
    out=[]
    for start in roots:
        order=[start];idx={start:0}
        for q in order:
            for b in (0,1):
                t=rows[q,b][2]
                if t in controls and t not in idx:idx[t]=len(order);order.append(t)
        out.append(tuple((w,d,idx.get(n,len(controls))) for q in order for w,d,n in (rows[q,0],rows[q,1])))
    return min(out)

def search(rows,start=None,fuel=9):
    controls=sorted({q for q,b in rows})
    inc=defaultdict(list)
    for k,(w,d,n) in rows.items():inc[n].append((k,w,d))
    eligible=[];history={}
    for q in controls:
        if q==start or not inc[q]:continue
        ws={w for k,w,d in inc[q]};ds={d for k,w,d in inc[q]}
        if len(ws)==1 and ds=={1}:
            eligible.append(q);history[q]=next(iter(ws))
    tested=0;found=[]
    for a,b in itertools.combinations(eligible,2):
        if any(k[0] in (a,b) for k,w,d in inc[a]+inc[b]):continue
        for ta,tb in ((0,1),(1,0)):
            tags={a:ta,b:tb}
            # Work states apart from the merged state have the identity frame.
            base={}
            for k,(w,d,n) in rows.items():
                if k[0] in (a,b):continue
                base[k]=(tags[n],d,b) if n in tags else (w,d,n)
            options=[]
            for bit in (0,1):
                good=[]
                actions={(bit,-1,h) for h in controls if h not in (a,b)}
                actions.update(rows[q,bit] for q in (a,b))
                for act in actions:
                    if act[2]==a:continue
                    works=True;durations=[]
                    for q in (a,b):
                        ow,od,on=rows[q,bit]
                        expected=(b if on in tags else on,od,history[q],tags[on] if on in tags else ow)
                        pos=0;prev=tags[q];cur=bit;state=b
                        for step in range(1,fuel+1):
                            if pos not in (-1,0):break
                            value=prev if pos==-1 else cur
                            if state==b:
                                if step!=1:break
                                w,d,n=act
                            else:
                                edge=base.get((state,value))
                                if edge is None:break
                                w,d,n=edge
                            if pos==-1:prev=w
                            else:cur=w
                            pos+=d;state=n
                            if (state,pos,prev,cur)==expected:
                                durations.append(step);break
                        else:step=fuel
                        if len(durations)<(1 if q==a else 2):works=False;break
                    tested+=1
                    if works:good.append((act,durations))
                options.append(good)
            if all(options):
                found.append({'delete':a,'keep':b,'original_bits':[history[a],history[b]],'tags':[ta,tb],
                  'options':options,'incoming':inc[a]+inc[b]})
    return {'eligible_states':len(eligible),'tested_branch_actions':tested,'candidates':found}

def main():
    p=argparse.ArgumentParser();p.add_argument('paths',nargs='+');p.add_argument('--output',default='repaint_results.json');p.add_argument('--fuel',type=int,default=9)
    args=p.parse_args();outputs=[];known=set();t0=time.monotonic()
    for name in args.paths:
        path=Path(name)
        try:rows=read(path)
        except Exception:continue
        if len(rows)!=388:continue
        graph=canonical(rows)
        if graph is None or graph in known:continue
        known.add(graph)
        start=0 if (0,0) in rows and len({q for q,b in rows})==194 and max(q for q,b in rows)==193 else 74
        result=search(rows,start,args.fuel)
        result.update(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest())
        outputs.append(result)
        Path(args.output).write_text(json.dumps(outputs,indent=2)+'\n')
        print(json.dumps({'path':str(path),'eligible':result['eligible_states'],'tested':result['tested_branch_actions'],'candidates':len(result['candidates']),'elapsed':round(time.monotonic()-t0,2)}),flush=True)
    print('TOTAL',len(outputs),sum(len(x['candidates'])for x in outputs),flush=True)

if __name__=='__main__':main()
