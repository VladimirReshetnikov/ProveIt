#!/usr/bin/env python3
"""Construct two marker-separated, accelerated witness-calculus machines.

New composition of attributed prior components. Standard-library Python 3.10+.
This is an exact table and certificate builder, not a proof-assistant kernel.
"""
from pathlib import Path
import argparse, hashlib, itertools, json
ROOT=Path(__file__).resolve().parent
START,HALT=74,254
FAST={(26,1):(1,'R',91),(101,0):(0,'R',17)}

def require(ok,msg):
    if not ok:raise AssertionError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def read(path):
    out={}
    for line in path.read_text().splitlines():
        if not line.strip():continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        require((q,b)not in out and b in(0,1)and w in(0,1)and d in('L','R'),'invalid row')
        out[q,b]=w,d,n
    return out
def table(rows):return ''.join(f'{q} {b} {w} {d} {n}\n' for(q,b),(w,d,n)in sorted(rows.items()))
def dump(p,o):p.write_text(json.dumps(o,indent=2)+'\n')
def move(table,c):
    q,h,t=c;t=set(t)
    if q==HALT:return q,h,t
    w,d,n=table[q,int(h in t)];(t.add if w else t.discard)(h)
    return n,h+(1 if d=='R'else-1),t
def f(q):return 400 if q==51 else 88 if q==301 else q

def accelerate(old):
    def incoming(q):return [(p,b,*a)for(p,b),a in sorted(old.items())if a[2]==q]
    require(old[26,1]==(1,'R',42)and old[101,0]==(0,'L',26),'acceleration parent rows')
    require(old[42,0]==(0,'R',13)and old[13,0]==(0,'L',91),'first detour')
    require(old[26,0]==(0,'R',194)and old[194,0]==(0,'R',17),'second detour')
    require(incoming(101)==[(96,0,0,'R',101)],'101 history')
    require(incoming(26)==[(11,0,0,'L',26),(101,0,0,'L',26)],'26 history')
    require(incoming(11)and all(a[2]==0 for a in incoming(11)),'11 history')
    new=dict(old);new.update(FAST);cases=[]
    for bits in itertools.product((0,1),repeat=5):
        support={i-2 for i,b in enumerate(bits)if b}
        for q,b in FAST:
            if int(0 in support)!=b:continue
            if q==26 and (1 in support or 2 in support):continue
            if q==101 and -1 in support:continue
            a=(q,0,support);trace=[]
            for _ in range(3):
                a=move(old,a);require(a[0]!=HALT,'hidden halt');trace.append([a[0],a[1],sorted(a[2])])
            require(a==move(new,(q,0,support)),'acceleration identity')
            cases.append(dict(state=q,read=b,window=bits,old_steps=3,new_steps=1,old_trace=trace))
    require(len(cases)==12,'case count')
    return new,dict(incoming={str(q):incoming(q)for q in(11,26,101)},cases=cases)

def separate(old):
    require(400 not in {q for q,b in old},'fresh marker label')
    for k,a in { (51,0):(0,'R',16),(51,1):(1,'R',51),(301,0):(0,'R',45),(301,1):(1,'R',103),
                 (88,0):(0,'R',122),(88,1):(1,'R',103),(122,0):(0,'L',137),(137,0):(0,'R',30),(30,0):(0,'R',45)}.items():
        require(old[k]==a,('marker premise',k))
    incoming={q:[(p,b,*a)for(p,b),a in sorted(old.items())if a[2]==q]for q in(301,88)}
    require(incoming[301]and incoming[88],'nonempty predecessors')
    require(all((w,d)==(0,'R')for p,b,w,d,n in incoming[301]),'history zero')
    require(all((w,d)==(1,'R')for p,b,w,d,n in incoming[88]),'history one')
    new={(f(q),b):(w,d,f(n))for(q,b),(w,d,n)in old.items()if q!=301}
    new[88,0]=0,'L',51;new[51,0]=0,'R',122;new[51,1]=1,'R',51
    unaffected=[k for k in old if k[0]not in(301,88)]
    require(all(new[f(q),b]==(w,d,f(n))for q,b in unaffected for w,d,n in[old[q,b]]),'ordinary rows')
    cases=[]
    for q,hist in[(301,0),(88,1)]:
        for bit in(0,1):
            t={-1:hist,0:bit};oldaction=old[q,bit];w,d,n=oldaction
            target=(f(n),1 if d=='R'else-1,{-1:hist,0:w})
            nq,pos=88,0;trace=[]
            for k in range(1,6):
                require(pos in t,'touched arbitrary exterior')
                act=new[nq,t[pos]];trace.append([nq,pos,t[-1],t[0],*act])
                w,d,nq=act;t[pos]=w;pos+=1 if d=='R'else-1
                require(nq!=HALT,'local hidden halt')
                if(nq,pos,t)==target:break
            else:raise AssertionError('local fold did not close')
            cases.append(dict(old_state=q,left=hist,read=bit,duration=k,trace=trace,exit=[nq,pos,t[-1],t[0]]))
    require([x['duration']for x in cases]==[5,1,3,1],'local clocks')
    return new,dict(incoming=incoming,ordinary_rows=len(unaffected),cases=cases)

def dense(rows):
    controls={q for q,b in rows};require(len(controls)==194 and len(rows)==388,'state count')
    require(set(rows)=={(q,b)for q in controls for b in(0,1)},'total table')
    require({n for w,d,n in rows.values()}-controls=={HALT},'unique halt')
    order=[START];index={START:0}
    for q in order:
        for b in(0,1):
            n=rows[q,b][2]
            if n!=HALT and n not in index:index[n]=len(order);order.append(n)
    require(set(order)==controls,'full graph reachability')
    return {(index[q],b):(w,d,194 if n==HALT else index[n])for(q,b),(w,d,n)in rows.items()},order+[HALT]

def replay(parent,fast,child,meta,extra=10000):
    a=z=n=(START,0,set());parent_clock=fast_clock=child_clock=0
    seed=json.loads((ROOT/'inputs'/meta['parent']/'startup.json').read_text())
    expected=(seed['state'],seed['head'],set(seed['one_cells']))
    counts={'acceleration':{str(k):0 for k in FAST},'marker':{'301/0':0,'88/0':0}}
    recurrence={'acceleration':{str(k):0 for k in FAST},'marker':{'301/0':0,'88/0':0}}
    startup=None
    for iteration in range(300000):
        edge=(z[0],int(z[1]in z[2]));oldq,oldb=edge
        duration=3 if edge in FAST else 1
        hist=5 if oldq==301 and oldb==0 else 3 if oldq==88 and oldb==0 else 1
        selected=counts if startup is None else recurrence
        if edge in FAST:selected['acceleration'][str(edge)]+=1
        if hist>1:selected['marker'][f'{oldq}/{oldb}']+=1
        z=move(fast,z);fast_clock+=1
        for _ in range(duration):a=move(parent,a);parent_clock+=1
        for _ in range(hist):n=move(child,n);child_clock+=1
        require(a==z and n==(f(z[0]),z[1],z[2]),('trajectory identity',iteration))
        require(z[0]!=HALT,'unexpected finite halt')
        if startup is None and z==expected:
            require(parent_clock==seed['steps'],'parent startup clock')
            startup=dict(parent_steps=parent_clock,accelerated_steps=fast_clock,steps=child_clock,
                         state=n[0],head=n[1],one_cells=sorted(n[2]),complete_tape=True,counts=counts)
        if startup and fast_clock==startup['accelerated_steps']+extra:break
    require(startup is not None,'missing seed')
    return startup,dict(additional_accelerated_steps=extra,parent_clock=parent_clock,fast_clock=fast_clock,child_clock=child_clock,recurring_uses=recurrence)

def build(out):
    out.mkdir(parents=True,exist_ok=True);receipts=[]
    for meta in json.loads((ROOT/'inputs/specifications.json').read_text()):
        p=ROOT/'inputs'/meta['parent']/'machine.native.tm';require(digest(p.read_bytes())==meta['parent_native_sha256'],'parent bytes')
        parent=read(p);fast,ac=accelerate(parent);child,mc=separate(fast);dt,labels=dense(child)
        startup,post=replay(parent,fast,child,meta)
        dest=out/meta['name'];dest.mkdir(parents=True,exist_ok=True)
        for name,rows in [('machine.native.tm',child),('machine.tm',dt),('accelerated_parent.native.tm',fast)]:
            (dest/name).write_text(table(rows))
        dump(dest/'labels.json',labels);dump(dest/'startup.json',startup)
        receipt=dict(name=meta['name'],parent=meta['parent'],states=194,rows=388,start=0,halt=194,native_start=START,native_halt=HALT,
                     parent_native_sha256=meta['parent_native_sha256'],native_sha256=digest(table(child).encode()),dense_sha256=digest(table(dt).encode()),
                     acceleration=ac,marker=mc,startup=startup,post_startup=post,
                     theorem='iPRA: H_parent(t) -> H_child(5t), H_child(t) -> H_parent(3t); hence NH equivalence.',
                     proof_status='Written relative proof and exhaustive local certificate; inherited written absolute calibration; no new end-to-end kernel proof.')
        dump(dest/'receipt.json',receipt);receipts.append(receipt)
        print(meta['name'],receipt['dense_sha256'],startup['steps'],flush=True)
    dump(out/'receipts.json',receipts)
    return receipts
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'machines');args=ap.parse_args();build(args.output)
