import sys,random,json,time
from pathlib import Path
from discover_folds import read_table,history_contexts

def pi(s,drop,keep):return keep if s==drop else s

def candidate_row(t,s,b,drop,keep,rows):
    w,d,z=rows[b] if s==keep else t[s,b]
    return w,d,pi(z,drop,keep)

def screen(t,s,b,c,drop,keep,rows,rng,limit=31):
    if 0 in c and c[0]!=b:return True
    tape={p:rng.randrange(2) for p in range(-limit-2,limit+3)}
    tape.update(c);tape[0]=b
    w,d,z=t[s,b];target=pi(z,drop,keep)
    expected=dict(tape);expected[0]=w
    state,head=keep,0
    for k in range(limit):
        if state==254:return False
        v,e,state=candidate_row(t,state,tape[head],drop,keep,rows)
        tape[head]=v;head+=e
        if (state,head)==(target,d) and tape==expected:return True
    return False

def exact(t,s,b,c,drop,keep,rows,limit=31):
    if 0 in c and c[0]!=b:return []
    w,d,z=t[s,b];target=pi(z,drop,keep)
    c=dict(c);c[0]=b
    stack=[(keep,0,{},c,[])];cert=[]
    while stack:
        state,head,writes,vals,trace=stack.pop()
        if trace and (state,head)==(target,d):
            positions=set(writes)|{0}
            if all(writes.get(p,vals.get(p,('v',p)))==(w if p==0 else vals.get(p,('v',p))) for p in positions):
                cert.append({'input':vals,'trace':trace});continue
        if state==254 or len(trace)>=limit:return None
        bit=writes.get(head,vals.get(head))
        if bit is None:
            for v in (0,1):
                vs=dict(vals);vs[head]=v;stack.append((state,head,dict(writes),vs,list(trace)))
            continue
        v,e,z=candidate_row(t,state,bit,drop,keep,rows)
        ws=dict(writes);ws[head]=v
        stack.append((z,head+e,ws,vals,trace+[[state,head,bit,v,e,z]]))
        if len(stack)+len(cert)>4096:return None
    return cert

if __name__=='__main__':
    t=read_table(Path(sys.argv[1]));out=Path(sys.argv[2]);depth=int(sys.argv[3]) if len(sys.argv)>3 else 7
    start=time.monotonic();contexts=({int(q):[tuple(map(tuple,c)) for c in cs] for q,cs in json.loads(Path(sys.argv[4]).read_text()).items()} if len(sys.argv)>4 else history_contexts(t,depth))
    states=sorted({s for s,b in t if s!=0});rng=random.Random(1);results=[];count=0
    print('contexts',sum(map(len,contexts.values())),max(map(len,contexts.values())),flush=True)
    for i,q in enumerate(states):
        for r in states[:i]:
            inputs=[(s,b,dict(c)) for s in(q,r) for c in contexts[s] for b in(0,1)]
            for a0 in(q,r):
                for a1 in(q,r):
                    rows=[t[a0,0],t[a1,1]];count+=1
                    if not all(screen(t,s,b,c,q,r,rows,rng) for s,b,c in inputs for _ in range(2)):continue
                    cases=[]
                    for s,b,c in inputs:
                        cs=exact(t,s,b,c,q,r,rows)
                        if cs is None:break
                        cases.append({'state':s,'bit':b,'context':c,'branches':cs})
                    else:
                        print('FOUND',q,r,rows,flush=True)
                        results.append({'remove':q,'keep':r,'rows':rows,'cases':cases})
    out.write_text(json.dumps({'depth':depth,'count':count,'seconds':time.monotonic()-start,'results':results},indent=2)+'\n')
    print('DONE',len(results),count,time.monotonic()-start,flush=True)
