"""Wall-clock of the Rust scan with 1, 2 and 3 raced orders, interleaved, on expensive random closures."""
import json,os,random,statistics,subprocess,sys
HERE=os.path.dirname(os.path.abspath(__file__))
B=os.path.join(HERE,'target','release','fastunknot.exe' if os.name=='nt' else 'fastunknot')
D=os.path.join(HERE,'target','race_inputs'); os.makedirs(D,exist_ok=True)
def run(path,race,seconds=30):
    p=subprocess.run([B,'khovanov',path,'--race',str(race),'--seconds',str(seconds)],capture_output=True,text=True)
    try: r=json.loads(p.stdout)
    except Exception: return None
    return r.get('seconds') if 'reduced_rank' in r else None, r.get('reduced_rank')
def knot(s,w):
    p=list(range(s))
    for g in w:
        i=abs(g)-1; p[i],p[i+1]=p[i+1],p[i]
    x,n=p[0],1
    while x!=0: x,n=p[x],n+1
    return n==s
rng=random.Random(3030); inputs=[]; tried=0
while len(inputs)<40 and tried<4000:
    s=rng.choice((4,5,6,7)); n=rng.randrange(34,56)
    w=[rng.choice((1,-1))*rng.randrange(1,s) for _ in range(n)]
    if not knot(s,w): continue
    tried+=1
    path=os.path.join(D,f'in{tried}.json'); json.dump({"braid":{"strands":s,"word":w}},open(path,'w'))
    t=run(path,1,seconds=20)
    if t and t[0] and 0.03<=t[0]<=8: inputs.append((path,s,n,t[1]))
    else: os.remove(path)
print(len(inputs),"inputs with a single scan between 30 ms and 8 s (of",tried,"closures tried)",flush=True)
rows=[]
for path,s,n,rank in inputs:
    times={1:[],2:[],3:[]}
    for rnd in range(5):
        for race in ((1,2,3),(3,1,2),(2,3,1))[rnd%3]:
            t=run(path,race); assert t and t[1]==rank,(path,race,t)
            times[race].append(t[0])
    m={k:statistics.median(v) for k,v in times.items()}
    rows.append({'strands':s,'n':n,'t1':m[1],'t2':m[2],'t3':m[3]})
    print(f"strands {s} n {n}: {m[1]*1e3:9.1f} ms | race 2: {m[2]/m[1]:.2f} | race 3: {m[3]/m[1]:.2f}",flush=True)
json.dump(rows,open(os.path.join(HERE,'results','race_eval.json'),'w'),indent=1)
for k in ('t2','t3'):
    r=sorted(x[k]/x['t1'] for x in rows)
    print(f"race {k[1]}: total time {sum(x[k] for x in rows)/sum(x['t1'] for x in rows):.3f} of single; per-input ratio median {statistics.median(r):.3f}, min {r[0]:.2f}, max {r[-1]:.2f}; faster on {sum(v<0.97 for v in r)}, slower on {sum(v>1.03 for v in r)}, within 3% on {sum(0.97<=v<=1.03 for v in r)}")
