from search_folds import *
import sys
rows=read_table(BASE/'sources/bb196/data/pa196.tm')
k=int(sys.argv[1]) if len(sys.argv)>1 else 5
reach=reachable(rows,k)
limit=40
n=max(q for q,b in rows)+1

def possible(q,b,v,exclude):
    tape={i-k:(v>>i)&1 for i in range(2*k+1)}
    orig=tape.copy();h=0;s=q;seen={};opts={}
    for steps in range(1,limit+1):
        if h not in tape or (s,tape[h]) not in rows:break
        w,d,s=rows[s,tape[h]];tape[h]=w;h+=d
        if steps>=2 and s!=exclude and abs(h)==1 and all(tape[j]==orig[j] for j in tape if j!=0):
            key=(tape[0],h,s)
            opts[key]=min(opts.get(key,steps),steps)
    return opts

start=time.time();hits=[];edge_hits=[]
for deleted in range(1,n):
    incoming=[(q,b) for (q,b),(w,d,t) in rows.items() if t==deleted and q!=deleted]
    selected={};lengths={};failed=False
    for q,b in incoming:
        vs=[v for v in reach[q] if ((v>>k)&1)==b]
        possible_rows=None;lens={}
        for v in vs:
            opt=possible(q,b,v,deleted)
            if possible_rows is None:possible_rows=set(opt)
            else:possible_rows.intersection_update(opt)
            if not possible_rows:break
            for act in possible_rows:lens.setdefault(act,set()).add(opt[act])
        if possible_rows:
            act=min(possible_rows,key=lambda a:(max(lens[a]),a))
            selected[q,b]=act;lengths[q,b]=lens[act]
            edge_hits.append((deleted,q,b,act,sorted(lens[act])))
        else:failed=True;break
    if not failed and selected:
        res={'deleted':deleted,'rows':[[q,b,*a] for (q,b),a in selected.items()],'lengths':{str(key):sorted(v) for key,v in lengths.items()}}
        hits.append(res);print('HIT',json.dumps(res),flush=True)
print('DONE',len(hits),time.time()-start,flush=True)
(BASE/f'research/bypass_k{k}.json').write_text(json.dumps({'hits':hits,'edge_hits':edge_hits},indent=2))
