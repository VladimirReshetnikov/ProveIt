"""Independent source-conditioned context screen for new composite machines.

The complete positive/zero source-mask invariant and arbitrary-natural symbolic
instruction contracts refine the independently sound blank-window abstraction.
"""
from pathlib import Path
from collections import deque
import sys,json,hashlib,importlib.util,argparse,time
HERE=Path(__file__).resolve().parent
ROOT=HERE
BASE=HERE/'reference'
COLLECT=BASE/'window_collector.py'
sys.path.insert(0,str(BASE))
import symbolic_runtime as s
import source_language as source
spec=importlib.util.spec_from_file_location('collector_module',COLLECT)
cm=importlib.util.module_from_spec(spec);spec.loader.exec_module(cm)
spec=importlib.util.spec_from_file_location('helper_replay',BASE/'helper_replay.py')
hr=importlib.util.module_from_spec(spec);spec.loader.exec_module(hr)

def successors(row,mask):
    effect,targets=row
    if effect[0]=='halt':return []
    if effect[0]=='identity':return [(targets[0],mask)]
    bit=1<<effect[1]
    if effect[0]=='increment':return [(targets[0],mask|bit)]
    return [(targets[1],mask&~bit),(targets[1],mask)] if mask&bit else [(targets[0],mask)]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('family');a=ap.parse_args()
    inp=ROOT/'inputs'/a.family
    out=HERE/'results'/a.family;out.mkdir(parents=True,exist_ok=True)
    tab={}
    for line in (inp/'machine.native.tm').read_text().splitlines():
        q,b,w,d,t=line.split();tab[int(q),int(b)]=int(w),1 if d=='R' else -1,int(t)
    labels=sorted({q for q,b in tab});labels.remove(74);labels.insert(0,74)
    dn={q:i for i,q in enumerate(labels)};dn[254]=len(labels)
    mapping={int(k):v for k,v in json.loads((BASE/'legacy_mapping.json').read_text()).items()}
    for q in labels:mapping.setdefault(q,q+10000)
    lt={(mapping[q],b):(w,d,mapping[t]) for(q,b),(w,d,t) in tab.items()}
    dt={(dn[q],b):(w,d,dn[t]) for(q,b),(w,d,t) in tab.items()}
    legacy_to_dense={mapping[q]:dn[q] for q in labels}
    opmap={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    sites=[[p,opmap[op],arg] for p,op,arg in json.loads((inp/'sites.json').read_text())]
    graph,_=source.graph_arithmetic(sites)
    assert graph==source.graph_intervals(sites)
    seen={(25,1)};todo=deque(seen);masks=[set() for _ in sites]
    while todo:
        i,m=todo.popleft();masks[i].add(m)
        for nxt in successors(graph[i],m):
            if nxt not in seen:seen.add(nxt);todo.append(nxt)
    assert all(nxt in seen for i,m in seen for nxt in successors(graph[i],m))
    s.HEADER_BASE=48
    lemmas,blocks=s.prove_blocks(lt)
    list_states={ev[1][0] for block in blocks for ev in block['trace']}
    c=cm.Collector(legacy_to_dense);c.original=s.State.step
    s.State.step=lambda state,table,lemmas,clock,motion:c.observe(state,table,lemmas,clock,motion)
    original_var=s.var;count=skipped=0;start=time.monotonic()
    for i,site in enumerate(sites):
        if not masks[i]:continue
        may=0;must=511
        for m in masks[i]:may|=m;must&=m
        zero=511^may
        for pos in ([False,True] if site[1]=='CD' else [False]):
            if site[1]=='CD' and ((pos and zero>>site[2]&1) or (not pos and must>>site[2]&1)):
                skipped+=1;continue
            def restricted_var(slot):
                if 2<=slot<=10:
                    reg=slot-2
                    if zero>>reg&1:return s.ZERO
                    if must>>reg&1 and not(site[1]=='CD' and reg==site[2]):return s.add(original_var(slot),s.num(1))
                return original_var(slot)
            s.var=restricted_var
            s.case(lt,lemmas,site,pos);count+=1
        if i%500==499:print(a.family,'contracts',count,'windows',sum(map(len,c.windows.values())),'seconds',time.monotonic()-start,flush=True)
    tape=set();q=74;head=0
    for step in range(57922):
        mask=sum(int(head+j in tape)<<(j+2) for j in range(-2,3));c.windows[dn[q]].add(mask)
        w,d,q=tab[q,int(head in tape)];(tape.add if w else tape.discard)(head);head+=d
    expected={head-1,head+48}|{head+i for i,b in enumerate(sites[25][0])if b=='1'}
    p=head+49
    for v in [0,0,0,0,0,0,2,0,0]+[1]*26:
        expected.update(range(p+1,p+v+2));p+=v+2
    assert q==84 and tape==expected
    fold=hr.load_fold();fold.STATES=len(labels)
    global_contexts,mh,cl=fold.blank_window_contexts(dt,6)
    gw={q:set() for q in range(len(labels))}
    for(q,b),ts in global_contexts.items():gw[q]|={sum(t[i]<<(i+2)for i in range(-2,3))for t in ts}
    for q in list_states:c.windows[legacy_to_dense[q]].update(gw[legacy_to_dense[q]])
    refined={q:c.windows[q]&gw[q]for q in gw}
    contexts={(q,b):[{i:(mask>>(i+2))&1 for i in range(-2,3)}for mask in sorted(refined[q])if (mask>>2)&1==b]for q in gw for b in(0,1)}
    counts,records,sha=hr.run_engine(HERE/'scan_helper',out,dt,contexts,len(labels))
    report=dict(family=a.family,source_sites=len(sites),source_mask_pairs=len(seen),source_contracts=count,skipped_branches=skipped,
                symbolic_steps=c.steps,unary_events=c.unary,list_calls=c.list_calls,global_closure=cl,global_windows=sum(map(len,gw.values())),
                refined_windows=sum(map(len,refined.values())),screen=counts,records=records,context_sha256=sha,
                dense_labels=labels+[254],native_sha256=hashlib.sha256((inp/'machine.native.tm').read_bytes()).hexdigest())
    (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
