"""Explore register-role renaming after transfers into provably zero registers.

Uses the original source-program mask invariant as a proved-by-induction
ordinary certificate. No generated table or unbounded machine proof is claimed.
"""
from pathlib import Path
from collections import deque,Counter,defaultdict
import json,sys,time
sys.path.insert(0,str(Path(__file__).parent/'input'))
import permutation252_phase_analysis as p
ROOT=Path(__file__).parent
sites,cases,targets,first=p.program_graph((ROOT/'input/Prog254.v').read_bytes())
values=json.loads((ROOT/'value-analysis-32.json').read_text())['values']
dag=json.loads((ROOT/'input/27-variant-experiments-machine_search-grammar_search-decoder_entries.json').read_text())
by=[[] for _ in sites];incoming=[[] for _ in sites]
for ci,(site,*_) in enumerate(cases):
    by[site].append(ci)
    if targets[ci] is not None:incoming[targets[ci]].append(ci)
lookup={x[0]:i for i,x in enumerate(sites)}
K=32;high=1<<K;small=high-1

def transfer(v,ci):
    if v is None:return None
    out=list(v);_,_,op,r,z=cases[ci]
    if op=='CI':out[r]=((out[r]&small)<<1)|(out[r]&high)
    elif op=='CD':
        if z:
            if not out[r]&1:return None
            out[r]=1
        else:
            if not out[r]&~1:return None
            out[r]=((out[r]&small)>>1)|((high|(high>>1)) if out[r]&high else 0)
    return tuple(out)

move_nodes={}
for n,pair in dag['nodes'].items():
    if pair[0][0]=='D' and pair[1][0]=='N':
        ch=dag['nodes'][str(pair[1][1])]
        if ch[0][0]=='I' and ch[1]==['C',2]:
            move_nodes[int(n)]=(pair[0][1],ch[0][1])

swaps={};occurrences=[];entry_values={}
def visit(n,path):
    if n in move_nodes:
        r,d=move_nodes[n];site=lookup[path+'0']
        external=[ci for ci in incoming[site] if not cases[ci][1].startswith(path)]
        post=[transfer(values[cases[ci][0]],ci) for ci in external]
        post=[v for v in post if v is not None]
        entry=tuple(0 for _ in range(9))
        for v in post:entry=tuple(a|b for a,b in zip(entry,v))
        accepted=entry[d]==1
        occurrence=dict(node=n,path=path,site=site,source=r,destination=d,external=external,entry_masks=entry,accepted=accepted)
        occurrences.append(occurrence)
        if accepted:
            pc=p.inc_path(path)
            candidates=[(len(s),i) for s,i in lookup.items() if s.startswith(pc) and '1' not in s[len(pc):]]
            if not candidates:
                # incPath can retain trailing carry zeros beyond the next leaf.
                candidates=[(len(s),i) for s,i in lookup.items() if pc.startswith(s) and '1' not in pc[len(s):]]
            assert len(candidates)==1,(path,pc,candidates)
            dst=candidates[0][1]
            swaps[site]=(r,d,dst);entry_values[site]=entry
    for bit,e in enumerate(dag['nodes'][str(n)]):
        if e[0]=='N':visit(e[1],path+str(bit))
visit(dag['root'],'')

def canonical(site,perm):
    v=entry_values.get(site,values[site])
    if v is None:return perm
    groups=defaultdict(list)
    for i,m in enumerate(v):
        if m and m&(m-1)==0 and m!=high:groups[m].append(i)
    out=list(perm)
    for ids in groups.values():
        slots=sorted(perm[i] for i in ids)
        for i,slot in zip(ids,slots):out[i]=slot
    return tuple(out)

def successors(site,perm):
    if site in swaps:
        r,d,dst=swaps[site];out=list(perm);out[r],out[d]=out[d],out[r]
        yield dst,canonical(dst,tuple(out)),('swap',r,d)
    else:
        for ci in by[site]:
            if transfer(values[site],ci) is None:continue
            dst=targets[ci]
            if dst is None:continue
            yield dst,canonical(dst,perm),('step',ci)

def main():
    max_nodes=int(sys.argv[1]) if len(sys.argv)>1 else 1000000
    initial=(first,canonical(first,tuple(range(9))))
    seen={initial};q=deque([initial]);pops=0;edges=0;start=time.monotonic();counts=Counter()
    while q and len(seen)<max_nodes:
        site,perm=q.popleft();pops+=1
        for dst,other,kind in successors(site,perm):
            edges+=1;item=(dst,other)
            if item not in seen:seen.add(item);q.append(item)
        if pops%100000==0:print('progress',pops,len(seen),len(q),time.monotonic()-start,flush=True)
    for site,_ in seen:counts[site]+=1
    summary=dict(status='complete' if not q else 'node_limit',sites=len(sites),move_occurrences=len(occurrences),accepted_moves=len(swaps),states=len(seen),pops=pops,edges=edges,pending=len(q),seconds=time.monotonic()-start,unique_sites=len(counts),clones_histogram=dict(Counter(counts.values())),worst_sites=counts.most_common(30))
    result=dict(summary=summary,occurrences=occurrences,states=sorted(seen))
    (ROOT/'dynamic-renaming.json').write_text(json.dumps(result))
    print(summary,flush=True)

if __name__=='__main__':main()
