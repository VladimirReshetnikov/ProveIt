#!/usr/bin/env python3
"""Experimental source emitter reusing compatible origin-state labels.

Unlike allocation by unchanged fingerprint alone, a changed node can overwrite
its original state when no unchanged decoder node claims that state. Every
emission is then independently checked on every guarded leaf; initialization
and source-equivalence proofs are still separate obligations.
"""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'code'))
sys.path.insert(0,str(ROOT/'search/context'))
sys.path.insert(0,str(ROOT/'search/runtime'))
from source_transfer_identity import E,R,N,root
from functools import lru_cache
import json,hashlib,time

def mutate_origins(nodes,rt,n,exp):
    new={};seen={};origins={}
    def intern(a,b):
        p=(a,b)
        if p not in seen:seen[p]=len(new);new[seen[p]]=p
        return ('N',seen[p])
    @lru_cache(None)
    def edge(e):
        if e[0]=='N':
            if e[1]==n:z=edge(exp)
            else:z=intern(*(edge(x) for x in nodes[e[1]]))
            origins.setdefault(z[1],set()).add(e[1]);return z
        if e[0]=='T':return intern(edge(e[1]),edge(e[2]))
        return e
    nr=edge(('N',rt))[1]
    return new,nr,origins

def emit(nodes,rt,origins,generic=False,recycle=False):
    @lru_cache(None)
    def fingerprint(edge):
        text='N('+','.join(fingerprint(e) for e in nodes[edge[1]])+')' if edge[0]=='N' else ':'.join(map(str,edge))
        return hashlib.sha256(text.encode()).hexdigest()
    fingerprints={n:fingerprint(('N',n)) for n in nodes}
    U=E.T.copy();entry={};fresh=256;metadata={};claimed={'96'};reused={}
    def allocate():
        nonlocal fresh
        q=str(fresh);fresh+=1;return q
    for n in nodes:
        f=fingerprints[n]
        if n==rt:entry[n]='96'
        elif f in E.OLD_FP:
            entry[n]=max(E.OLD['state_entries'][str(E.OLD_FP[f])],key=E.OLD['state_entries'][str(E.OLD_FP[f])].get)
            claimed.add(entry[n])
    # Preserve each changed node's label when an unchanged node does not use it.
    newnodes=sorted(set(nodes)-entry.keys(),key=lambda n:(not origins.get(n),n))
    for n in newnodes:
        candidates=[]
        for oldn in sorted(origins.get(n,())):
            candidates.extend(E.OLD['state_entries'][str(oldn)])
        candidates=[q for q in candidates if q not in claimed and int(q) not in E.MACRO and q!='71']
        if candidates:
            entry[n]=candidates[0];claimed.add(entry[n]);reused[n]=entry[n]
    # A rotation can create an interior node without an origin while retiring
    # its old interior node. Try their otherwise unclaimed labels as well.
    if recycle:
        old_fps=set(fingerprints.values())
        available=[]
        for f,oldn in E.OLD_FP.items():
            if f in old_fps:continue
            for q in E.OLD['state_entries'][str(oldn)]:
                if q not in claimed and int(q) not in E.MACRO and q!='71':available.append(q)
        for n in newnodes:
            if n in entry:continue
            if available:
                q=available.pop(0);entry[n]=q;claimed.add(q);reused[n]=q
    for n in newnodes:
        if n not in entry:entry[n]=allocate()
    C={0:'4'};BR={0:'7'}
    def control(op,k):
        cache=C if op=='C' else BR
        if k not in cache:
            prev=control(op,k-1);q=allocate();cache[k]=q
            U[q,0]=(0,'L',q if op=='C' else prev)
            U[q,1]=(0,'L',prev if op=='C' else q)
        return cache[k]
    def transition(e,bit):
        if e[0]=='N':return bit,'R',entry[e[1]]
        if e[0] in 'BC':
            if generic:
                op,k=e
                if op=='B' and bit==0 and k==0:return (1,'R','10')
                return (0,'L',control(op,k-int(bit==(0 if op=='B' else 1))))
            if e[0]=='B' and e[1]==1:return 0,'L','7' if bit==0 else '33'
            return E.CONTROL[e,bit].most_common(1)[0][0]
        return bit,'R',max(E.OLD['leaf_entries'][':'.join(map(str,e))],key=E.OLD['leaf_entries'][':'.join(map(str,e))].get)
    for n in nodes:
        if n==rt or fingerprints[n] not in E.OLD_FP:
            for bit,e in enumerate(nodes[n]):
                U[entry[n],bit]=transition(e,bit);metadata[entry[n],bit]=e
    return U,entry,reused

if __name__=='__main__':
    results=[];began=time.monotonic();rank={};options=R.options(N)
    for idx,(n,exp,kind) in enumerate(options):
        nodes,nr,origins=mutate_origins(N,root,n,exp);zm=R.zero_metrics(nodes,nr)
        if len(nodes)>203 or zm[1]>7 or zm[2]>40:continue
        cases=E.make_cases(E.get_sites(nodes,nr));record={'index':idx,'node':n,'kind':kind,'nodes':len(nodes),'metrics':zm,'variants':[]}
        for recycle in (False,True):
            for generic in (False,True):
                U,entry,reused=emit(nodes,nr,origins,generic=generic,recycle=recycle)
                table=E.Track(U);table.used=set();err=None
                for i in sorted(range(len(cases)),key=lambda i:-rank.get(i,0)):
                    pc,branch,target,halt=cases[i]
                    try:E.A.run(table,pc,branch,target,halt=halt,fuel=2000)
                    except Exception as ex:
                        rank[i]=rank.get(i,0)+1;err={'pc':pc,'branch':branch,'message':str(ex)};break
                v={'recycle':recycle,'generic':generic,'reused':reused}
                if err:v.update(status='affine_failure',failure=err)
                else:
                    retained={q for q,b in table.used|E.PAIRS}
                    v.update(status='PASS',states=len(retained));print('PASS',idx,len(retained),recycle,generic,len(reused),flush=True)
                    if len(retained)<=246:
                        out=Path(__file__).with_name('origin-reuse-'+str(idx)+'-'+str(len(retained))+'-'+str(int(recycle))+str(int(generic)));out.mkdir(exist_ok=True)
                        (out/'dag.json').write_text(json.dumps(dict(root=nr,nodes=nodes,node=n,expression=exp),indent=2)+'\n')
                        (out/'result.json').write_text(json.dumps(v,indent=2)+'\n')
                        pruned={e:(w,d,t if t in retained or t=='254' else '95') for e,(w,d,t) in U.items() if e[0] in retained}
                        (out/'machine.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(pruned.items(),key=lambda x:(int(x[0][0]),x[0][1]))))
                record['variants'].append(v)
        results.append(record)
        print('DONE OPTION',idx,'seconds',time.monotonic()-began,flush=True)
        Path(__file__).with_name('origin-reuse-results.json').write_text(json.dumps(results,indent=2)+'\n')
