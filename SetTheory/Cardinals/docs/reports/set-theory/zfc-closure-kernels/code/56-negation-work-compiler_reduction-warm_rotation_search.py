#!/usr/bin/env python3
"""Screen closed source rotations with a fixed, already checked folding seed.

Fresh decoder labels are aligned by original-node provenance before replaying
the seed folds. A replay is only a search proposal: every result is screened
against all instruction contracts for its own source, then blank execution.
"""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter
from pathlib import Path
import search_structural as s

def load_source(path):
    d=json.loads(path.read_text())
    return ({int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()},d['root'],
            {int(k):set(v) for k,v in d['origins'].items()})

def load_folds(paths):
    folds=[]
    for p in paths:
        for round_ in json.loads(p.read_text())['rounds']:
            accepted=[x for x in round_['survivors'] if x['boot']['outcome']=='zero_root']
            if accepted:
                x=accepted[-1];folds.append((x['deleted'],x['target'],x['mask']))
    return folds

def apply_folds(table,folds):
    table=table.copy()
    for dead,keep,mask in folds:
        if (dead,0) not in table or (keep,0) not in table:
            continue
        rows=[table[dead,b] if mask>>b&1 else table[keep,b] for b in range(2)]
        table={(q,b):(w,m,keep if target==dead else target)
               for (q,b),(w,m,target) in table.items() if q!=dead}
        for b,(w,m,target) in enumerate(rows):
            table[keep,b]=w,m,keep if target==dead else target
    return table

def aligned_emit(nodes,root,origins,reference,refroot,reforigins,stable_extra_labels=False):
    _,refmeta=s.emit(reference,refroot,reforigins,'fresh')
    refentries=refmeta['entries'];reffp=s.fingerprints(reference)
    fpentry={f:refentries[n] for n,f in reffp.items()}
    originentry={o:refentries[n] for n,org in reforigins.items() for o in org}
    fp=s.fingerprints(nodes)
    entries={n:96 if n==root else s.NODE_LABELS[s.OLD_FP[fp[n]]]
             for n in nodes if n==root or fp[n] in s.OLD_FP}
    used=set(entries.values());fresh=max(refentries.values())+1
    for n in nodes:
        if n in entries:continue
        candidates=([fpentry[fp[n]]] if fp[n] in fpentry else [])
        candidates+=sorted({originentry[o] for o in origins.get(n,()) if o in originentry})
        candidates=[q for q in candidates if q>=255 and q not in used]
        if stable_extra_labels and not candidates:
            candidates=sorted({1000+o for o in origins.get(n,()) if 1000+o not in used})
        if candidates:q=candidates[0]
        elif stable_extra_labels:
            q=10000+int(fp[n][:12],16)
            while q in used:q+=1
        else:
            while fresh in used:fresh+=1
            q=fresh;fresh+=1
        entries[n]=q;used.add(q)
    def trans(e,b):
        if e[0]=='N':return b,'R',entries[e[1]]
        if e[0]=='B' and e[1]==1:return 0,'L',7 if b==0 else 33
        if e[0] in 'BC':return s.CONTROL[e,b].most_common(1)[0][0]
        return b,'R',s.LEAF_LABELS[':'.join(map(str,e))]
    table=s.BASE.copy()
    for n in nodes:
        if n==root or fp[n] not in s.OLD_FP:
            for b,e in enumerate(nodes[n]):table[entries[n],b]=trans(e,b)
    return table,entries

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path)
    ap.add_argument('--reference',type=Path,default=s.HERE/'direct_negation/fresh.json')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--fold-log',type=Path,action='append',default=[])
    ap.add_argument('--limit',type=int,default=10000)
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    nodes,root,origins=load_source(a.source);ref,rr,ro=load_source(a.reference)
    folds=load_folds(a.fold_log);begun=time.monotonic();counts=Counter();results=[]
    options=[None]+list(s.rotate.options(nodes));best=999
    for index,opt in enumerate(options[:a.limit]):
        if opt is None:nn,nr,no=nodes,root,origins;mutation=None
        else:
            n,exp,kind=opt;nn,nr,no=s.mutate(nodes,root,n,exp,origins);mutation=[n,exp,kind]
        zm=s.rotate.zero_metrics(nn,nr)
        if zm[1]>7 or zm[2]>39:
            counts['shape_bound']+=1;continue
        tab,entries=aligned_emit(nn,nr,no,ref,rr,ro);tab=apply_folds(tab,folds)
        rt,used=s.check(tab,nn,nr)
        result=dict(index=index,mutation=mutation,source_nodes=len(nn),zero_metrics=zm,
                    runtime=rt,folds=folds,outcome='runtime_pass' if rt['passed'] else 'runtime_fail')
        if rt['passed']:
            bt,bu=s.boot(tab,150000);result['boot']=bt
            if bt['outcome']=='zero_root':
                pt=s.prune(tab,used|bu);count=len(pt)//2
                result.update(outcome='passed',working_states=count,table=pt,entries=entries)
                if count<=best:
                    best=count;s.save_candidate(result,nn,nr,no,f'candidate_{index}_{count}',a.output)
                    print('CANDIDATE',index,count,mutation,flush=True)
            else:result['outcome']='boot_'+bt['outcome']
        result.pop('table',None);result.pop('entries',None);result.pop('boot',None)
        results.append(result);counts[result['outcome']]+=1
        (a.output/'results.json').write_text(json.dumps(dict(source=str(a.source),best_states=best,
            folds=folds,counts=counts,results=results,elapsed=time.monotonic()-begun),indent=2)+'\n')
        if index%10==0:print('PROGRESS',index,best,dict(counts),round(time.monotonic()-begun,1),flush=True)
    print('FINISHED',best,dict(counts),round(time.monotonic()-begun,1),flush=True)

if __name__=='__main__':main()
