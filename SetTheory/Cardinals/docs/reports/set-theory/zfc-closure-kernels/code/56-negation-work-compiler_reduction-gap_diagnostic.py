#!/usr/bin/env python3
"""Exact affine substitution: audit frames of gap BASE+n for all n>=0."""
from collections import Counter
from pathlib import Path
from types import SimpleNamespace
import argparse,json,sys,time
import search_structural as s

HERE=Path(__file__).resolve().parent
SOURCE=s.SOURCE/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'

def checker(gap):
    raw=SOURCE.read_text()
    assert raw.count('40-len(pc)')==1
    raw=raw.replace('40-len(pc)',f'{gap}-len(pc)')
    ns={};exec(compile(raw,str(SOURCE)+'[affine-gap-substitution]', 'exec'),ns)
    return SimpleNamespace(**ns)

def check_gap(table,nodes,root,gap):
    strict=checker(gap);count=0
    traced=s.Tracking({(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()})
    for p,e in s.sites(nodes,root):
        k=e[0];r=e[1] if len(e)>1 else None
        physical=s.audit.NEWPHYS[r] if k in 'ID' else r
        for z in ((True,False) if k=='D' else (None,)):
            nxt=s.audit.successor(p,'C'+k,r,z)
            effect=('inc',physical) if k=='I' else ('dec',physical) if k=='D' and not z else None
            right=([('r',0,1,gap+1),('b',1),('box',('plain',effect))] if nxt is None else
                   [('b',int(b)) for b in nxt]+[('r',0,1,gap-len(nxt)),('b',1),('box',('plain',effect))])
            target=strict.canon([('b',1)],right)
            try:strict.run(traced,p,(physical,z) if k=='D' else None,target,halt=k=='H',fuel=2000)
            except (AssertionError,KeyError) as ex:
                return dict(passed=False,cases_passed=count,gap_base=gap,failure=dict(path=p,operation=e,zero=z,reason=str(ex))),traced.used
            count+=1
    return dict(passed=True,cases_passed=count,gap_base=gap),traced.used

def safe_boot(table,gap_limit,fuel=3000000):
    """Sufficient Truth/top, empty stack and Truth/cache root, full tape parse."""
    state,head,ones=64,0,set();used=set();first=[]
    for steps in range(fuel+1):
        if state==96 and ones and head-1 in ones and min(ones)==head-1:
            future=[x for x in ones if x>=head]
            if future and min(future)-head>=gap_limit:
                header=min(future);i=header+1;regs=[]
                while i not in ones and i+1 in ones:
                    i+=1;count=0
                    while i in ones:count+=1;i+=1
                    regs.append(count-1)
                if len(regs)>=9 and not any(x>=i for x in ones):
                    logical=[regs[s.audit.NEWPHYS[r]] for r in range(9)]
                    frame=dict(steps=steps,gap=header-head,head=head,primary=regs[:9],logical=logical,spares=regs[9:],ones=sorted(ones))
                    if logical[1]==logical[2]==logical[5]==0:
                        return dict(outcome='sufficient_truth_root',frame=frame),used
                    if len(first)<3:first.append(frame)
        if state==254:return dict(outcome='halt',steps=steps,first_frames=first),used
        if steps==fuel:break
        used.add((state,int(head in ones)))
        w,d,state=table[state,int(head in ones)]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R' else -1
    return dict(outcome='fuel_limit',steps=fuel,first_frames=first),used

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--output',type=Path,default=HERE/'gap_diagnostics');ap.add_argument('--gap',type=int,nargs='+',default=[40,41,42,43,44,45]);ap.add_argument('--boot',action='store_true')
    a=ap.parse_args();d=json.loads(a.input.read_text());nodes={int(q):tuple(map(tuple,v)) for q,v in d['nodes'].items()};root=d['root'];origins={int(q):set(v) for q,v in d['origins'].items()};a.output.mkdir(parents=True,exist_ok=True)
    results=[]
    for mode in ['fresh','identity']:
        table,emission=s.emit(nodes,root,origins,mode)
        for gap in a.gap:
            rr,used=check_gap(table,nodes,root,gap);rr['allocation']=mode
            if rr['passed'] and a.boot:
                startup,bootused=safe_boot(table,gap)
                rr['boot']=startup
                if startup['outcome']=='sufficient_truth_root':
                    new=s.prune(table,used|bootused);rr['working_states']=len(new)//2
                    (a.output/f'{mode}_gap{gap}.tm').write_bytes(s.audit.encode(new))
            results.append(rr);print(mode,gap,rr,flush=True)
        (a.output/'results.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
