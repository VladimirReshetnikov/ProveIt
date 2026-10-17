#!/usr/bin/env python3
"""Greedy measured contextual folds after a closed decoder reassociation.

Runtime sites, literal finite bootstrap, and conservative protected box rows
are rechecked after each accepted step. Unused rows are pruned only from the
union of these three coverage sources. No kernel-verification claim.
"""
import argparse,json,time
from collections import defaultdict
import cost_search as s

def check_full(table,nodes,root):
    assert all(table[p]==s.BASE253[p] for p in s.BOX_PAIRS)
    ns=s.ctx.executor(table,s.BASE/'tools/tm/symexec.py');cases=s.ctx.cases(ns,s.sites(nodes,root))
    traced=s.Tracking(table);ns['T']=traced
    for c in cases:
        if not s.ctx.check(ns,c):return None
    boot,boot_used=s.boot_candidate(table,nodes,root)
    if boot['outcome']!='matched':return None
    used=traced.used|boot_used|s.BOX_PAIRS
    keep={q for q,b in used}|{'5','96'}
    result={}
    for (q,b),(w,d,t) in table.items():
        if q not in keep:continue
        if t not in keep|{'254'}:
            assert (q,b) not in used;t='5'
        result[q,b]=w,d,t
    return result,boot

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--index',type=int,default=49);args=ap.parse_args()
    n,e,kind=s.rot.options(s.NODES)[args.index];nodes,root=s.rot.mutate(s.NODES,s.ROOT,n,e)
    initial=s.evaluate(nodes,root);assert initial['outcome']=='passed';table=initial.pop('table')
    protected={str(q) for q in s.BOX_STATES}|{'5','96'}
    out=s.HERE/'results';history=[];tested=0;box_filtered=0;begin=time.monotonic()
    for stage in range(20):
        ns=s.ctx.executor(table,s.BASE/'tools/tm/symexec.py');cases=s.ctx.cases(ns,s.sites(nodes,root))
        usage=defaultdict(list)
        for i,c in enumerate(cases):
            traced=s.Tracking(table);ns['T']=traced;assert s.ctx.check(ns,c)
            for q in {q for q,b in traced.used}:usage[q].append(i)
        states={q for q,b in table};sources=sorted(states-protected,key=lambda q:(len(usage[q]),int(q)))
        accepted=None
        for qi,q in enumerate(sources):
            witnesses=sorted(usage[q],key=lambda i:len(cases[i][1]))
            for replacement in sorted(states-{q},key=int):
                changed={k:(w,d,replacement if t==q else t) for k,(w,d,t) in table.items() if k[0]!=q}
                if any(changed[p]!=s.BASE253[p] for p in s.BOX_PAIRS):box_filtered+=1;continue
                ns['T']=changed;tested+=1
                if not all(s.ctx.check(ns,cases[i]) for i in witnesses):continue
                full=check_full(changed,nodes,root)
                if full is None:continue
                result,boot=full
                if len(result)>=len(table):continue
                accepted={'stage':stage,'deleted':q,'replacement':replacement,
                          'old_states':len(table)//2,'new_states':len(result)//2,
                          'further_pruned_states':sorted(states-{q}-{r for r,b in result},key=int),
                          'boot':boot}
                table=result;history.append(accepted)
                s.emit_table(out/f'greedy_rotation{args.index}_stage{stage}.tm',table)
                print('accepted',q,'->',replacement,'states',len(table)//2,'boot',boot['steps'],flush=True)
                break
            if accepted:break
            if (qi+1)%50==0:print('stage',stage,'sources',qi+1,'/',len(sources),'tested',tested,'seconds',round(time.monotonic()-begin,1),flush=True)
        if not accepted:break
    result={'rotation_index':args.index,'initial_states':initial['working_states'],'final_states':len(table)//2,
            'history':history,'affine_candidates_tested':tested,'candidates_box_filtered':box_filtered,
            'elapsed_seconds':round(time.monotonic()-begin,3),'scope':'Greedy direct state redirections, complete affine runtime model with unchanged published box rows and exact bounded boot into a reachable candidate-RM prefix; post-fold coverage pruning; no kernel verification or minimality assertion.'}
    (out/f'greedy_rotation{args.index}.json').write_text(json.dumps(result,indent=2)+'\n')
    s.emit_table(out/f'greedy_rotation{args.index}_final.tm',table)
    print(json.dumps({k:v for k,v in result.items() if k!='history'},indent=2),flush=True)

if __name__=='__main__':main()
