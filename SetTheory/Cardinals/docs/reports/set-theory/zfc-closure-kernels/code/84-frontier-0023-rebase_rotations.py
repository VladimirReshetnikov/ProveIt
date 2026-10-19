#!/usr/bin/env python3
"""Arbitrary source-tree rotations, with exact control-graph rebasing.

The source need not be a closed sequential expression. All ordinary register
instructions remain at the same DFS occurrence. Break/Continue levels are
rebased only when their exact successor occurrence can be preserved. Both
edges of every decrement must also preserve their exact successors.
"""
from pathlib import Path
from functools import lru_cache
from bisect import bisect_right
from collections import Counter
import argparse,json,time,hashlib
import composed_rotations as D
import affine_acceleration as F
E,R,O=D.E,D.R,D.O
HERE=Path(__file__).resolve().parent

def sites(nodes,root):
    out=[]
    def walk(e,p):
        if e[0]=='N':
            a,b=nodes[e[1]];walk(a,p+'0');walk(b,p+'1')
        else:out.append((p,e))
    walk(('N',root),'');return out

def indexer(ss):
    starts=[int(p,2)<<(64-len(p)) if p else 0 for p,e in ss]
    def index(word):
        value=int(word,2)<<(64-len(word)) if word else 0
        return bisect_right(starts,value)-1
    return index

def jump(path,op,k):
    stripped=E.audit.full_strip(path,'0' if op=='B' else '1',k)
    return E.audit.full_inc(stripped)[0] if op=='B' else stripped

BASE=sites(O.N,O.root)
BASE_INDEX=indexer(BASE)
TARGETS=[]
for i,(p,e) in enumerate(BASE):
    op=e[0]
    if op=='D':TARGETS.append((BASE_INDEX(E.audit.full_inc(p)[0]),BASE_INDEX(jump(p,'B',1))))
    elif op=='I':TARGETS.append((BASE_INDEX(E.audit.full_inc(p)[0]),))
    elif op in 'BC':TARGETS.append((BASE_INDEX(jump(p,op,e[1])),))
    else:TARGETS.append(())

def rebase(nodes,root,origins,mode='same'):
    ss=sites(nodes,root);assert len(ss)==len(BASE)
    idx=indexer(ss);changed=[];new_leaves=[]
    for i,((p,e),(_,old)) in enumerate(zip(ss,BASE)):
        assert e==old
        op=e[0]
        if op=='D':
            targets=(idx(E.audit.full_inc(p)[0]),idx(jump(p,'B',1)))
            if targets!=TARGETS[i]:return None,dict(status='decrement_scope_changed',leaf=i,path=p,targets=targets,wanted=TARGETS[i])
        elif op=='I':
            assert (idx(E.audit.full_inc(p)[0]),)==TARGETS[i]
        elif op in 'BC':
            goal=TARGETS[i][0]
            if idx(jump(p,op,e[1]))!=goal:
                kinds=(op,) if mode=='same' else (op,'B' if op=='C' else 'C')
                choices=[(kind,k) for kind in kinds for k in range(len(p)+2) if idx(jump(p,kind,k))==goal]
                if not choices:return None,dict(status='control_target_not_expressible',leaf=i,path=p,wanted=goal,old=e)
                # Prioritize retaining the opcode and the smallest changed level.
                e=min(choices,key=lambda x:(x[0]!=op,abs(x[1]-old[1]),x[1]))
                changed.append((i,old,e))
        new_leaves.append(e)
    # Rebuild shared nodes after per-occurrence corrections. Distinct corrected
    # subtrees inherit every original entry label they can soundly claim.
    nn,interned,no={}, {}, {};at=0
    def tree(e):
        nonlocal at
        if e[0]!='N':
            result=new_leaves[at];at+=1;return result
        a,b=map(tree,nodes[e[1]]);pair=(a,b)
        if pair not in interned:
            interned[pair]=len(nn);nn[interned[pair]]=pair
        n=interned[pair]
        no.setdefault(n,set()).update(origins.get(e[1],()))
        return ('N',n)
    rt=tree(('N',root))[1];assert at==len(BASE)
    # Independent recomputation of every newly encoded leaf successor.
    corrected=sites(nn,rt);at_index=indexer(corrected)
    for i,(p,e) in enumerate(corrected):
        op=e[0]
        if op=='D':actual=(at_index(E.audit.full_inc(p)[0]),at_index(jump(p,'B',1)))
        elif op=='I':actual=(at_index(E.audit.full_inc(p)[0]),)
        elif op in 'BC':actual=(at_index(jump(p,op,e[1])),)
        else:actual=()
        assert actual==TARGETS[i],(i,actual,TARGETS[i])
    return (nn,rt,no),dict(status='PASS_EXACT_LEAF_CFG',rebased_leaves=changed,source_nodes=len(nn))

def options(nodes):
    for n,(x,y) in nodes.items():
        if x[0]=='N':
            a,b=nodes[x[1]];yield n,('T',a,('T',b,y)),'right'
        if y[0]=='N':
            a,b=nodes[y[1]];yield n,('T',('T',x,a),b),'left'

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--max-nodes',type=int,default=203);a=ap.parse_args()
    out=HERE/'rebased';out.mkdir(exist_ok=True);counts=Counter();records=[];seen=set();began=time.monotonic()
    for i,(n,exp,kind) in enumerate(options(O.N)):
        ns,rt,orig=D.mutation(O.N,O.root,n,exp,{k:{k} for k in O.N})
        for mode in ('same','switch'):
            counts['source_rebase_recipes']+=1
            result,rec=rebase(ns,rt,orig,mode)
            if result is None:
                counts[rec['status']]+=1;continue
            counts['exact_cfg_pass']+=1
            nn,nr,no=result;zm=R.zero_metrics(nn,nr)
            if len(nn)>a.max_nodes or zm[1]>7 or zm[2]>40:
                counts['shape_rejected']+=1;continue
            sg=D.digest(nn,nr)
            if sg in seen:continue
            seen.add(sg);counts['unique_emitted_sources']+=1
            base_record=dict(recipe=i,node=n,rotation=kind,control_policy=mode,signature=sg,metrics=zm,source=rec)
            for recycle,generic in ((True,False),(False,False),(True,True),(False,True)):
                record=dict(base_record,recycle=recycle,generic=generic)
                try:U,entry,reused=O.emit(nn,nr,no,recycle=recycle,generic=generic)
                except (KeyError,IndexError) as ex:
                    counts['unsupported_direct_control']+=1;record.update(status='unsupported_direct_control',error=str(ex));records.append(record);continue
                physical=E.get_sites(nn,nr)
                fast,used=F.run(U,physical,use_priority=False)
                record['fast']=fast;counts['emitted_variants']+=1
                if fast['code']!=0:
                    record['status']='FAST_REJECTED' if fast['code']<0 else 'AT_LEAST_246_OBSERVED_STATES'
                    counts[record['status']]+=1
                else:
                    # Recheck every universal contract with the original engine.
                    cases=E.make_cases(physical);table=E.Track(U);table.used=set()
                    for pc,branch,target,halt in cases:E.A.run(table,pc,branch,target,halt=halt,fuel=2000)
                    retained={q for q,b in table.used|E.PAIRS}
                    assert retained=={q for q,b in used}
                    record.update(status='PASS_GUARDED',states=len(retained));counts['PASS_GUARDED']+=1
                    d=out/f'pass_{i}_{mode}_{int(recycle)}{int(generic)}_{len(retained)}';d.mkdir(exist_ok=True)
                    (d/'dag.json').write_text(json.dumps(dict(nodes=nn,root=nr),indent=2)+'\n')
                    (d/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
                    D.write_table(d/'machine.tm',U,retained)
                    print('PASS',record,flush=True)
                records.append(record)
        if i%10==0:
            print('RECIPE',i,'COUNTS',dict(counts),'SECONDS',round(time.monotonic()-began,2),flush=True)
            (out/'results.json').write_text(json.dumps(dict(counts=counts,records=records,seconds=time.monotonic()-began),indent=2)+'\n')
        if time.monotonic()-began>a.seconds:counts['time_limit_hit']+=1;break
    (out/'results.json').write_text(json.dumps(dict(arguments=vars(a),counts=counts,records=records,seconds=time.monotonic()-began),indent=2)+'\n')
    print('FINAL',dict(counts),flush=True)

if __name__=='__main__':main()
