#!/usr/bin/env python3
from variant_search import *
from equivalent_search import get_dictionary, parse_with_dictionary
from itertools import product
sys.path.insert(0,str(OUT.parent/'incoming208'))
import compile_ax as ca

def enc2(x,config):
    if isinstance(x,str):return 'Pi' if x=='1' else x
    op,a,b=x
    if config.get(op,False):a,b=b,a
    tags={'I':0,'M':1,'U':config['utag'],'E':5-config['utag']}
    return enc2(a,config)+enc2(b,config)+'C'+'i'*tags[op]

def save(t,info,name):
    T,internal,root=ca.compile_tree(t)
    selected=ca.best_selection(T,internal);table,proj=ca.make_fold(T,selected)
    raw=len(ca.states(T));n=len(ca.states(table))
    path=OUT/'coding_catalog';path.mkdir(exist_ok=True)
    obj=dict(info,tree=t,root=proj[root],table=[[q,b,*a] for(q,b),a in sorted(table.items())],folds=selected,states=n,raw_states=raw)
    (path/(name+'.json')).write_text(json.dumps(obj))
    return n

def main():
    prefix,hs,gate=parts();rng=random.Random(19249);best=196;bestdag=68;dpbest=68;start=time.time();countchecks=0
    baseword=word(get_macro_tree()[2]);d=get_dictionary()
    configs=[{'U':u,'E':e,'M':m,'utag':tag} for u,e,m,tag in product((False,True),(False,True),(False,True),(2,3))]
    orders=list(permutations(range(6)))
    for ci,cfg in enumerate(configs):
        prefix=enc2(U('D','H'),cfg)+'JHDCKDHCAHCCC'
        suffix=enc2(gate,cfg)+'LGX'
        if cfg=={'U':True,'E':False,'M':False,'utag':2}:assert prefix+''.join(enc2(h,cfg) for h in hs)+suffix==baseword
        cbest=999
        for order in orders:
            w=prefix+''.join(enc2(hs[i],cfg) for i in order)+suffix
            cost,pieces=parse_with_dictionary(w,d)
            if cost<dpbest:
                dpbest=cost
                print('DPBEST',cost,'config',cfg,'order',order,flush=True)
                (OUT/f'coding_dp_{cost}.json').write_text(json.dumps({'config':cfg,'head_order':order,'pieces':pieces,'word':w}))
            if cost>70:continue
            for k in range(4):
                t=repair(w,rng,0 if k%2 else rng.randrange(1,6));c=count(t)
                if c<cbest:cbest=c
                if c>70:continue
                n,selection=ca.price(t);countchecks+=1
                if n<best:
                    best=n
                    print('PHYSBEST',n,'DAG',c,'folds',len(selection),'cfg',cfg,'order',order,flush=True)
                    save(t,{'config':cfg,'head_order':order,'word':w},f'coding_best_{n}')
                if n<=198:
                    name=f'coding_{ci}_{countchecks}_{n}'
                    save(t,{'config':cfg,'head_order':order,'word':w},name)
        for j in range(1500):
            order=(0,1,2,3,4,5) if j%2 else rng.choice(orders)
            w=prefix+''.join(enc2(hs[i],cfg) for i in order)+suffix
            t=repair(w,rng,0 if j%2 else rng.randrange(1,6));c=count(t)
            if c<cbest:cbest=c
            if c>70:continue
            n,selection=ca.price(t);countchecks+=1
            if n<best:
                best=n
                print('PHYSBEST',n,'DAG',c,'folds',len(selection),'cfg',cfg,'order',order,flush=True)
                save(t,{'config':cfg,'head_order':order,'word':w},f'coding_best_{n}')
            if n<=198:save(t,{'config':cfg,'head_order':order,'word':w},f'coding_{ci}_{countchecks}_{n}')
        print('CONFIG',ci,cfg,'bestDAG',cbest,'bestphys',best,'seconds',time.time()-start,flush=True)
    print('DONE','bestphys',best,'checks',countchecks,flush=True)

if __name__=='__main__':main()
