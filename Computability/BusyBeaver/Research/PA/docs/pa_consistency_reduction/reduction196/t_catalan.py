from t_only import *
from search_top_shapes import shapes,expand,fastcodes

if __name__=='__main__':
    start=time.time();old,defs=S.source_tree();mb,tb=setup();oldcodes=fastcodes(S.flatten(tb))
    htot=(('leaf',('dec',5)),defs['node38'])
    leaves=[defs['node36'],defs['node167'],defs['node37'],htot,defs['node19']]
    ent=[120,11,28,2000,31];tested=0;best=198
    for si,sh in enumerate(shapes(0,5)):
        repl=expand(sh,leaves);tree=C.replace(old,defs['node170'],repl);sites=S.flatten(tree)
        try:
            if fastcodes(sites)!=oldcodes:continue
        except ValueError:continue
        for perm in itertools.permutations((37,133,2001)):
            ids=iter(perm);m=mb.copy()
            def emit(x,root=False):
                if isinstance(x,int):return ent[x]
                a=emit(x[0]);b=emit(x[1]);q=127 if root else next(ids)
                m[q,0]=(0,1,a);m[q,1]=(1,1,b)
                return q
            emit(sh,True);S.all_sites=lambda:sites
            protect={q for q,b in S.ENGINE_ROWS}|{m[k][2]for k in S.ENGINE_ROWS}|{0,S.ROOT}
            opts=F.candidates(m,{q for q,b in m if q not in protect});sel,_=F.best_subset(m,opts)
            n,_=F.fold(m,sel);count=len(n)//2;tested+=1
            if count<=best:
                print('SCORE',si,perm,count,sel,flush=True);best=count
                fails=[]
                for i,b,br,s,z in S.contracts():
                    if S.execute(n,br,s,z)is None:fails.append((i,b))
                print('CHECK',si,perm,len(fails),fails[:10],flush=True)
                if not fails:
                    p=Path(__file__).with_name(f't_catalan_{count}_{si}_'+ '_'.join(map(str,perm)))
                    p.with_suffix('.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {t}\n'for(q,b),(w,d,t)in sorted(n.items())))
                    p.with_suffix('.json').write_text(json.dumps(dict(tree=tree,folds=sel)))
    print('DONE',tested,best,time.time()-start,flush=True)
