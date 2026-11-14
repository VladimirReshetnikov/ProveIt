from layout import *
import sys
t=read_grammar(sys.argv[1]);r,index,sh=build(t);ops=opportunities_fast(r,sh);match=max_matching(ops)
sites,ins,cs=source(t)
print('source',len(sites),'maxpath',max(len(p)for p,*_ in sites),'raw',len(r)//2,'matching',match,flush=True)
print('baseline',validate(r,cs),flush=True)
choices=[]
for a,b in match:
    oo=next(o for x,y,o in ops if (x,y)==(a,b))
    choices.append([(a,b,(x,y))for x,y in itertools.product(*oo)])
for selected in itertools.product(*choices):
    alias={a:b for a,b,acts in selected};actions={b:acts for a,b,acts in selected}
    rr={}
    for (q,bit),act in r.items():
        if q in alias:continue
        w,d,n=actions[q][bit]if q in actions else act
        rr[q,bit]=(w,d,alias.get(n,n))
    ans=validate(rr,cs)
    print('test',len(rr)//2,ans,flush=True)
    if ans['ok']:
        Path('transport_folded.json').write_text(json.dumps({'rows':[[q,b,*a]for(q,b),a in sorted(rr.items())],'folds':selected,'source_grammar':sys.argv[1],'source_sites':sites,'validation':ans},indent=2));break
