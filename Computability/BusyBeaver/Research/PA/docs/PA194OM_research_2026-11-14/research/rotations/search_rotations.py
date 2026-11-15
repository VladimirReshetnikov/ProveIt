from pathlib import Path
import json,sys,time,collections,itertools,hashlib
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/'vendor'))
import compiler as c,support as s,engine_helpers as e
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=BASE/'rerun');args=ap.parse_args()
OUT=args.output;OUT.mkdir(parents=True,exist_ok=True)
P=BASE/'inputs'
nodes={k:e.tup(v)for k,v in json.loads((P/'AX11H.nodes.json').read_text()).items()}
g=c.read_grammar(P/'AX11H.grammar.json')
fixed={k:v for k,v in s.read_table(P/'primary.raw.native.tm').items()if k[0]<1300}
fixed[164,1]=(1,True,114)
for q,b,a in json.loads((P/'h_shift_edits.json').read_text()):fixed[q,b]=tuple(a)
c.machine=lambda:(fixed,[]);c.raw_nodes=lambda:nodes
INC=('leaf','inc',1);c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
raw,index,shape=c.build(g);folds=json.loads((P/'primary.folds.json').read_text())
base,ali=s.apply_folds(raw,folds)
sites,ins,cs=c.source(g)
mapping=collections.defaultdict(set)
def branch(q):return all(raw[q,b][0:2]==(b,True)for b in(0,1))
def walk(t,q):
    if isinstance(t,str):
        mapping[t].add(q)
        t=g if t=='x67' else nodes[t]
    if not isinstance(t,tuple)or len(t)!=2 or not branch(q):return
    for b in(0,1):walk(t[b],raw[q,b][2])
walk('node172',84)
def expand(t):return nodes[t]if isinstance(t,str) and t!='x67'else t
def reach(rows):
    seen={74};todo=[74]
    for q in todo:
        for b in(0,1):
            t=rows[q,b][2]
            if t!=254 and t not in seen:seen.add(t);todo.append(t)
    return {k:v for k,v in rows.items()if k[0]in seen}
records=[]
for name,qs in sorted(mapping.items()):
    if name=='x67' or len(qs)!=1:continue
    q=next(iter(qs));t=nodes[name]
    if not branch(q):continue
    for side in(0,1):
        child=expand(t[side]);other=t[1-side]
        if not c.isnode(child):continue
        old=raw[q,side][2]
        if not branch(old):continue
        if side==0:
            A,B=child;C=other
            new=(A,(B,C));pair=((0,True,raw[old,1][2]),(1,True,raw[q,1][2]))
            left=(0,True,raw[old,0][2]);right=None
        else:
            A=other;B,C=child
            new=((A,B),C);pair=((0,True,raw[q,0][2]),(1,True,raw[old,0][2]))
            left=None;right=(1,True,raw[old,1][2])
        nn=dict(nodes);nn[name]=new
        c.raw_nodes=lambda:nn
        try:ss,ii,cc=c.source(g)
        except Exception as ex:continue
        if ii!=ins:continue
        providers=[r for r in {r for r,b in raw}if r!=q and (raw[r,0],raw[r,1])==pair]
        providers+= [old,4000]
        for r in dict.fromkeys(providers):
            rr=dict(raw);rr[r,0],rr[r,1]=pair
            rr[q,0]=left or (0,True,r);rr[q,1]=right or (1,True,r)
            childrows,aa=s.apply_folds(rr,folds)
            try:s.check_local_folds(rr,childrows,aa,folds)
            except Exception:continue
            try:childrows=reach(childrows)
            except KeyError:continue
            count=len(childrows)//2
            if count>194:continue
            tag=f'{name}_{side}_{r}_{count}'
            print('trial',tag,flush=True)
            cv=c.validate(childrows,cc)
            rec=dict(tag=tag,node=name,side=side,root=q,old=old,new=r,count=count,source_same=True,validation=cv)
            if cv['ok']:
                try:rec['startup']=s.startup(childrows,ss[25][0])
                except Exception as ex:rec['startup_error']=str(ex)
                dest=OUT/tag;dest.mkdir(exist_ok=True)
                (dest/'machine.native.tm').write_text(s.table_text(childrows))
                for fname,data in [('nodes.json',nn),('sites.json',ss),('instructions.json',ii),('receipt.json',rec)]:
                    (dest/fname).write_text(json.dumps(data,indent=2)+'\n')
            print(json.dumps(rec),flush=True);records.append(rec)
(OUT/'results.json').write_text(json.dumps(records,indent=2)+'\n')
print('DONE',len(records),'accepted',sum(x['validation']['ok'] and 'startup'in x for x in records),flush=True)
