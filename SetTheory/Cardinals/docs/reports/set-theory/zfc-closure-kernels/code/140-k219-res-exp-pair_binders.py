from additive_binder import *
from functools import cache
@cache
def assocs(xs):
 if len(xs)==1:return(xs[0],)
 return tuple((l,r)for i in range(1,len(xs))for l in assocs(xs[:i])for r in assocs(xs[i:]))
IMP=q(90)
assert IMP[1][1]==(('CD',7),((((INC,INC),(INC,INC))),('CC',2)))
OUT=ROOT/'research_calculus/generated/pair_binders';OUT.mkdir(parents=True,exist_ok=True)
records=[]
for scale in [1,2,3,4]:
 if scale==1:incblock=INC
 elif scale==2:incblock=(INC,INC)
 elif scale==3:incblock=((INC,INC),INC)
 else:incblock=((INC,INC),(INC,INC))
 PM=(IMP[0],(IMP[1][0],(('CD',7),(incblock,('CC',2)))))
 for tag in range(4):
  if scale==1 and tag==0:continue
  for order in ['ab','ba']:
   x,y=(A,B)if order=='ab'else(B,A)
   for shape in ['r','l','outer_r','outer_l']:
    ct=serial([PM]+[INC]*tag)if tag else PM
    if shape=='r':n=x,(y,ct)
    elif shape=='l':n=(x,y),ct
    elif shape=='outer_r':n=serial([(x,(y,PM))]+[INC]*tag)if tag else(x,(y,PM))
    else:n=serial([((x,y),PM)]+[INC]*tag)if tag else((x,y),PM)
    new=s.replace(TREE,PATH,n);name=f'{scale}_{tag}_{order}_{shape}'
    r={'name':name,'metrics':s.metrics(new)}
    try:
     tt,m=compile_tree(T,TREE,new);r['compile']=m
     if m['working_states']<=221:
      d=OUT/name;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(s.sites(new)));(d/'candidate.tm').write_bytes(b.table_bytes(tt))
    except Exception as e:r['error']=repr(e)
    records.append(r)
    if r.get('compile',{}).get('working_states',999)<=221:print(json.dumps(r),flush=True)
(OUT/'summary.json').write_text(json.dumps(records,indent=2)+'\n')
print('variants',len(records),'best',min(r.get('compile',{}).get('working_states',999)for r in records))
