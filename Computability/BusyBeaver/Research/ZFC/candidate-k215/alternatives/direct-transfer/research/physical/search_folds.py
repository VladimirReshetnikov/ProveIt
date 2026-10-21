from pathlib import Path
import importlib.util,json,itertools,time,argparse,gzip
R=Path(__file__).resolve().parent
def mod(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
b=mod('b',R/'vendor/check_joint_fold.py')
f=mod('f',R/'vendor/search_v3.py')
a=argparse.ArgumentParser();a.add_argument('--table',type=Path,default=R/'inputs/k215.native.tm');a.add_argument('--radius',type=int,default=5);a.add_argument('--output',type=Path,required=True);a=a.parse_args();a.output.mkdir(parents=True,exist_ok=True)
T,st=b.read(a.table);Q=sorted({q for q,_ in T});print('domain',flush=True);I=b.domain(T,st,a.radius);print('contexts',sum(map(len,I.values())),flush=True);cache={};tried=0;hits=[];t=time.time()
for keep,drop in itertools.combinations(Q,2):
 if drop==st:continue
 phi=lambda q:keep if q==drop else q
 N={(q,c):(w,d,phi(z)) for (q,c),(w,d,z) in T.items() if q!=drop}
 actions=[sorted({(T[q,c][0],T[q,c][1],phi(T[q,c][2])) for q in (keep,drop)}) for c in (0,1)]
 common=[c for c in (0,1) if len(actions[c])==1]
 variants=list(itertools.product(*actions))
 if len(common)==1:
  c=common[0]
  for w,d,z in itertools.product((0,1),(-1,1),sorted(set(Q)-{drop}|{254})):
   act=(w,d,z)
   if act in actions[1-c]:continue
   pair=[None,None];pair[c]=actions[c][0];pair[1-c]=act;variants.append(tuple(pair))
 for x,y in variants:
  tried+=1;N[keep,0]=x;N[keep,1]=y
  failure=f.local_filter(T,N,I,keep,drop,cache,97,a.radius)
  if failure is None:
   print('HIT',keep,drop,x,y,flush=True)
   try:r=b.check(T,N,st,st,keep,drop,a.radius,97,I)
   except Exception as e:print('FAIL',e,flush=True);continue
   p=a.output/f'fold-{keep}-{drop}-{len(hits)}.tm';p.write_bytes(f.encode(N,st));hits.append({'keep':keep,'drop':drop,'rows':[x,y],'proof':r,'table':str(p)});(a.output/'hits.json').write_text(json.dumps(hits,indent=2))
 if keep%10==0 and drop==Q[-1]:print('progress',keep,tried,round(time.time()-t,2),flush=True)
(a.output/'result.json').write_text(json.dumps({'tried':tried,'hits':hits,'seconds':time.time()-t,'radius':a.radius,'fuel':97},indent=2))
print('DONE',tried,len(hits),time.time()-t,flush=True)
