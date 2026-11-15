from make_dup_seeds import *
OUT=HERE/'global_search'
base=HERE/'inputs/parameterized_generalizer'
ts=[];meta=[]
for name in ['direct_top_188.grammar.json','newgen_189.grammar.json']:
 t=read(base/name);w=word(t)
 if w[-1]!= 'node49':w[-1]='node49';t=adapt(t,w)
 print(name,len(w),w[:15]);ts.append(t);meta.append(name)
 for s in shapes:ts.append(adapt(s,w));meta.append('adapt:'+name)
f=(OUT/'original.templates.txt').open();nb=int(next(f));fixed=[str(nb)]+[next(f).rstrip()for _ in range(nb)]
MACROS['node75']=332;text=fixed+[str(len(ts))]
for tid,t in enumerate(ts):
 ns,root=tarray(t);text.append(f'{tid} {len(ns)} {root}');text.extend(' '.join(map(str,row))for row in ns)
(OUT/'direct_top.templates.txt').write_text('\n'.join(text)+'\n');(OUT/'direct_top.metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
