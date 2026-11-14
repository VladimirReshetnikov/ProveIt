from search_folds import *
import sys
sys.path.insert(0,str(BASE/'sources/incoming208'))
import compile_ax as c
T,I,root=c.compile_tree(c.g.get_macro_tree()[2],True)
cs=[q for q in c.candidates(T,I) if c.valid_selection(T,[q])]
selections=[]
for n in (5,6):
 for sel in itertools.combinations(cs,n):
  if c.valid_selection(T,sel):selections.append(sel)
print('SELECTIONS',len(selections),flush=True)
start=time.time();hits=[]
for i,sel in enumerate(selections):
 old,p=c.make_fold(T,sel)
 order=[74]+[q for q in c.states(old) if q!=74]+[254];mp={q:i for i,q in enumerate(order)}
 rows={(mp[q],b):(w,1 if d=='R' else -1,mp[t]) for (q,b),(w,d,t) in old.items()}
 reach=reachable(rows,5)
 found=search(rows,reach,5)
 print('LAYOUT',i,'count',len(order)-1,'found',len(found),'secs',time.time()-start,flush=True)
 for f in found:
  a,b=f['a'],f['b'];x=f['symbol'];h=f['helper'];w=f['write'];d=f['move']
  mp2={q:(a if q==b else q) for q in range(len(order))}
  new={(q,s):(ww,dd,mp2[t]) for(q,s),(ww,dd,t) in rows.items() if q!=b}
  new[a,x]=(w,d,mp2[h])
  rec={'layout':i,'selection':sel,'native_labels':order,'fold':f,'table':[[q,s,*act] for(q,s),act in sorted(new.items())]}
  hits.append(rec);(BASE/f'research/layout_fold_{i}_{a}_{b}.json').write_text(json.dumps(rec,indent=2))
(BASE/'research/layout_folds.json').write_text(json.dumps(hits,indent=2))
print('DONE',len(hits),time.time()-start,flush=True)
