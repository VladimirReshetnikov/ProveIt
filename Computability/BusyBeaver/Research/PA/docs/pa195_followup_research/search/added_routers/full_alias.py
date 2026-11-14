import sys,json,time,collections
from pathlib import Path
P=(Path(__file__).resolve().parent / 'reference_pa195');sys.path.insert(0,str(P));import build_verify as v
c=v.c;OUT=Path(__file__).resolve().parent;rows=v.table(P/'pa195.native.tm');t=c.read_grammar(P/'grammar.json');sites,cfg,cs=c.source(t);byh=collections.defaultdict(list)
for ci,cc in enumerate(cs):
 seen=set();assert c.run(rows,cc,observe=lambda s:seen.add(s[0])) is not None
 for h in seen:byh[h].append(ci)
states=sorted({q for q,b in rows});protected=c.BOXSTATES|{74}|{n for(q,b),(w,d,n)in rows.items()if q in c.BOXSTATES};hs=[h for h in states if h not in protected]
count=0;survive=[];started=time.time()
for h in hs:
 for u in states:
  if u==h:continue
  rr={(q,b):(w,d,u if n==h else n) for(q,b),(w,d,n)in rows.items() if q!=h};count+=1
  if any(c.run(rr,cs[ci]) is None for ci in byh[h]):continue
  rv=c.validate(rr,cs);assert rv['ok'];name=f'alias194_{h}_{u}';print('SURVIVOR',name,rv,flush=True)
  labels=[74]+sorted({q for q,b in rr}-{74})+[254];rev={q:i for i,q in enumerate(labels)};dense={(rev[q],b):(w,d,rev[n]) for(q,b),(w,d,n)in rr.items()}
  try:st=v.startup(dense,labels)
  except Exception as e:print('BAD_STARTUP',name,repr(e),flush=True);continue
  (OUT/(name+'.native.tm')).write_bytes(v.table_bytes(rr));(OUT/(name+'.tm')).write_bytes(v.table_bytes(dense));(OUT/(name+'.labels.json')).write_text(json.dumps(labels));data={'deleted':h,'alias':u,'runtime':rv,'startup':st,'protected_engine_rows_unchanged':True};(OUT/(name+'.validation.json')).write_text(json.dumps(data,indent=2));survive.append(data);print('SUCCESS',name,flush=True)
 print('PROGRESS',h,count,'survivors',len(survive),'time',time.time()-started,flush=True)
(OUT/'full_alias_results.json').write_text(json.dumps({'cases':count,'states_considered':hs,'survivors':survive},indent=2));print('DONE',count,len(survive),time.time()-started,flush=True)
