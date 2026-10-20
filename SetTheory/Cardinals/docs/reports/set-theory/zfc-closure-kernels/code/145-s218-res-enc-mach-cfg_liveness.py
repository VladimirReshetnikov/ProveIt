from pathlib import Path
import sys,json,collections
sys.path.insert(0,str(Path(__file__).parent/'support/k221/portable'))
import source_language as s
rows=json.loads(Path(sys.argv[1]).read_text());G,_=s.graph_arithmetic(rows);base=Path(sys.argv[2]);bisim=json.loads(base.with_suffix('.json').read_text());J=bisim['identity_closure'];C=bisim['site_classes'];active=sorted(set(J));L={i:0 for i in active};clear={};transfers={};keep=[[0,0]for _ in rows]
for i in active:
 if i<0:continue
 op,tg=G[i]
 if op[0]!='decrement':continue
 r=op[1];j=tg[1];seen=set();body=[];writes=0
 while j!=i and j not in seen:
  seen.add(j);opj,tgj=G[j]
  if opj[0]=='identity':pass
  elif opj[0]=='increment'and opj[1]!=r:writes|=1<<opj[1]
  else:break
  body.append(j);j=tgj[0]
 if j!=i:continue
 clear[i]=r;transfers[i]=writes;keep[i][1]|=1<<r
 for j in body:keep[j][0]|=1<<r;keep[j][1]|=1<<r
rounds=0
while True:
 changed=False;rounds+=1
 for i in reversed(active):
  if i<0:continue
  op,tg=G[i]
  if op[0]=='halt':v=0
  elif i in clear:
   v=L[J[tg[0]]]&~(1<<clear[i])
   if v&transfers[i]:v|=1<<clear[i]
  elif op[0]=='increment':v=L[J[tg[0]]]
  elif op[0]=='decrement':v=L[J[tg[0]]]|L[J[tg[1]]]|(1<<op[1])
  else:raise AssertionError(op)
  assert v|L[i]==v
  if v!=L[i]:L[i]=v;changed=True
 if not changed:break
live=[L[J[i]]for i in range(len(rows))]
r={'clear_loops':clear,'transfer_writes':transfers,'live_masks':live,'edge_keep_masks':keep,'rounds':rounds,'live_bit_histogram':dict(collections.Counter(x.bit_count()for x in live)),'progress_guarded_edges':sum(any(k)for k in keep)}
base.with_name(base.name+'_liveness').with_suffix('.json').write_text(json.dumps(r,indent=2))
base.with_name(base.name+'_liveness').with_suffix('.in').write_text(''.join(f'{pc} {op} {a if a is not None else -1} {C[i]} {live[i]} {keep[i][0]} {keep[i][1]}\n'for i,(pc,op,a)in enumerate(rows)))
print({'clear_loops':len(clear),'rounds':rounds,'live_bit_histogram':r['live_bit_histogram'],'progress_guarded_edges':r['progress_guarded_edges']})
