from trace_origin import *
def target(site,vals,header=56,spares=(0,)):
 pc,op,arg=site; vals=vals.copy();overflow=0;delta=0;spares=list(spares)
 if op=='CI':vals[arg]+=1;pc,overflow=ir.inc(pc);spares.append(1)
 elif op=='CD' and vals[arg]>0:vals[arg]-=1;pc,overflow=ir.inc(pc);delta=1
 elif op in ('CD','CB'):pc,overflow=ir.inc(ir.strip(pc,'0',arg if op=='CB' else 1))
 elif op=='CC':pc=ir.strip(pc,'1',arg)
 elif op=='CH':return None
 ones=frame([pc,op,arg],vals,header=header+delta+overflow,spares=spares)
 return 84,-overflow,sorted(x-overflow for x in ones)
def primitive(table,site,vals,maxsteps=20000,header=56,log=False):
 ones=frame(site,vals,header=header);q=84;h=0;trace=[];goal=target(site,vals,header)
 for i in range(maxsteps):
  b=int(h in ones);w,d,z=table[q,b]
  if log and q in [23,34,75,84]:trace.append((i,q,h,b,w,d,z,[(j,int(j in ones)) for j in range(h-12,h+13)]))
  ones.add(h) if w else ones.discard(h);h+=d;q=z
  if (q,h,sorted(ones))==goal or q==254:return {'steps':i+1,'q':q,'h':h,'ones':sorted(ones),'trace':trace}
 return {'steps':maxsteps,'q':q,'h':h,'ones':sorted(ones),'trace':trace,'fail':True}
if __name__=='__main__':
 U=T.copy();U[23,0]=(0,-1,75);U.pop((34,0));U.pop((34,1))
 for pos in [0,1]:
  vals=[0]*9;vals[8]=pos
  a=primitive(T,sites[0],vals,log=True);b=primitive(U,sites[0],vals,log=True)
  print('POS',pos,'BASE', {k:v for k,v in a.items() if k not in ('trace','ones')},'NEW', {k:v for k,v in b.items() if k not in ('trace','ones')})
  Path(f'analysis/runtime_redesign/primitive_{pos}.json').write_text(json.dumps({'base':a,'short':b},indent=2))
  print('BASE TRACE')
  for row in a['trace']:print(row[:7],''.join(str(bit) for j,bit in row[7]))
  print('NEW TRACE')
  for row in b['trace'][:120]:print(row[:7],''.join(str(bit) for j,bit in row[7]))
