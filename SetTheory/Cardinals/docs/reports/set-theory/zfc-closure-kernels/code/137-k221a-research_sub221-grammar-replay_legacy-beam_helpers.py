#!/usr/bin/env python3
from helper_fast import *
p=argparse.ArgumentParser();p.add_argument('--depth',type=int,default=6);p.add_argument('--beam',type=int,default=200);p.add_argument('--cost',type=int,default=222);p.add_argument('--start');p.add_argument('--output',default='research_sub221/grammar/helper_beam');a=p.parse_args();out=Path(a.output);out.mkdir(parents=True,exist_ok=True)
tr=Grammar();base=tr.read(json.loads(BASE.read_text()));root=tr.read(json.loads(Path(a.start).read_text()))if a.start else base;front=[(tr.cost(tr.living(root)),root,[])];seen={root};start=time.time();reports=[];saved=0
for depth in range(a.depth):
 nxt=[]
 for index,(oldcost,r,hist)in enumerate(front):
  for n in tr.living(r):
   if tr.leaf(n):continue
   l,rr=tr.nodes[n]
   for d in (0,1):
    if tr.leaf(l if d==0 else rr):continue
    if d==0:x,y=tr.nodes[l];z=rr
    else:x=l;y,z=tr.nodes[rr]
    if tr.bd[x][0]or tr.bd[z][1]:continue
    nn=tr.intern((x,tr.intern((y,z))))if d==0 else tr.intern((tr.intern((x,y)),z));nr=tr.substitute(r,n,nn)
    if nr in seen:continue
    seen.add(nr)
    if tr.zrun[nr]>6 or tr.good[nr]!=15:continue
    cost=tr.cost(tr.living(nr))
    if cost>a.cost:continue
    hh=hist+[(n,nn,d)];nxt.append((cost,nr,hh))
    if cost<221 or (cost==221 and saved<12 and depth>=2 and len(hh)>=3):
     saved+=1;dout=out/f'd{depth+1}_cost{cost}_{saved:04}';dout.mkdir();(dout/'sites.json').write_text(json.dumps(tr.sites(nr),separators=(',',':'))+'\n');res=cc.compile(dout/'sites.json',dout/'compiled');rec=dict(path=str(dout),cost=cost,history=hh,metrics=tr.metrics(nr),**{k:res.get(k)for k in('states','decoder_ok','decoder_failures','error')});reports.append(rec);(dout/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');(out/'results.json').write_text(json.dumps(reports,indent=2)+'\n');print('COMPILED',rec,flush=True)
     if res.get('states',999)<=220 and res.get('decoder_ok'):print('SUCCESS NEEDS INDEPENDENT PROOFS',dout,flush=True);raise SystemExit
  if index%20==19:print('PROGRESS',depth,index,'of',len(front),'next',len(nxt),'nodes',len(tr.nodes),flush=True)
 nxt.sort(key=lambda x:(x[0],tr.depth[x[1]],x[1]));front=nxt[:a.beam];print('DEPTH',depth+1,'generated',len(nxt),'retained',len(front),'best',nxt[0][0]if nxt else None,'seen',len(seen),'nodes',len(tr.nodes),'seconds',round(time.time()-start,2),flush=True)
 if not front:break
print('DONE',flush=True)
