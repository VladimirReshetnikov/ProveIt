from pathlib import Path
exec((Path(__file__).resolve().parent / 'exhaust_context.py').read_text().split('choices={}')[0])
import importlib.util
sp=importlib.util.spec_from_file_location('audit',BASE/'code/audit_routing_grammar.py');audit=importlib.util.module_from_spec(sp);sp.loader.exec_module(audit);audit.BASE=OUT.parent
ax=max(roots,key=len);A='eijkKC';C='VqkjGqkjGVqkjG'
def fringe(w,lo,hi):
 if lo==hi:return []
 if lo==0 and hi==len(w):return [w]
 a,b=g[w];n=len(a)
 return (fringe(a,lo,min(hi,n)) if lo<n else [])+(fringe(b,max(lo-n,0),hi-n) if hi>n else [])
def reparse(d,parts):
 n=len(parts);dp={};word={}
 for i in range(n):
  for j in range(i+1,n+1):word[i,j]=''.join(parts[i:j])
  dp[i,i+1]=(0,None)
 for k in range(2,n+1):
  for i in range(n-k+1):
   j=i+k;w=word[i,j]
   if w in d:dp[i,j]=(0,None);continue
   opts=[(1+dp[i,h][0]+dp[h,j][0],h) for h in range(i+1,j) if allowed_side(word[i,h],0) and allowed_side(word[h,j],1)]
   dp[i,j]=min(opts,default=(10**9,None))
 def install(i,j):
  w=word[i,j];k=dp[i,j][1]
  if k is not None:
   a,b=install(i,k),install(k,j);d[w]=(a,b)
  return w
 return install(0,n)
cs153=next(cs for s,b,cs in groups if(s,b)==(153,1));states153=[(q,p) for q in g for p in force(q,tuple(cs153)) if q!=routes[153,1]]
print('Alternative153',len(states153));hits=[]
for k in range(len(A)+1,len(ax)-len(C)):
 if ax[k:k+len(C)]!=C:continue
 for route153,plan153 in states153:
  d=g.copy();x=reparse(d,fringe(ax,len(A),k));y=reparse(d,fringe(ax,k+len(C),len(ax)))
  left,right=A+x,C+y
  if not all([allowed_side(A,0),allowed_side(x,1),allowed_side(C,0),allowed_side(y,1)]):continue
  d[left]=(A,x);d[right]=(C,y);d[ax]=(left,right)
  for q,l,r in plan153:d[q]=(l,r)
  rs=routes.copy();rs[153,1]=route153;rs[159,0]=ax
  good=True
  for source,read,cs in groups:
   if match(d,rs[source,read],cs):continue
   opts=[q for q in d if match(d,q,cs)]
   if not opts:good=False;break
   rs[source,read]=min(opts,key=lambda w:(len(w),w))
  if not good:continue
  d=close(d,rs)
  if d is None:continue
  n=len(d)
  out=dict(gram);out.update(rules_count=n,roots=roots,rules=[[q,*d[q]] for q in sorted(d)],routes=[dict(source=s,read=b,word=w) for(s,b),w in sorted(rs.items())],properties=[])
  p=OUT/f'route-ax-{k}-k{n}.json';p.write_text(json.dumps(out,indent=2)+'\n')
  try:
   result=audit.audit(p,short_scan=True,allow_scanner_risk=True);props=result['search_AST_properties'];out['properties']=[props['leading_zeros'],props['maximum_zero_run'],props['depth']];p.write_text(json.dumps(out,indent=2)+'\n');(OUT/f'route-ax-{k}-k{n}-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(k,n,props,flush=True);hits.append(dict(position=k,rules=n,properties=props,file=p.name))
  except Exception as e: print('INVALID',k,n,repr(e))
(OUT/'route-ax-summary.json').write_text(json.dumps(hits,indent=2)+'\n')
