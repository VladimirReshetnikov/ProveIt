#!/usr/bin/env python3
"""Independent finite certificate checker; imports neither builder nor search.

Finite algebra authenticates the explicit polynomial and its exact projection.
The unbounded logical equivalence is the separately retained ordinary proof.
"""
from pathlib import Path
import json,hashlib,math,copy,sys
ROOT=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def read(name):return json.loads((ROOT/name).read_text())
def poly(ts):
 out={}
 for c,m in ts:
  key=tuple(sorted(m));out[key]=out.get(key,0)+c
 return {m:c for m,c in out.items() if c}
def plus(*args):
 out={}
 for p in args:
  for m,c in p.items():out[m]=out.get(m,0)+c
 return {m:c for m,c in out.items() if c}
def times(p,q):
 out={}
 for m,c in p.items():
  for n,d in q.items():
   k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def product(ps):
 out={():1}
 for p in ps:out=times(out,p)
 return out
def variable(i):return {(i,):1}
ONE={():1}
def verify_source():
 p=read('parent206.json');s=read('source206.json');c=read('orientation_certificate.json');f=read('factored_pool.json');r=c['orientation_row']
 require(hashlib.sha256((ROOT/'parent206.json').read_bytes()).hexdigest()==c['parent_sha256'],'frozen parent hash')
 require(p['variables']==s['variables'] and len(p['residuals'])==len(s['residuals']),'source dimensions')
 require([i for i,row in enumerate(p['residuals']) if any(c['quotient'] in m for a,m in row['terms'])]==[r],'orientation quotient is private')
 for i,(a,b) in enumerate(zip(p['residuals'],s['residuals'])):
  if i!=r:require(a==b,'unpermitted source edit '+str(i))
 old={};lin={};tri={};norm={};dlt={};yy={};zz={}
 for pair in c['pairs']:
  X,Y,Z,K=[poly(pair[k]) for k in ('X','Y','Z','index')];Xm=plus(X,neg(ONE));err=plus(Y,neg(K));err2=times(err,err)
  old=plus(old,times(Xm,Xm),err2);lin=plus(lin,neg(Xm),err2);tri=plus(tri,times(X,Xm),err2)
  norm=plus(norm,poly(p['residuals'][pair['norm_row']]['terms']));dlt=plus(dlt,Xm);yy=plus(yy,times(Y,Y));zz=plus(zz,times(Z,Z))
 M=plus(poly(c['center']),neg(ONE));MQ=times(M,variable(c['quotient']))
 require(plus(old,neg(norm),neg(MQ))==poly(p['residuals'][r]['terms']),'old orientation identity')
 require(plus(lin,neg(MQ))==poly(s['residuals'][r]['terms']),'affine orientation identity')
 require(plus(tri,neg(norm),neg(MQ))==poly(c['triangular_row']),'triangular orientation identity')
 require(plus(poly(c['triangular_row']),neg(poly(c['new_row'])))==plus(zz,neg(yy)),'triangular affine quotient shear')
 require(poly(c['old_row'])==poly(p['residuals'][r]['terms']) and poly(c['new_row'])==poly(s['residuals'][r]['terms']),'printed orientation rows')
 for key,expected in [('old_full_error',old),('triangular_full_error',tri),('linear_full_error',lin),('ordinate_square_sum',yy),('AY_square_sum',zz),('added_delta',dlt)]:require(poly(c[key])==expected,'orientation certificate '+key)
 ts=[poly(b['T']) for b in f['blocks']];es=[poly(b['E']) for b in f['blocks']];bs=[poly(b['base']) for b in f['blocks']]
 pool=plus(*(product([bs[i],es[i]]+ts[:i]+ts[i+1:]) for i in range(5)),neg(product([variable(f['pool_coordinates'][0])]+ts)))
 require(pool==poly(s['residuals'][-1]['terms']),'factored pool expansion')
 return s,f
def check_graph(g):
 source_file=g['source_file'];raw=(ROOT/source_file).read_bytes();s=json.loads(raw);f=read('factored_pool.json');R=[poly(r['terms']) for r in s['residuals']];N=len(s['variables']);G=g['nodes'];ip=g['source_input_indices']
 require(g['source_sha256']==hashlib.sha256(raw).hexdigest(),'graph source hash')
 require(g['parent_sha256']==hashlib.sha256((ROOT/'parent206.json').read_bytes()).hexdigest(),'graph parent hash')
 require(len(set(ip))==len(ip) and all(0<=i<N for i in ip),'free coordinate list')
 for i,nd in enumerate(G):
  require(isinstance(nd,list) and nd[0] in ('var','const','+','-','*'),'invalid node')
  if nd[0]=='var':require(len(nd)==2 and 0<=nd[1]<len(ip),'input node')
  elif nd[0]=='const':require(len(nd)==2 and isinstance(nd[1],int),'integer literal')
  else:require(len(nd)==3 and all(isinstance(j,int) and 0<=j<i for j in nd[1:]),'backward node reference')
 require(G[:len(ip)]==[['var',i] for i in range(len(ip))],'input node order')
 require(not any(nd[0]=='var' for nd in G[len(ip):]),'duplicate input leaves')
 defs={};used=set()
 for st in g['source_definitions']:
  r,v=st['row'],st['variable'];require(r not in used and v not in defs,'duplicate pivot')
  p=R[r];a=p.get((v,),0);require(a in (-1,1) and not any(v in m for m in p if m!=(v,)),'nonunit pivot')
  defs[v]=(r,{m:-a*c for m,c in p.items() if m!=(v,)});used.add(r)
 require(ip==[i for i in range(N) if i not in defs],'projected input order')
 require(g['variables']==[dict(source_index=i,**s['variables'][i]) for i in ip],'input metadata')
 ports={j:variable(i) for j,i in enumerate(ip)};source_roots=dict(zip(ip,range(len(ip))));checked_defs=set();residuals=[];retained=[];macros={}
 def expand(root,boundary):
  memo={}
  def go(i):
   if i in boundary:return boundary[i]
   if i in memo:return memo[i]
   op,*a=G[i]
   if op=='const':out={():a[0]} if a[0] else {}
   elif op=='var':raise ValueError('undeclared source input in block')
   else:
    x,y=go(a[0]),go(a[1]);out=plus(x,y) if op=='+' else plus(x,neg(y)) if op=='-' else times(x,y)
   memo[i]=out;return out
  return go(root)
 for block in g['blocks']:
  k=block['kind'];root=block['root'];require(0<=root<len(G),'block root')
  if k=='definition':
   v=block['source_variable'];r=block['source_row'];require(v in defs and defs[v][0]==r and v not in checked_defs,'definition binding')
   require(all(j in source_roots for m in defs[v][1] for j in m),'acyclic definition order')
   require(expand(root,ports)==defs[v][1],'definition coefficients '+str(v))
   require(root not in ports,'definition root aliases another coordinate')
   ports[root]=variable(v);source_roots[v]=root;checked_defs.add(v)
  elif k=='residual':
   r=block['source_row'];require(r not in used and r<len(R)-1,'retained source row')
   require(expand(root,ports)==R[r],'residual coefficients '+str(r));residuals.append(root);retained.append(r)
  elif k=='pool_macro':
   j,field=block['block'],block['field'];require(field in ('base','T','E'),'macro field')
   require(expand(root,ports)==poly(f['blocks'][j][field]),'pool macro coefficients');macros[j,field]=root
  elif k=='pool':
   r=block['source_row'];require(r==len(R)-1,'pool source row')
   ts=[macros[i,'T'] for i in range(5)];es=[macros[i,'E'] for i in range(5)];bs=[macros[i,'base'] for i in range(5)];q=source_roots[f['pool_coordinates'][0]]
   portids=set(ts+es+bs+[q]);bp={i:variable(i) for i in portids};expected=plus(*(product([variable(bs[i]),variable(es[i])]+[variable(t) for t in ts[:i]+ts[i+1:]]) for i in range(5)),neg(product([variable(q)]+[variable(t) for t in ts])))
   require(expand(root,bp)==expected,'literal five-base pool formula');residuals.append(root);retained.append(r)
  else:raise ValueError('unknown block kind')
 require(checked_defs==set(defs),'missing definitions')
 require(g['restore_source_roots']==[source_roots[i] for i in range(N)],'source restoration graph')
 require(retained==[r for r in range(len(R)) if r not in used] and retained==g['retained_source_rows'],'complete source row partition')
 require(residuals==g['residual_roots'],'residual root list')
 require(expand(g['output'],{r:variable(r) for r in residuals})=={(r,r):1 for r in residuals},'complete sum of squares')
 # Independently reconstruct upper degrees and a nonzero leading ray.
 dc=g['degree_certificate'];mod=dc['modulus'];require(mod==1000000007,'degree modulus');dd={i:1 for i in ip};tt=dict(zip(ip,dc['direction']));hh={i:0 for i in ip}
 require(dc['direction']==[i+3 for i in ip],'degree ray')
 def stat(p):
  d=max((sum(dd[j] for j in m) for m in p),default=0)
  lead=sum(c*math.prod(tt[j] for j in m) for m,c in p.items() if sum(dd[j] for j in m)==d)%mod
  h=max(((abs(c)-1).bit_length()+sum(hh[j] for j in m) for m,c in p.items()),default=0)+(len(p)-1).bit_length() if p else 0
  return d,lead,h
 for b in g['blocks']:
  if b['kind']=='definition':
   v=b['source_variable'];dd[v],tt[v],hh[v]=stat(defs[v][1])
 values=[stat(R[r]) for r in retained];rd=[x[0] for x in values];rt=[x[1] for x in values];rh=[x[2] for x in values]
 require(dc['source_degrees']==[dd[i] for i in range(N)] and dc['source_leading_coefficients']==[tt[i]%mod for i in range(N)],'source leading certificate')
 require(dc['residual_degrees']==rd and dc['residual_leading_coefficients']==rt,'residual leading certificate')
 D=max(rd);j=retained.index(dc['witness_source_row']);require(rd[j]==D and rt[j]!=0 and dc['witness_residue']==rt[j],'nonzero maximal leading coefficient')
 # Reverse-mode derivatives give independent input-occurrence witnesses.
 occurrence=[False]*len(ip)
 for proof in g['input_occurrence_certificates']:
  prime=proof['modulus'];point=proof['point'];require(prime==1000000007 and len(point)==len(ip),'derivative point')
  val=[]
  for nd in G:
   op=nd[0]
   if op=='var':z=point[nd[1]]
   elif op=='const':z=nd[1]
   else:
    a,b=nd[1:];z=val[a]+val[b] if op=='+' else val[a]-val[b] if op=='-' else val[a]*val[b]
   val.append(z%prime)
  adj=[0]*len(G);adj[g['output']]=1
  for i in range(len(G)-1,-1,-1):
   nd=G[i];op=nd[0]
   if op in ('+','-','*'):
    a,b=nd[1:];da=1 if op in ('+','-') else val[b];db=1 if op=='+' else -1 if op=='-' else val[a]
    adj[a]=(adj[a]+adj[i]*da)%prime;adj[b]=(adj[b]+adj[i]*db)%prime
  actual=adj[:len(ip)];require(actual==proof['derivatives'],'input derivative certificate');occurrence=[a or bool(b) for a,b in zip(occurrence,actual)]
 require(all(occurrence),'inactive input')
 live=set();todo=[g['output']]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if G[i][0] in ('+','-','*'):todo.extend(G[i][1:])
 metrics={'variables':len(ip),'residuals':len(retained),'exact_degree':2*D,'binary_operations':sum(G[i][0] in ('+','-','*') for i in live),'live_nodes':len(live),'stored_nodes':len(G),'largest_literal':max(abs(G[i][1]) for i in live if G[i][0]=='const'),'coefficient_height_strict_power_of_two':2*max(rh)+(len(rh)-1).bit_length()+1}
 require(g['metrics']==metrics,'reported metrics')
 return metrics
def main():
 verify_source();results=[]
 for p in read('PROFILES.json'):
  g=read('equations/'+p['name']+'.json');metrics=check_graph(g);results.append(dict(name=p['name'],**metrics))
 # Four material corruption controls are required to fail.
 g=read('equations/integer84_degree2097808.json');bad=[]
 x=copy.deepcopy(g);x['metrics']['variables']+=1;bad.append(x)
 x=copy.deepcopy(g);x['degree_certificate']['witness_residue']=0;bad.append(x)
 x=copy.deepcopy(g);x['nodes'][x['output']][0]='-';bad.append(x)
 x=copy.deepcopy(g);x['source_definitions'][0]['variable']=142;bad.append(x)
 for x in bad:
  try:check_graph(x)
  except (ValueError,IndexError,KeyError,RecursionError):pass
  else:raise ValueError('accepted deliberate corruption')
 receipt={'status':'PASS','profiles':results,'negative_controls':len(bad),'source_edit':'source136 affine orientation, exact row135 binding','scope':'finite algebra and complete expression authentication; unbounded semantic proof retained separately'}
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
