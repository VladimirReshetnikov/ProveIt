#!/usr/bin/env python3
"""Bounded unpublished source probe; no maintained compiler/API or new bound claim."""
import argparse,copy,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={'three_mass_unbounded_endpoint_projection.py':'96d41f43190547fce121c5271e351af3d2bc99fa2226379e4d24f980bae998dd','three_mass_unbounded_endpoint_projection.json':'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457','three_mass_unbounded_endpoint_projection.md':'8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c'}
def need(x,m):
 if not x:raise ValueError(m)
def run(rows,v):
 e=dict(v)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return e

def verify(root):
 for n,h in PINS.items():need(hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n)
 receipt=json.loads((root/'three_mass_unbounded_endpoint_projection.json').read_text());out=[];counts=Counter();rng=random.Random(592467465468)
 for form in receipt['forms']:
  p=form['packet'];rows=p['source'];h=p['interfaces']['height'];d={n:(op,a,b) for n,op,a,b in rows};K=p['mapping']['K'];qh=p['mapping']['halt']
  h0=d['bridge_height_without_time'][1]
  need(d[h0]==('+','bridge_input','bridge_target'),'actual input-target sum')
  need(d['bridge_height_without_time']==('+',h0,'height_slack') and d['endpoint_raised_height']==('+','bridge_height_without_time',K) and d[h]==('+','endpoint_raised_height','T'),'actual four additions')
  for n,users in [(h0,{'bridge_height_without_time'}),('bridge_height_without_time',{'endpoint_raised_height'}),('endpoint_raised_height',{h}),('height_slack',{'bridge_height_without_time'})]:
   need({dest for dest,op,a,b in rows if n in (a,b)}==users,'private cone')
   need(all(n not in pair for pair in p['comparisons']),'no private comparison')
  new=[]
  for row in rows:
   n,op,a,b=row
   if n in (h0,'endpoint_raised_height'):continue
   if n=='bridge_height_without_time':new.append([n,'+','bridge_input','height_slack'])
   elif n==h:new.append([n,'+','bridge_height_without_time','T'])
   else:new.append(row[:])
  full=new+copy.deepcopy(p['polynomial_source'][len(rows):])
  # Prove h after eta_EP=eta-K*y-qh, then compare every unchanged output
  # via a distinct formal h cut. Target itself is unchanged.
  need(K==5 and qh in (2,3),'actual constants')
  # Coefficient dictionaries in x,y,T,eta,1; n0=5x+1.
  old=[K,K,1,1,1+qh];shift=[0,-K,0,0,-qh];child=[K,0,1,1,1]
  need([a+b for a,b in zip(old,shift)]==child,'exact affine height identity')
  atoms={}
  def iid(t):
   if t not in atoms:atoms[t]=len(atoms)
   return atoms[t]
  def formal(src):
   env={n:iid(('input',n)) for n in p['parameters']+p['auxiliaries']}
   at=lambda v:iid(('int',v)) if type(v)is int else env[v]
   for n,op,a,b in src:env[n]=iid(('proved_height',)) if n==h else iid((op,at(a),at(b)))
   return env
  a=formal(p['polynomial_source']);b=formal(full)
  for l,r in p['comparisons']:need((a[l],a[r])==(b[l],b[r]),'all19 retained operands')
  need(a[p['output']]==b[p['output']],'entire finalizer identity after height cut')
  counts['whole_source_identities']+=1;counts['formal_retained_comparisons']+=19
  # Independent closure/live/complete ledger.
  free=set(p['parameters']+p['auxiliaries']);seen=set(free);deps={};deg={n:1 for n in free};c=Counter()
  for n,op,a,b in full:
   need(n not in seen and all(type(v)is int or v in seen for v in (a,b)),'closed source')
   ds=[0 if type(v)is int else deg[v] for v in (a,b)];deg[n]=sum(ds) if op=='*' else max(ds);deps[n]=(a,b);seen.add(n);c['M' if op=='*' else 'A']+=1
  live=set();todo=[p['output']]
  while todo:
   n=todo.pop()
   if type(n)is int or n in free or n in live:continue
   live.add(n);todo.extend(deps[n])
  need(live==set(deps),'complete liveness')
  need(c['M']==p['polynomial_ledger']['M'] and c['A']==p['polynomial_ledger']['A']-2 and deg[p['output']]==p['degree']['upper_bound'],'full two-addition delta and propagated degree')
  for j in range(16):
   v={n:rng.randrange(-3,4) for n in free};pv=v.copy();pv['height_slack']-=K*v['y']+qh
   e1=run(p['polynomial_source'],pv);e2=run(full,v);need(e1[p['output']]==e2[p['output']],'full signed pullback');counts['signed_full_evaluations']+=1
  fixtures=[];mp=p['mapping'];m=mp['modulus'];table=mp['table'];clocks=mp['clocks']
  for x in [0,1,4,9,19,40,100]:
   path=[K*x+mp['initial']];qs=[];rs=[];ticks=[]
   for _ in range(6):
    q,r=divmod(path[-1]-1,m);a,d0=table[r];cc,bb=clocks[r];qs.append(q);rs.append(r);ticks.append(cc*q+bb);path.append(a*q+d0)
    if (path[-1]-1)%K+1 in (mp['halt'],mp['trap']):break
   if (path[-1]-1)%K+1!=mp['halt']:continue
   T=sum(ticks);y=(path[-1]-qh)//K+1;hh=1
   while hh<=path[0]+T or hh<=max(qs):hh*=2
   C=next(row[2] for row in rows if row[1]=='*' and row[3]=='bridge_height_square');B=C*hh*hh;P=B**len(qs);J=(P-1)//(B-1)
   pack=lambda vals:sum(v*B**i for i,v in enumerate(vals))
   E=[pack([int(r==j) for r in rs]) for j in range(m)];W=pack(qs);base=min(a for a,d0 in table);classes=sorted({a for a,d0 in table}-{base});Z=[pack([q if table[r][0]==a else 0 for q,r in zip(qs,rs)]) for a in classes]
   v={n:1 for n in free};v.update(x=x,y=y,T=T,height_slack=hh-path[0]-T,quotient_hat=W+1,global_slack=P-J-W-1-sum(Z)-len(Z),clock_quotient_hat=1+(pack(ticks)-T)//(B-1));v.update({f'edge{i}_hat':z+1 for i,z in enumerate(E)});v.update({f'product{i}_hat':z+1 for i,z in enumerate(Z)})
   need(all(v[n]>0 for n in p['auxiliaries']),'positive outer witnesses')
   e=run(new,v)
   for l,r in [p['comparisons'][0],p['comparisons'][1],p['comparisons'][-1]]:need(e[l]==e[r],'actual outer equation')
   H=(e['native__padded_A']-12)//16;M=(e['native__padded_B']-10)//16;A=(e['native__F3']-8)//16
   need(H&M==A and e[h]==hh,'joined native AND and height')
   fixtures.append(dict(x=x,y=y,T=T,h=hh,eta=v['height_slack'],signed_coefficient_parent_eta=v['height_slack']-path[-1],signed_endpoint_parent_eta=v['height_slack']-K*y-qh,native_witnesses_materialized=False));counts['genuine_outer_fixtures']+=1
  # Pretyping lower boundary h2 is allowed off-zero.
  v={n:1 for n in free};v.update(x=0,y=0,T=0);e=run(new,v);need(e[h]==2 and e['bridge_target']<=0,'minimum height2 and y0')
  need(e['native__padded_A']>0 and e['native__padded_B']>0 and e['native__F3']>0 and e['native__q']>0,'positive pretyping native ports at boundary')
  counts['height_two_boundaries']+=1
  out.append(dict(variant=p['variant'],source=new,comparisons=p['comparisons'],polynomial_source=full,output=p['output'],parameters=p['parameters'],auxiliaries=p['auxiliaries'],probe_ledger=dict(operations=len(full),M=c['M'],A=c['A'],positive_witnesses=len(p['auxiliaries']),comparisons=19,degree_upper_bound=deg[p['output']],all_gates_live=True),outer_fixtures=fixtures))
 nop=next(f for f in out if f['variant']=='clock_nop');counter=next(f for f in nop['outer_fixtures'] if f['x']==40)
 need((counter['y'],counter['T'],counter['h'],counter['eta'],counter['signed_coefficient_parent_eta'])==(41,7880,8192,111,-91),'loss of positive same-coordinate lift')
 return dict(status='PASS bounded probe; not independently reviewed or promoted',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),pins=PINS,counts=dict(counts),forms=out)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path('/tmp'));ap.add_argument('--output',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']}))
