#!/usr/bin/env python3
"""Small data-only independent Report31 geometry, algebra and orbit checks."""
import argparse,json,hashlib
from collections import Counter
from pathlib import Path
from zipfile import ZipFile
ZIP='Binary_Planar_Four_Particle_Shuttle_Package.zip'
ZIP_SHA='08020df876af26b1c8cfbf42aa2a79386375254f573f2e5079c07263689d7d98'
PREFIX='binary-planar-shuttle-release-20261003/'
PINS={
 'README.md':'c9202b6629735360706cdb8d9164a93af034fbd52a1bca18bb0fe9edfc59046d',
 'scientific/PROOF.md':'a10c07b450ad16bd1591091c4dc4c0b241ccb00d99fb58f1a77a2e200752a373',
 'scientific/LOCAL_ALGEBRA.md':'6aaad6679b2ba8cd5fd183203a62a054a8b9defdf9a6b29df94cb65ac18acf60',
 'scientific/audit/drift-and-first-arrivals.md':'32b7fe7cde1a48d25fbe88023661af0d071a498e2b6646833550b9b9b2658029',
 'scientific/local-rule-certificate.json':'92d4f4265004704c44bbf5d53d1e0d61e29ce1c923d7720a4293b8bb2d2ced8c',
 'scientific/local-quartic-certificate.json':'e0d9bd288b86e2d3c521a7e40c5945707e61825f992f1741bc5d64be0ae11613',
 'verification/expected-quartic-counts.json':'d4cf053e5fe09ac952717f99186d16642d587705655eb93a2484c05031e7daee',
}
RULES=[('E',{(0,0),(1,0)},{(1,0),(2,0)}),('W',{(0,0),(2,0)},{(-1,0),(1,0)}),('R',{(0,0),(1,0),(3,0)},{(-1,0),(1,0),(4,1)}),('L',{(0,0),(2,0),(4,0)},{(0,1),(3,1),(4,1)})]
def need(ok,why):
 if not ok:raise ValueError(why)
def sha(b):return hashlib.sha256(b).hexdigest()
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(same(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b) and all(same(x,y)for x,y in zip(a,b))
 return a==b
def shift(s,x,y):return {(a+x,b+y)for a,b in s}
def poly(rows):
 out={}
 for r in rows:
  c,m=r['coefficient'],r['variables'];need(type(c)is int and c!=0 and type(m)is list and m==sorted(m) and all(type(i)is int and 0<=i<693 for i in m),'exact polynomial term')
  need(tuple(m)not in out,'distinct monomial');out[tuple(m)]=c
 return out

def algebra(local,q,expected):
 coords=[(x,y)for y in range(-3,3)for x in range(-6,7)];ix={p:i for i,p in enumerate(coords)}
 need(q['input_coordinates']==[list(p)for p in coords] and q['external_variable_count']==79,'exact external coordinates')
 need(q['variable_order']==['c_'+str(x)+'_'+str(y)for x,y in coords]+['y']+['z_'+str(i)for i in range(614)],'full variable order')
 inds=[];gates=[];res=[];cyl={1:[],-1:[]};drift={1:[],-1:[]};top={};nextvar=79
 for name,A,B in RULES:
  for sign,difference in ((1,B-A),(-1,A-B)):
   for x,y in sorted(difference):
    ones=shift(A,-x,-y);halo={(a+dx,b+dy)for a,b in ones for dx in range(-2,3)for dy in range(-2,3)};zeros=halo-ones
    for dy,collection in ((0,cyl),(-1,drift)):
     mask=lambda s:str(sum(1<<((b+dy+6)*13+a+6)for a,b in s))
     collection[sign].append(dict(ones=mask(ones),zeros=mask(zeros)))
    oi=sorted(ix[p]for p in ones);zi=sorted(ix[p]for p in zeros);current=oi[0]
    for v,complement in [(i,False)for i in oi[1:]]+[(i,True)for i in zi]:
     gates.append(dict(previous=current,input=v,target=nextvar,complement=complement))
     res.append({(nextvar,):1,(current,):-1,tuple(sorted((current,v))):1}if complement else{(nextvar,):1,tuple(sorted((current,v))):-1})
     current=nextvar;nextvar+=1
    inds.append(dict(name=name,anchor=[-x,-y],sign=sign,ones=oi,zeros=zi,result_variable=current))
    if len(halo)==45:top[tuple(sorted(oi+zi))]=sign*(-1)**len(zi)
 need(local['births']==cyl[1] and local['removals']==cyl[-1] and local['drifted_rule']['births']==drift[1] and local['drifted_rule']['removals']==drift[-1],'all32 literal G/F cylinders from geometry')
 need(local['drifted_rule']['baseline_source_bit']==str(1<<((5)*13+6)),'shifted baseline bit')
 need(q['gates']==gates and q['indicators']==inds,'all614 literal gates and16 indicators reconstructed')
 for i in range(78):res.append({(i,i):1,(i,):-1})
 output={(78,):1,(ix[(0,0)],):-1};output.update({(i['result_variable'],):-i['sign']for i in inds});res.append(output)
 need(res==[poly(p)for p in q['residuals']],'all693 complete residuals independently reconstructed')
 full=Counter()
 for p in res:
  for m,c in p.items():
   for n,d in p.items():full[tuple(sorted(m+n))]+=c*d
 full={m:c for m,c in full.items()if c}
 need(full==poly(q['expanded_polynomial']),'entire integer coefficient SOS expansion')
 need(top==poly(q['degree_45_boolean_top_terms']) and len(top)==6 and set().union(*(set(m)for m in top))==set(range(78)),'six distinct nonzero degree45 leaders cover all78 cells')
 counts=dict(auxiliary_variables=len(gates),collected_expanded_terms=len(full),complement_product_gates=sum(g['complement']for g in gates),degree=max(map(len,full)),external_variables=79,input_bits=78,maximum_coefficient_magnitude=max(map(abs,full.values())),ordered_sos_expansion_occurrences=sum(len(p)**2 for p in res),plain_product_gates=sum(not g['complement']for g in gates),residual_monomial_occurrences=sum(map(len,res)),residuals=len(res))
 need(same(counts,q['counts']) and same(counts,expected),'all reported paid syntax counts')
 return dict(cylinders=32,indicators=16,boolean_degree=45,essential_cells=78,counts=counts)

def step(s):
 unseen=set(s);out=set()
 while unseen:
  seed=unseen.pop();component={seed};todo=[seed]
  while todo:
   a,b=todo.pop();neighbors={p for p in unseen if max(abs(p[0]-a),abs(p[1]-b))<=2};unseen-=neighbors;component|=neighbors;todo+=list(neighbors)
  x=min(p[0]for p in component);y=min(p[1]for p in component);shape=shift(component,-x,-y);targets=[shift(B,x,y)for _,A,B in RULES if A==shape]
  new=targets[0]if targets else component;need(not(out&new),'no output collision');out|=new
 need(len(out)==len(s),'finite mass');return out

def orbits():
 phases=arrivals=boxes=0
 for k in (7,8,11):
  T=lambda n:n*n+(2*k-11)*n
  s={(0,0),(3,0),(4,0),(k,0)};seen={};drift=set();n=0
  for t in range(161):
   while T(n+1)<=t:n+=1
   d=k+n;j=t-T(n)
   want={(0,n),(3+j,n),(4+j,n),(d,n)}if j<=d-6 else{(0,n),(d-4-(j-d+5),n),(d-2-(j-d+5),n),(d+1,n+1)}
   need(s==want,'every sampled phase including both boundaries');phases+=1
   for p in s:seen.setdefault(p,t)
   ds={(x,y+t)for x,y in s};need(not(drift&ds),'all four sampled drift traces disjoint');drift|=ds
   s=step(s)
  for row in range(6):
   d=k+row;points={0,d}|set(range(2,d-1));need({x for x,y in seen if y==row}==points,'whole completed visited row')
   for x in points:
    expected=0 if row==0 and x==d else T(row)if x in (0,3,4)else T(row)+2*d-11 if x==2 else T(row)-(d-6)if x==d else T(row)+x-4
    need(seen[(x,row)]==expected,'actual first arrival');arrivals+=1
  for N in range(k+1,81):
   A=sum(T(i)+i-1<=N for i in range(1,100));B=sum(T(i)+k+2*i-5<=N for i in range(100))
   need(sum(0<=x<=N and 0<=y<=N for x,y in drift)==4*(N+1)-3*A-B,'complete bounded drift box count');boxes+=1
  for N in range(0,k+7):
   points={(x,row)for row in range(N+1)for x in ({0,k+row}|set(range(2,k+row-1)))if x<=N}
   wanted=1 if N==0 else N*(N+1)if N<=k-2 else(N*N+(2*k-1)*N-k*k+3*k-4)//2
   need(len(points)==wanted,'stationary closed-set box arithmetic');boxes+=1
 return dict(k_values=[7,8,11],phase_states=phases,first_arrivals=arrivals,box_checks=boxes,scope='Three short independent component simulations and finite formula checks, not all-input enumeration.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo-root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();path=a.repo_root/'docs/incoming'/ZIP
 need(sha(path.read_bytes())==ZIP_SHA,'ZIP pin')
 with ZipFile(path)as z:
  need(len(z.namelist())==len(set(z.namelist())),'unique archive members');blobs={n:z.read(PREFIX+n)for n in PINS}
 for n,b in blobs.items():need(sha(b)==PINS[n],'member pin '+n)
 js=lambda n:json.loads(blobs[n])
 r=dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),archive=ZIP,archive_sha256=ZIP_SHA,member_pins=PINS,local=algebra(js('scientific/local-rule-certificate.json'),js('scientific/local-quartic-certificate.json'),js('verification/expected-quartic-counts.json')),orbits=orbits(),scope='Data-only geometry-to-cylinder/gate/residual/quartic reconstruction and bounded orbit checks. General all-input proof assessed in companion note; no archive Python or historical suite executed, no universality or unbounded Diophantine consequence.')
 if a.expect:need(same(r,json.loads(a.expect.read_text())),'exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],local=r['local'],orbits=r['orbits'])))
if __name__=='__main__':main()
