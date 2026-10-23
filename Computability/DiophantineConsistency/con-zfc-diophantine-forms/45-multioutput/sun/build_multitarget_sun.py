#!/usr/bin/env python3
"""New authored simultaneous-quadratic source builder, ten integer variables."""
from pathlib import Path
from collections import defaultdict,Counter
import json,math
from build_weighted_sun import DAG,geom
ROOT=Path(__file__).resolve().parent
BETA_EXP=2134940

def load_common_parent():
 raw=json.loads((ROOT/'data/parent_system60.json').read_text());zero=(0,)*35
 def add(a,b,sign=1):
  ans=dict(a)
  for k,v in b.items():ans[k]=ans.get(k,0)+sign*v
  return {k:v for k,v in ans.items() if v}
 def mul(a,b):
  ans=defaultdict(int)
  for aa,x in a.items():
   for bb,y in b.items():ans[tuple(u+v for u,v in zip(aa,bb))]+=x*y
  return {k:v for k,v in ans.items() if v}
 env={}
 for i,name in enumerate(raw['variables']+raw['constants']):
  aa=list(zero);aa[i]=1;env[name]={tuple(aa):1}
 def get(x):return {zero:x} if isinstance(x,int) else env[x]
 for name,op,a,b in raw['source']:
  env[name]=mul(get(a),get(b)) if op=='*' else add(get(a),get(b),-1 if op=='-' else 1)
 eqs=[]
 for j,(a,b) in enumerate(raw['comparisons'],1):
  pol=add(get(a),get(b),-1)
  eqs.append({'number':j,'terms':[{'powers':list(k),'coefficient':v} for k,v in sorted(pol.items())]})
 return {'variables':raw['variables'],'equations':eqs}

def shifted_rows(parent):
 rows=[]
 for eq in parent['equations']:
  p=defaultdict(int)
  for term in eq['terms']:
   ps=[((),term['coefficient'])]
   for i,e in enumerate(term['powers']):
    ps=[(a+(j,),v*(math.comb(e,j) if i<31 else 1)) for a,v in ps for j in (range(e+1) if i<31 else [e])]
   for a,v in ps:p[a]+=v
  groups=defaultdict(dict)
  for a,v in p.items():
   if v:groups[a[:31]][a[31:]]=v
  rows.append(groups)
 return rows

def main():
 parent=load_common_parent();rows=shifted_rows(parent)
 certpath=ROOT.parent/'quartic/B2_CERTIFICATE.json'
 cert=json.loads(certpath.read_text());weights=cert['weights'];W=max(weights);gap=2*W+1
 # The fifth row has constant coefficient 1, so it is placed last.
 order=[i for i in range(22) if i!=4]+[4];H=[(j+1)*gap for j in range(22)];Hmax=max(H);K=Hmax+2*W
 assert rows[4][(0,)*31]=={(0,0,0,0):1}
 old=json.loads((ROOT/'upstream/signed10/generated/signed10.json').read_text());d=DAG();v={n:d.leaf('variable',n) for n in old['variables']};c=d.lit
 b=d.name('b',d.add(c(1),d.mul(c(3),v['f'])));B=d.name('base',d.mul(d.leaf('fixed','beta_sun'),d.pow(b,2)))
 recipes={};records=[];Dterms=[];rowterms=defaultdict(list)
 for position,ri in enumerate(order):
  for alpha,co in sorted(rows[ri].items()):
   factor=math.factorial(2-sum(alpha))
   for e in alpha:factor*=math.factorial(e)
   pp=[{'powers':list(a),'coefficient':val*factor} for a,val in sorted(co.items())]
   key=json.dumps(pp,sort_keys=True,separators=(',',':'))
   if len(pp)==1 and pp[0]['powers']==[0]*4:node=c(pp[0]['coefficient']);name=None
   else:name=recipes.setdefault(key,'q'+str(len(recipes)).zfill(4));node=d.leaf('fixed',name)
   expo=H[position]-sum(a*w for a,w in zip(alpha,weights));assert expo>=0
   records.append({'row':ri+1,'target':H[position],'alpha':list(alpha),'name':name,'coefficient_polynomial_in_fixed_ports':pp,'exponent':expo})
   Dterms.append((expo,node));rowterms[position].append((alpha,node))
 # Shared homogeneous degree-two row evaluation, then Horner across blocks.
 uv=[d.pow(B,W)]+[d.pow(B,W-x) for x in weights]
 vv=[]
 for position in range(22):
  terms=[]
  for alpha,node in rowterms[position]:
   aa=[2-sum(alpha)]+list(alpha)
   term=node
   for x,e in zip(uv,aa):
    if e:term=d.mul(term,d.pow(x,e))
   terms.append(term)
  vv.append(d.add(*terms))
 stride=d.pow(B,gap);D=vv[-1]
 for rowval in reversed(vv[:-1]):D=d.add(d.mul(stride,D),rowval)
 D=d.name('Dcode',d.mul(B,D))
 ell=d.name('ell',d.add(*(d.pow(B,x) for x in weights)))
 N0=d.name('N0',d.pow(B,W+1));N1=d.name('N1',d.mul(c(4),d.pow(B,K+1)));N=d.name('N',d.mul(N0,N1))
 mask=d.name('Mcode',d.sub(d.sub(N0,c(1)),d.mul(d.sub(b,c(1)),ell)))
 targets=d.name('targets',d.add(*(d.pow(B,h) for h in H)))
 T=d.name('Tcode',d.add(mask,d.mul(d.sub(B,c(2)),targets,N0)))
 J=d.name('Jcode',d.add(d.mul(c(2),d.pow(d.add(c(1),v['g']),2),D),d.mul(B,geom(d,B,K+1)[1])))
 S=d.name('Scode',d.add(v['g'],d.mul(J,N0)));R=d.name('Rcode',d.add(d.mul(d.add(S,T,c(1)),N),T,c(1)))
 X=d.name('X',d.mul(d.sub(N,c(1)),R));Y=d.name('Y',d.pow(N,2));cap=d.name('Ccap',d.mul(b,d.pow(B,W)))
 mapped={old['named_nodes'][n]:d.names[n] for n in ['b','X','Y','Ccap']}
 def graft(i):
  if i in mapped:return mapped[i]
  n=old['nodes'][i];k=n['kind']
  if k in ('literal','variable','fixed'):r=d.leaf(k,n['value'] if k=='literal' else n['name'])
  else:r=d.op(k,graft(n['left']),graft(n['right']))
  mapped[i]=r;return r
 out=graft(old['output'])
 for n,i in old['named_nodes'].items():
  if i in mapped:d.names[n]=mapped[i]
 nodes,out,names=d.export(out);deg=[]
 for n in nodes:
  k=n['kind'];deg.append(1 if k=='variable' else 0 if k in ('literal','fixed') else deg[n['left']]+deg[n['right']] if k=='mul' else max(deg[n['left']],deg[n['right']]))
 counts=dict(Counter(n['kind'] for n in nodes if 'left'in n))
 result={'schema':'proveit-multitarget-sun10-v1','variables':old['variables'],'domain':'unrestricted integers','nodes':nodes,'output':out,'named_nodes':names,'weights':weights,'W':W,'targets':H,'row_order':[i+1 for i in order],'Kcode':K,'degree_upper_bound':deg[out],'operation_counts':counts,'total_operations':sum(counts.values()),'beta_sun_exponent':BETA_EXP,'binding':'MULTITARGET_INSTANCE.json','coefficient_recipes':'generated/quadratic_coefficients.json','proof':'MULTITARGET_SOURCE_PROOF.md','tail_proof':'upstream/SIGNED10_PROOF.md','named_degrees':{k:deg[i] for k,i in names.items()}}
 (ROOT/'generated/multitarget_sun10.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
 (ROOT/'generated/quadratic_coefficients.json').write_text(json.dumps({'records':records,'fixed_port_order':['beta','K0','MC','MF'],'source':'data/parent_system60.json'},indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['W','targets','Kcode','degree_upper_bound','operation_counts','total_operations']}))
if __name__=='__main__':main()
