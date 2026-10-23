#!/usr/bin/env python3
"""Round8 sparse calibrated source + source-parametric ratio finalizer.
Only inert pinned source JSON and locally authored modules are used.
"""
from pathlib import Path
from collections import defaultdict,Counter
import ast,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'source'))
from verify_selective_source import expr,need
from ratio_tail import append_ratio_tail,exact_degree

class Circuit:
 def __init__(self):self.nodes=[];self.cache={};self.powers={};self.names={}
 def atom(self,kind,value):return self.node(kind,value)
 def node(self,kind,*args):
  if kind in ('add','mul'):args=tuple(sorted(args))
  key=(kind,)+args
  if key not in self.cache:
   self.cache[key]=len(self.nodes)
   self.nodes.append(dict(kind=kind,**(dict(left=args[0],right=args[1])if kind in('add','sub','mul')else{('value'if kind=='literal'else'name'):args[0]})))
  return self.cache[key]
 def c(self,n):return self.node('literal',n)
 def op(self,kind,a,b):
  x=self.nodes[a].get('value');y=self.nodes[b].get('value')
  if x is not None and y is not None:return self.c(x+y if kind=='add'else x-y if kind=='sub'else x*y)
  if kind=='add'and x==0:return b
  if kind in('add','sub')and y==0:return a
  if kind=='sub'and a==b:return self.c(0)
  if kind=='mul':
   if x==0 or y==0:return self.c(0)
   if x==1:return b
   if y==1:return a
  return self.node(kind,a,b)
 def add(self,*items):
  a=self.c(0)
  for b in items:a=self.op('add',a,b)
  return a
 def sub(self,a,b):return self.op('sub',a,b)
 def mul(self,*items):
  a=self.c(1)
  for b in items:a=self.op('mul',a,b)
  return a
 def pow(self,a,n):
  need(type(n)is int and n>=0,'Nonnegative fixed exponent')
  if n==0:return self.c(1)
  if n==1:return a
  if(a,n)not in self.powers:
   h=self.pow(a,n//2);h=self.mul(h,h);self.powers[a,n]=self.mul(h,a)if n%2 else h
  return self.powers[a,n]
 def geom(self,b,n):
  if n==0:return self.c(0)
  if n==1:return self.c(1)
  h=n//2;r=self.mul(self.geom(b,h),self.add(self.c(1),self.pow(b,h)))
  return self.add(r,self.pow(b,n-1))if n%2 else r
 def sparse(self,b,terms):
  grouped=defaultdict(list)
  for e,a in terms:grouped[e].append(a)
  work=sorted((e,self.add(*items))for e,items in grouped.items());e,r=work.pop()
  while work:
   en,a=work.pop();r=self.add(self.mul(r,self.pow(b,e-en)),a);e=en
  return self.mul(r,self.pow(b,e))
 def save(self,name,node):self.names[name]=node;return node
 def export(self,out):
  live=set();todo=[out]
  while todo:
   ix=todo.pop()
   if ix in live:continue
   live.add(ix);node=self.nodes[ix]
   if'left'in node:todo.extend([node['left'],node['right']])
  mapping={old:new for new,old in enumerate(sorted(live))};nodes=[]
  for old in sorted(live):
   node=dict(self.nodes[old])
   if'left'in node:node.update(left=mapping[node['left']],right=mapping[node['right']])
   nodes.append(node)
  return nodes,mapping[out],{k:mapping[v]for k,v in self.names.items()if v in mapping}

def build(certpath,mode='horner',positive=True,majorant='quotient2048',certificate=False):
 certpath=Path(certpath);data=json.loads(certpath.read_text());srcpath=ROOT.parent/'source/data/source_system60.json';raw=json.loads(srcpath.read_text());selective=json.loads((ROOT.parent/'source/selective12_source.json').read_text());shift=set(selective['shifted_coordinates'])
 need(hashlib.sha256(srcpath.read_bytes()).hexdigest()==data['source_sha256'],'Source binding')
 d=Circuit();c=d.c;add=d.add;sub=d.sub;mul=d.mul;pw=d.pow;sv=d.save
 names=['b','g','h','s','w','phi','i','j','n'];v={name:d.atom('variable',name)for name in names}
 if positive:
  for x in['phi','j','n']:v[x]=sub(v[x],c(1))
 else:
  for x in['g','h','s','w','i']:v[x]=add(v[x],c(1))
 b=sv('b',v['b'] if positive else add(v['b'],c(1)))
 kap=864026;radix=d.atom('fixed','radix_scale');B=sv('B',mul(radix,pw(b,2)))
 W=data['maximum_weight'];p=data.get('padding_exponent',0);weights=data['weights'];K=data['Kcode'];E=K+W+2
 portnames=['beta','K0','MC','MF'];env={name:{tuple(int(i==j)for j in range(4)):1}for i,name in enumerate(portnames)};recipes={}
 def coef(text):
  poly=expr(text,env,4);key=tuple(sorted(poly.items()))
  if len(poly)==1 and (0,0,0,0)in poly:return c(poly[0,0,0,0])
  if not poly:return c(0)
  if key not in recipes:recipes[key]=(f'c{len(recipes):03}',[dict(powers=list(m),coefficient=n)for m,n in key])
  return d.atom('fixed',recipes[key][0])
 rows=[];terms=[]
 for row in data['rows']:
  items=[]
  for term in row['terms']:
   node=coef(term['weighted_coefficient']);items.append((term,node));terms.append((term['encoding_exponent'],node))
  rows.append((row,items))
 if mode=='horner':DC=d.sparse(B,terms)
 elif mode=='sum':DC=add(*(mul(node,pw(B,e))for e,node in terms))
 elif mode=='rows':
  pieces=[]
  for row,items in rows:
   lo=min(t['encoding_exponent']for t,node in items)
   pieces.append(mul(pw(B,lo),d.sparse(B,[(t['encoding_exponent']-lo,node)for t,node in items])))
  DC=add(*pieces)
 elif mode=='shared':
  need(min(row['target_exponent']for row,items in rows)>=2*W,'Shared source nonnegative row shifts')
  u0=pw(B,W-p);coords=[pw(B,W-w)for w in weights]
  registers={name:((add(z,u0)if name in shift else z),1)for name,z in zip(raw['variables'],coords)}
  registers.update({name:(coef(name),0)for name in portnames})
  def get(x):return(c(x),0)if type(x)is int else registers[x]
  def lift(pair,degree):return mul(pair[0],pw(u0,degree-pair[1]))
  for name,op,a,bb in raw['source']:
   aa,bb=get(a),get(bb)
   if op=='*':registers[name]=(mul(aa[0],bb[0]),aa[1]+bb[1])
   else:
    degree=max(aa[1],bb[1]);registers[name]=((add if op=='+'else sub)(lift(aa,degree),lift(bb,degree)),degree)
  residual={ix:sub(lift(get(a),2),lift(get(bb),2))for ix,(a,bb)in enumerate(raw['comparisons'],1)}
  pieces=[]
  for row,items in rows:
   correction=[]
   for term,node in items:
    alpha=term['alpha']
    if not any(alpha)or 2 in alpha:
     z=u0 if not any(alpha)else coords[alpha.index(2)]
     correction.append(mul(coef(term['coefficient']),pw(z,2)))
   rp=residual[row['original_row_one_based']]
   sign=data.get('coefficient_signs',[1]*len(data['rows']))[row['original_row_one_based']-1]
   if sign==-1:rp=sub(c(0),rp)
   pieces.append((row['target_exponent']-2*W,add(rp,*correction)))
  DC=d.sparse(B,pieces)
 else:raise ValueError(mode)
 DC=sv('Dcode',DC);ell=sv('ell',add(*(pw(B,w)for w in weights)))
 hh=sorted(row['target_exponent']for row,items in rows);stride=hh[1]-hh[0]
 if all(hh[ix]==hh[0]+ix*stride for ix in range(len(hh))):targets=mul(pw(B,hh[0]),d.geom(pw(B,stride),len(hh)))
 else:targets=d.sparse(B,[(h,c(1))for h in hh])
 targets=sv('targets',targets)
 N0=sv('N0',pw(B,W+1));mask=sv('mask',sub(sub(N0,c(1)),mul(sub(b,c(1)),ell)))
 Jcode=sv('Jcode',add(mul(c(2),pw(add(pw(B,p),v['g']),2),DC),targets))
 S=sv('Scode',add(v['g'],mul(N0,Jcode)));T=sv('Tcode',add(mask,mul(N0,sub(B,c(2)),targets)))
 L=sv('block_L',mul(c(2),b,pw(B,E)))
 R=sv('R',sub(mul(L,add(L,S,T,c(1))),add(S,c(1))))
 if K%2==0:q=(K+2*W+10)//2;cexp=15*kap//2-10;N=mul(d.atom('fixed','threshold_scale'),pw(B,q));degreeN=2*q
 else:q=(K+2*W+9)//2;cexp=8*kap-10;N=mul(d.atom('fixed','threshold_scale'),b,pw(B,q));degreeN=2*q+1
 N=sv('N',N);cap=sv('Gcap',mul(c(32),b,pw(B,W)))
 out=append_ratio_tail(d,R=R,N=N,b=b,g=v['g'],cap=cap,v=v,majorant=majorant,certificate=certificate)
 nodes,out,named=d.export(out);counts=dict(Counter(x['kind']for x in nodes if'left'in x));degreeR=4*E+2;degreecap=2*W+1
 return dict(schema='round8-sparse-calibrated-nine-v1',variables=names,domain='positive integers'if positive else'nonnegative integers',nodes=nodes,output=out,named_nodes=named,operation_counts=counts,total_operations=sum(counts.values()),degree=exact_degree(majorant,degreeR,degreeN,degreecap),source_degrees=dict(R=degreeR,N=degreeN,Gcap=degreecap),source_parameters=dict(W=W,padding=p,Dmax=data['Dmax'],Hmax=data['target_maximum'],Kcode=K,E=E,q=q,kappa=kap,threshold_scale_exponent=cexp),majorant=majorant,certificate_form=certificate,encoding=mode,source_coefficient_records=109,active_source_monomials=62,coefficient_recipes=[dict(name=name,terms=recipe)for name,recipe in recipes.values()],fixed_power_leaves=dict(radix_scale=kap,threshold_scale=cexp),native_coefficient_binding='../native/COEFFICIENT_BINDING.json',positional_certificate=str(certpath.resolve().relative_to(ROOT.parent)),positional_certificate_sha256=hashlib.sha256(certpath.read_bytes()).hexdigest(),source_sha256=hashlib.sha256(srcpath.read_bytes()).hexdigest(),positive_to_internal='b,g,h,s,w,i unchanged; phi,j,n subtract1',natural_to_internal='b,g,h,s,w,i add1; phi,j,n unchanged',proof='../source/SPARSE_POPCOUNT_SOURCE_PROOF.md')

def main():
 gen=ROOT/'generated';gen.mkdir(exist_ok=True);all_metrics=[]
 paths=sorted((ROOT.parent/'packing').glob('CERTIFICATE*.json'))
 for path in paths:
  data=json.loads(path.read_text());modes=['horner','rows','sum']
  if min(r['target_exponent']for r in data['rows'])>=2*data['maximum_weight']:modes.append('shared')
  for maj in ['simple64','support2048','quotient2048']:
   primary=path.name in ['CERTIFICATE_174_selective12_packed.json','CERTIFICATE_170_selective12_packed_shifted.json']
   extra=('regular' in path.name and maj=='simple64') or(path.name=='CERTIFICATE_170_selective12_packed.json'and maj=='quotient2048')
   if not(primary or extra):continue
   options=[build(path,mode,True,maj)for mode in modes];best=min(options,key=lambda o:o['total_operations'])
   tag=path.stem.removeprefix('CERTIFICATE_')+'_'+maj
   for positive in [True,False]:
    obj=best if positive else build(path,best['encoding'],False,maj)
    file=f'nine_{tag}_{"positive"if positive else"natural"}.json';(gen/file).write_text(json.dumps(obj,separators=(',',':'))+'\n')
    all_metrics.append(dict(file=file,degree=obj['degree'],operations=obj['total_operations'],encoding=obj['encoding'],majorant=maj,source=path.name,domain=obj['domain']))
   if maj in['simple64','quotient2048']:
    obj=build(path,best['encoding'],True,maj,True);(gen/f'nine_{tag}_positive_certificate.json').write_text(json.dumps(obj,separators=(',',':'))+'\n')
   print(path.name,maj,best['degree'],best['total_operations'],best['encoding'],{o['encoding']:o['total_operations']for o in options},flush=True)
 (ROOT/'METRICS.json').write_text(json.dumps(all_metrics,indent=2)+'\n')
if __name__=='__main__':main()
