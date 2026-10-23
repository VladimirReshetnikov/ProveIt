#!/usr/bin/env python3
"""Independent authored round-7 nine-variable polynomial compiler.
Reads mathematical JSON; never imports or executes supplied upstream scripts.
"""
import json, hashlib, argparse
from pathlib import Path
from collections import Counter, defaultdict
import sympy as sp
ROOT=Path(__file__).resolve().parent

class Circuit:
 def __init__(self): self.nodes=[]; self.intern={}; self.pows={}; self.names={}
 def atom(self,k,v): return self.node(k,v)
 def node(self,k,*a):
  if k in ('add','mul'): a=tuple(sorted(a))
  key=(k,)+a
  if key not in self.intern:
   self.intern[key]=len(self.nodes)
   self.nodes.append({'kind':k,**({'left':a[0],'right':a[1]} if k in ('add','mul','sub') else {'value' if k=='literal' else 'name':a[0]})})
  return self.intern[key]
 def c(self,x): return self.atom('literal',x)
 def op(self,k,a,b):
  x=self.nodes[a].get('value');y=self.nodes[b].get('value')
  if x is not None and y is not None: return self.c(x+y if k=='add' else x-y if k=='sub' else x*y)
  if k=='add' and x==0:return b
  if k in ('add','sub') and y==0:return a
  if k=='mul':
   if x==0 or y==0:return self.c(0)
   if x==1:return b
   if y==1:return a
  return self.node(k,a,b)
 def add(self,*xs):
  a=self.c(0)
  for b in xs:a=self.op('add',a,b)
  return a
 def mul(self,*xs):
  a=self.c(1)
  for b in xs:a=self.op('mul',a,b)
  return a
 def sub(self,a,b):return self.op('sub',a,b)
 def pow(self,a,e):
  assert e>=0
  if e==0:return self.c(1)
  if e==1:return a
  if (a,e) not in self.pows:
   h=self.pow(a,e//2);r=self.mul(h,h)
   self.pows[a,e]=self.mul(r,a) if e%2 else r
  return self.pows[a,e]
 def geom(self,a,e):
  if e==0:return self.c(0)
  if e==1:return self.c(1)
  half=e//2;r=self.mul(self.geom(a,half),self.add(self.c(1),self.pow(a,half)))
  return self.add(r,self.pow(a,e-1)) if e%2 else r
 def sparse(self,b,pairs):
  merged=defaultdict(list)
  for e,a in pairs:merged[e].append(a)
  terms=sorted((e,self.add(*a)) for e,a in merged.items());e,r=terms.pop()
  while terms:
   e2,a=terms.pop();r=self.add(self.mul(r,self.pow(b,e-e2)),a);e=e2
  return self.mul(r,self.pow(b,e))
 def save(self,name,a):self.names[name]=a;return a
 def export(self,out):
  live=set();todo=[out]
  while todo:
   i=todo.pop()
   if i in live:continue
   live.add(i);n=self.nodes[i]
   if 'left' in n:todo.extend([n['left'],n['right']])
  ren={i:j for j,i in enumerate(sorted(live))};nodes=[]
  for i in sorted(live):
   n=dict(self.nodes[i])
   if 'left' in n:n.update(left=ren[n['left']],right=ren[n['right']])
   nodes.append(n)
  return nodes,ren[out],{k:ren[v] for k,v in self.names.items() if v in ren}

def build(target_path,positive=True,certificate=False,encoding='horner'):
 data=json.loads(Path(target_path).read_text());binding=json.loads((ROOT.parent/'coefficients/COEFFICIENT_BINDING.json').read_text());bits=[x['bits'] for x in binding['ports']]
 d=Circuit();c=d.c;add=d.add;sub=d.sub;mul=d.mul;pw=d.pow;sv=d.save
 vs=['b','g','h','s','w','phi','i','j','n'];v={x:d.atom('variable',x) for x in vs}
 for x in (['phi','j','n'] if positive else ['b','g','h','s','w','i']):v[x]=sub(v[x],c(1)) if positive else add(v[x],c(1))
 weights=data['weights'];W=max(weights);hmax=data['target_maximum'];kcode=data.get('Kcode',hmax+2*W);dmax=data.get('Dmax',hmax);Lexp=kcode+W+2
 ports=sp.symbols('beta K0 MC MF');pmap=dict(zip(data['ports'],ports));recipes={};terms=[];row_terms=[];maxbound=0
 for row in data['rows']:
  rt=[]
  for term in row['terms']:
   p=sp.Poly(sp.sympify(term['weighted_coefficient'],locals=pmap),*ports)
   recipe=[{'powers':list(es),'coefficient':int(co)} for es,co in sorted(p.terms())];key=json.dumps(recipe,sort_keys=True)
   if key not in recipes:recipes[key]=(f'c{len(recipes):03}',recipe)
   name=recipes[key][0]
   node=c(recipe[0]['coefficient']) if len(recipe)==1 and recipe[0]['powers']==[0]*4 else d.atom('fixed',name)
   e=term['encoding_exponent'];terms.append((e,node));rt.append((term,node))
   bound=sum(abs(t['coefficient'])*(1<<sum(e*b for e,b in zip(t['powers'],bits))) for t in recipe);maxbound=max(maxbound,bound)
  row_terms.append((row,rt))
 mexp=maxbound.bit_length();lam=d.atom('fixed','radix_scale');b=sv('b',v['b']);B=sv('B',mul(lam,pw(b,2)))
 if encoding=='horner':DC=d.sparse(B,terms)
 elif encoding=='sum':DC=add(*(mul(a,pw(B,e)) for e,a in terms))
 elif encoding=='rows':
  rows=[]
  for row,rt in row_terms:
   lo=min(t['encoding_exponent'] for t,a in rt)
   rp=d.sparse(B,[(t['encoding_exponent']-lo,a) for t,a in rt]);rows.append(mul(rp,pw(B,lo)))
  DC=add(*rows)
 elif encoding=='shared':
  raw=json.loads((ROOT/'data/source_system60.json').read_text())
  assert hashlib.sha256((ROOT/'data/source_system60.json').read_bytes()).hexdigest()==data['source_sha256']
  def coefficient(expr):
   pp=sp.Poly(sp.sympify(expr,locals=pmap),*ports)
   rec=[{'powers':list(es),'coefficient':int(co)} for es,co in sorted(pp.terms())];key=json.dumps(rec,sort_keys=True)
   if key not in recipes:recipes[key]=(f'c{len(recipes):03}',rec)
   name=recipes[key][0]
   return c(rec[0]['coefficient']) if len(rec)==1 and rec[0]['powers']==[0]*4 else d.atom('fixed',name)
  u0=pw(B,W-data.get('padding_exponent',0));coords=[pw(B,W-w) for w in weights]
  env={name:(add(z,u0),1) for name,z in zip(raw['variables'],coords)}
  env.update({name:(coefficient(name),0) for name in raw['constants']})
  def get(x):return (c(x),0) if isinstance(x,int) else env[x]
  def align(z,t):return mul(z[0],pw(u0,t-z[1]))
  for name,op,aa,bb in raw['source']:
   aa,bb=get(aa),get(bb)
   if op=='*':env[name]=(mul(aa[0],bb[0]),aa[1]+bb[1])
   else:
    t=max(aa[1],bb[1]);env[name]=((add if op=='+' else sub)(align(aa,t),align(bb,t)),t)
  rowvals={ri:sub(align(get(aa),2),align(get(bb),2)) for ri,(aa,bb) in enumerate(raw['comparisons'],1)}
  blocks=[]
  for row,rt in row_terms:
   correction=[]
   for term,node in rt:
    alpha=term['alpha']
    if not any(alpha) or 2 in alpha:
     coord=u0 if not any(alpha) else coords[alpha.index(2)]
     correction.append(mul(coefficient(term['coefficient']),pw(coord,2)))
   rp=add(rowvals[row['original_row_one_based']],*correction);off=row['target_exponent']-2*W
   assert off>=0
   blocks.append((off,rp))
  DC=d.sparse(B,blocks)
 elif encoding=='homogeneous':
  assert data.get('target_spacing')
  hom=[pw(B,W-data.get('padding_exponent',0))]+[pw(B,W-w) for w in weights];rps=[]
  for row,rt in row_terms:
   rp=add(*(mul(a,*(pw(hom[i],e) for i,e in enumerate([2-sum(t['alpha'])]+t['alpha']) if e)) for t,a in rt));rps.append((row['target_exponent']-2*W,rp))
  DC=d.sparse(B,rps)
 else:raise ValueError(encoding)
 DC=sv('Dcode',DC);ell=sv('ell',add(*(pw(B,w) for w in weights)))
 N0=sv('N0',pw(B,W+1));N1=sv('N1',mul(c(4),pw(B,kcode+1)));N=sv('N',mul(N0,N1))
 mask=sv('mask',sub(sub(N0,c(1)),mul(sub(b,c(1)),ell)))
 if data.get('target_spacing'):
  stride=pw(B,data['target_spacing']);targets=mul(stride,d.geom(stride,len(row_terms)))
 else:targets=d.sparse(B,[(row['target_exponent'],c(1)) for row,rt in row_terms])
 targets=sv('targets',targets)
 Tc=sv('Tcode',add(mask,mul(sub(B,c(2)),targets,N0)))
 Jc=sv('Jcode',add(mul(c(2),pw(add(pw(B,data.get('padding_exponent',0)),v['g']),2),DC),mul(B,d.geom(B,kcode+1))))
 Sc=sv('Scode',add(v['g'],mul(Jc,N0)))
 R=sv('R',mul(sub(N,c(1)),add(mul(add(Sc,Tc,c(1)),N),Tc,c(1))))
 cap=sv('Gcap',mul(c(32),b,pw(B,W)))
 U=sv('U',mul(pw(N,2),v['w']));Y=sv('Y',mul(pw(N,2),v['s']));M=sv('M',mul(R,Y))
 P=sv('P',mul(c(2),pw(M,2),U));K=sv('K',add(R,c(1),mul(v['h'],sub(P,c(1)))))
 A=sv('A',mul(M,add(U,c(1))));B1=add(mul(c(2),R),c(1));W1=mul(b,v['w']);C=sv('C',add(B1,W1,v['phi']))
 J=sv('J',sub(mul(c(4),A),c(5)));Q=sv('Q',sub(mul(c(3),W1,C),mul(c(2),sub(pw(W1,2),c(1)))))
 am1=sub(pw(A,2),c(1));D=sv('D',add(mul(am1,pw(C,2)),c(1)))
 k=sv('k',mul(v['i'],J,C));L=sv('L',mul(k,D));E=sv('E',mul(L,C));F=sv('F',add(mul(am1,pw(E,2)),c(1)))
 G=sv('G',add(A,mul(F,sub(add(mul(C,D),c(1)),A))));H=sv('H',add(C,mul(F,add(B1,mul(v['j'],C)))))
 GH=sv('GH',mul(G,H));I=sv('I',add(sub(pw(GH,2),pw(H,2)),c(1)))
 V0=sv('V0',mul(P,K));a0=sv('a0',add(sub(pw(V0,2),pw(K,2)),c(1)));a1=sv('a1',mul(D,F,I))
 u=sv('u',J);vv=sv('v',Q)
 m=sv('m',sub(mul(sub(pw(K,2),mul(c(4),pw(sub(C,mul(K,Y)),2))),cap),mul(c(8),v['g'],pw(K,2))))
 Tpair=sv('Tpair',mul(k,sub(sub(mul(c(8),pw(D,2)),mul(c(4),D)),c(1))));V1=sv('V1',mul(Tpair,GH));Md=sv('Mdiv',Q);O=sv('Omega',mul(u,m))
 E0=sv('E0',add(mul(u,v['n']),vv))
 shift=add(V0,V1);theta=sv('Theta',sub(E0,mul(O,shift)))
 if certificate:
  delta=sv('Delta1',add(mul(sub(mul(add(mul(c(8),D),c(1)),pw(k,2)),mul(c(64),D)),pw(GH,2)),mul(c(64),D,F,sub(pw(H,2),c(1)))))
  delta0=sub(pw(K,2),c(1))
  inner=sv('inner',add(sub(pw(E0,2),mul(c(2),E0,O,shift)),mul(pw(O,2),add(delta0,delta,mul(c(2),V0,V1)))))
 else:inner=sv('inner',sub(pw(theta,2),mul(pw(O,2),add(a0,mul(c(64),a1)))))
 out=sub(pw(inner,2),mul(c(256),pw(O,4),a0,a1));nodes,out,names=d.export(out);counts=dict(Counter(n['kind'] for n in nodes if 'left' in n))
 return {'schema':'round7-margin-separated-nine-v1','crt_reparameterized':True,'radicand_scale':64,'majorant_order':2,'quotient_offset':False,'offset_free':True,'padding_exponent':data.get('padding_exponent',0),'variables':vs,'domain':'positive integers' if positive else 'nonnegative integers','nodes':nodes,'output':out,'named_nodes':names,'operation_counts':counts,'total_operations':sum(counts.values()),'degree':964*2*Lexp+8*W+236,'source_degree_N':2*Lexp,'source_exponent_N':Lexp,'degree_formula':'964t+8W+236, t=2(Kcode+W+2)','diagonal_leading_coefficient':{'power_of_two':1730,'radix_scale_power':964*Lexp+4*W},'W':W,'target_maximum':hmax,'Dmax':dmax,'Kcode':kcode,'weights':weights,'target_file':str(Path(target_path).resolve().relative_to(ROOT.parent)),'target_sha256':hashlib.sha256(Path(target_path).read_bytes()).hexdigest(),'coefficient_recipes':[{'name':n,'terms':r} for n,r in recipes.values()],'port_bit_lengths':bits,'coefficient_bound_exponent':mexp,'radix_scale_exponent':mexp+12,'radix_power':2,'encoding':encoding,'degree_certificate_form':certificate,'coefficient_binding':'../coefficients/COEFFICIENT_BINDING.json'}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('targets',nargs='+');args=parser.parse_args();(ROOT/'generated').mkdir(exist_ok=True)
 for file in args.targets:
  data=json.loads(Path(file).read_text());modes=['horner','sum','rows']+(['homogeneous'] if data.get('target_spacing') else [])+(['shared'] if min(r['target_exponent'] for r in data['rows'])>=2*max(data['weights']) else [])
  candidates=[build(file,True,False,mode) for mode in modes];best=min(candidates,key=lambda x:x['total_operations']);name=Path(file).stem.removeprefix('CERTIFICATE_')
  for positive in [True,False]:
   for cert in [False,True]:
    obj=best if positive and not cert else build(file,positive,cert,'horner' if cert else best['encoding']);suffix=('positive' if positive else 'natural')+('_degree_certificate' if cert else '')
    (ROOT/'generated'/f'nine_{name}_{suffix}.json').write_text(json.dumps(obj,separators=(',',':'))+'\n')
  print(json.dumps({'name':name,'degree':best['degree'],'ops':best['total_operations'],'Mexp':best['coefficient_bound_exponent'],'encoding_costs':{x['encoding']:x['total_operations'] for x in candidates}}))
if __name__=='__main__':main()
