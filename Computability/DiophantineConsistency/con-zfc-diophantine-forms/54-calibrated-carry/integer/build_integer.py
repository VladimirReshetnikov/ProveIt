#!/usr/bin/env python3
"""Independent ten-integer constructor. Vendored upstream code is not executed.
Consumes separately verified positional certificates and coherent four-port data.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import ast, json, hashlib, gzip, math, argparse, os
ROOT=Path(__file__).resolve().parent
VARS=['f','g','h','k','l','w','x','y','z','m']

class DAG:
 def __init__(self): self.nodes=[];self.unique={};self.names={};self.val={};self.powers={}
 def node(self,k,*args):
  key=(k,*args)
  if key in self.unique:return self.unique[key]
  n={'kind':k}
  if k=='literal':n['value']=args[0]
  elif k in ('variable','fixed'):n['name']=args[0]
  else:n.update(left=args[0],right=args[1])
  i=len(self.nodes);self.nodes.append(n);self.unique[key]=i
  if k=='literal':self.val[i]=args[0]
  return i
 def c(self,x):return self.node('literal',x)
 def op(self,k,a,b):
  if a in self.val and b in self.val:
   aa,bb=self.val[a],self.val[b];return self.c(aa+bb if k=='add' else aa-bb if k=='sub' else aa*bb)
  if k=='add':
   if self.val.get(a)==0:return b
   if self.val.get(b)==0:return a
  if k=='sub':
   if self.val.get(b)==0:return a
   if a==b:return self.c(0)
  if k=='mul':
   if self.val.get(a)==0 or self.val.get(b)==0:return self.c(0)
   if self.val.get(a)==1:return b
   if self.val.get(b)==1:return a
  if k in ('add','mul') and a>b:a,b=b,a
  return self.node(k,a,b)
 def add(self,*args):
  r=self.c(0)
  for a in args:r=self.op('add',r,a)
  return r
 def mul(self,*args):
  r=self.c(1)
  for a in args:r=self.op('mul',r,a)
  return r
 def sub(self,a,b):return self.op('sub',a,b)
 def pow(self,a,n):
  assert n>=0
  if n==0:return self.c(1)
  if n==1:return a
  key=a,n
  if key not in self.powers:
   q=self.pow(a,n//2);r=self.mul(q,q)
   if n%2:r=self.mul(r,a)
   self.powers[key]=r
  return self.powers[key]
 def save(self,name,i):self.names[name]=i;return i
 def export(self,out):
  use=set()
  def mark(i):
   if i in use:return
   use.add(i);n=self.nodes[i]
   if 'left'in n:mark(n['left']);mark(n['right'])
  mark(out);order=sorted(use);mp={i:j for j,i in enumerate(order)}
  nodes=[]
  for i in order:
   n=self.nodes[i].copy()
   if 'left'in n:n['left']=mp[n['left']];n['right']=mp[n['right']]
   nodes.append(n)
  return nodes,mp[out],{k:mp[v] for k,v in self.names.items() if v in mp}

def expression(s,ports):
 def go(n):
  if isinstance(n,ast.Expression):return go(n.body)
  if isinstance(n,ast.Constant) and isinstance(n.value,int):return n.value
  if isinstance(n,ast.Name):return ports[n.id]
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -go(n.operand)
  if isinstance(n,ast.BinOp):
   a,b=go(n.left),go(n.right)
   if isinstance(n.op,ast.Add):return a+b
   if isinstance(n.op,ast.Sub):return a-b
   if isinstance(n.op,ast.Mult):return a*b
   if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant) and 0<=b<=4:return a**b
  raise ValueError('Unsupported fixed coefficient expression')
 return go(ast.parse(s,mode='eval'))

def geom(d,B,n):
 if n==0:return d.c(1),d.c(0)
 if n==1:return B,d.c(1)
 p,s=geom(d,B,n//2);p2=d.mul(p,p);s2=d.mul(s,d.add(d.c(1),p))
 return (d.mul(p2,B),d.add(s2,p2)) if n%2 else (p2,s2)

def sparse_horner(d,B,terms):
 by={}
 for exponent,node in terms:by[exponent]=d.add(by.get(exponent,d.c(0)),node)
 terms=sorted(by.items(),reverse=True);last,res=terms[0]
 for e,node in terms[1:]:res=d.add(d.mul(res,d.pow(B,last-e)),node);last=e
 return d.mul(res,d.pow(B,last))

def tail(d,v,b,X,Y,cap,optimize=True,separator='equal'):
 c,A,M,S,P,N=d.c,d.add,d.mul,d.sub,d.pow,d.save
 L=N('L',M(v['l'],Y));halfU=M(L,X);U=N('U',M(c(2),halfU));V=N('V',M(c(4),v['g'],v['w'],Y));W=N('W',M(b,v['w']))
 halfA=N('halfA',M(halfU,A(V,c(1))));AA=N('A',M(c(2),halfA))
 BB=N('B1',A(M(c(2),X),c(1)));Am2=S(AA,c(2));Cshift=M(Am2,v['h']);C=N('C',A(BB,Cshift))
 Pn=N('Pn',M(P(U,2),V));K=N('K',A(X,c(1),M(v['k'],S(Pn,c(2)))));K2=P(K,2);Pn2=P(Pn,2)
 ss=N('S',S(M(c(2),AA),c(5)));tt=N('T',A(c(2),M(W,S(M(c(3),C),M(c(2),W)))))
 r1=N('r1',A(M(S(Pn2,c(4)),K2),c(4)));cap3=P(cap,3);g2=P(v['g'],2);diff=N('CKL',S(C,M(K,L)))
 delta=N('Delta',S(M(c(8),cap3,v['g'],K2),M(g2,A(M(c(32),P(diff,2),cap3),M(g2,K2)))))
 O=N('O',M(P(M(v['f'],v['l']),2),delta));xi=N('xi',M(v['z'],v['x']));C2=P(C,2);A2m4=S(P(AA,2),c(4))
 D=N('D',A(M(A2m4,C2),c(4)));E=N('E',M(C2,D,xi));E2=P(E,2);Fm1=N('Fm1',M(c(4),A2m4,E2));F=N('F',A(Fm1,c(1)))
 if optimize:Gplus=N('Gplus1',M(S(halfA,c(1)),Fm1));G=N('G',S(Gplus,c(1)))
 else:G=N('G',S(M(c(2),A(AA,c(2)),P(Am2,2),E2),c(1)))
 Omega=N('Omega',M(c(16),E))
 if optimize:H=N('H',A(C,M(F,S(M(Omega,v['y']),Cshift))))
 else:H=N('H',A(C,M(S(BB,C),F),M(Omega,F,v['y'])))
 I=N('I',A(M(M(Gplus,S(Gplus,c(2))) if optimize else S(P(G,2),c(1)),P(H,2)),c(1)))
 Sigma=N('Sigma',M(xi,P(ss,5)));r=N('t',A(tt,M(ss,v['y'])));ss2=P(ss,2);r2=P(r,2)
 # Factored cubic uses one fewer multiplication than the literal cubic.
 cubic=S(M(r,S(r2,ss2)),M(ss2,ss)) if optimize else S(S(P(r,3),M(r,ss2)),M(ss2,ss))
 theta=N('Theta',M(cubic,A(r2,M(c(23),ss2))))
 r0=N('r0',M(b,A(c(1),M(S(M(c(3),O),c(4)),P(M(b,v['z']),2)))))
 r2=N('r2',M(D,F,I))
 center=N('center',S(M(Sigma,v['m']),theta));sigma2=P(Sigma,2)
 a0=N('a0',M(sigma2,r0))
 if separator=='magnitude':
  common=M(sigma2,P(r0,2));a1=N('a1',M(common,r1));a2=N('a2',M(common,P(A(Pn2,K2,c(3)),2),r2))
 elif separator in ('pell','equal'):
  common=M(sigma2,P(b,2));a1=N('a1',M(common,r1));a2=N('a2',M(common,K2,r2) if separator=='pell' else M(common,r2))
 else:raise ValueError(separator)
 x2=P(center,2);vn=N('Vnorm',S(S(A(x2,a2),a0),a1));vn2=P(vn,2);xa=M(x2,a2);wn=N('Wnorm',A(vn2,M(c(4),S(xa,M(a0,a1)))))
 return N('F10',S(P(wn,2),M(c(16),vn2,xa)))

def build(certpath,source_mode='global',optimize=True,separator='equal',bridge='sparse_popcount'):
 cert=json.loads(certpath.read_text());ports={p:int.from_bytes(gzip.decompress((ROOT.parent/'native'/f'{f}.bin.gz').read_bytes()),'little') for p,f in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]}
 vals=[abs(expression(t['weighted_coefficient'],ports)) for row in cert['rows'] for t in row['terms']]
 C=1+sum(vals);multiplier=8192 if bridge=='sparse_popcount' else 2048;e=(multiplier*C).bit_length();e+=e%2
 fixed={'beta_source':1<<e};recipes={'beta_source':{'power_of_two':e}};aliases={}
 d=DAG();c,A,M,S,P,N=d.c,d.add,d.mul,d.sub,d.pow,d.save;v={n:d.node('variable',n) for n in VARS}
 b=N('b',A(c(1),M(c(3),v['f'])));B=N('base',M(d.node('fixed','beta_source'),P(b,2)));W=cert['maximum_weight'];H=cert['target_exponents'];Kcode=cert['Kcode']
 allterms=[];rowpolys=[]
 for row in cert['rows']:
  terms=[]
  for t in row['terms']:
   s=t['weighted_coefficient']
   try:node=c(int(s))
   except ValueError:
    if s not in aliases:
     name='q'+hashlib.sha256(s.encode()).hexdigest()[:12];aliases[s]=name;recipes[name]={'expression':s};fixed[name]=expression(s,ports)
    node=d.node('fixed',aliases[s])
   terms.append((t['encoding_exponent'],node))
  allterms+=terms
  if source_mode=='row':
   mn=min(e for e,n in terms);rowpolys.append((mn,sparse_horner(d,B,[(e-mn,n) for e,n in terms])))
 if source_mode in ('homogeneous','hybrid'):
  raw=json.loads((ROOT/'data/parent_system60.json').read_text());u0=P(B,W-cert.get('padding_exponent',0));coords=[P(B,W-w) for w in cert['weights']]
  shifted=set(cert.get('shifted_coordinates',raw['variables']));env={name:((A(x,u0) if name in shifted else x),1) for name,x in zip(raw['variables'],coords)}
  for name in raw['constants']:
   fixed[name]=ports[name];recipes[name]={'expression':name};env[name]=(d.node('fixed',name),0)
  def get(x):return (c(x),0) if isinstance(x,int) else env[x]
  def aligned(z,t):return M(z[0],P(u0,t-z[1]))
  for name,op,aa,bb in raw['source']:
   aa,bb=get(aa),get(bb)
   if op=='*':env[name]=(M(aa[0],bb[0]),aa[1]+bb[1])
   else:
    t=max(aa[1],bb[1]);env[name]=((A if op=='+' else S)(aligned(aa,t),aligned(bb,t)),t)
  rowvals={}
  for ri,(aa,bb) in enumerate(raw['comparisons'],1):
   aa,bb=get(aa),get(bb)
   if cert.get('coefficient_signs',[1]*len(raw['comparisons']))[ri-1]<0:aa,bb=bb,aa
   rowvals[ri]=S(aligned(aa,2),aligned(bb,2))
  blockterms=[]
  for row in cert['rows']:
   correction=[]
   for term in row['terms']:
    alpha=term['alpha'];isconstant=not any(alpha)
    if isconstant or 2 in alpha:
     ss=term['coefficient']
     try:co=c(int(ss))
     except ValueError:
      if ss not in aliases:
       name='q'+hashlib.sha256(ss.encode()).hexdigest()[:12];aliases[ss]=name;recipes[name]={'expression':ss};fixed[name]=expression(ss,ports)
      co=d.node('fixed',aliases[ss])
     coord=u0 if isconstant else coords[alpha.index(2)]
     correction.append(M(co,P(coord,2)))
   sign=cert.get('coefficient_signs',[1]*len(raw['comparisons']))[row['original_row_one_based']-1];rowval=A(rowvals[row['original_row_one_based']],*correction)
   offset=row['target_exponent']-2*W
   if offset<0:
    assert source_mode=='hybrid'
    terms=[]
    for term in row['terms']:
     ss=term['weighted_coefficient']
     try:node=c(int(ss))
     except ValueError:node=d.node('fixed',aliases[ss])
     terms.append((term['encoding_exponent'],node))
    mn=min(e for e,n in terms);blockterms.append((mn,sparse_horner(d,B,[(e-mn,n) for e,n in terms])))
   else:blockterms.append((offset,rowval))
  Dcode=N('Dcode',sparse_horner(d,B,blockterms))
 else:Dcode=N('Dcode',sparse_horner(d,B,allterms) if source_mode=='global' else sparse_horner(d,B,rowpolys))
 top=N('top',P(B,W));ell=N('ell',A(*(P(B,w) for w in cert['weights'])));N0=N('N0',M(top,B))
 spacing=cert.get('target_spacing',0);sorted_h=sorted(H)
 if not spacing and len(set(b-a for a,b in zip(sorted_h,sorted_h[1:])))==1:spacing=sorted_h[1]-sorted_h[0]
 if spacing:
  gap=spacing;hmin=min(H);_,gg=geom(d,P(B,gap),len(H));targetsum=M(P(B,hmin),gg)
 else:targetsum=sparse_horner(d,B,[(h,c(1)) for h in H])
 targetsum=N('targetsum',targetsum);mask=N('mask',S(S(N0,c(1)),M(S(b,c(1)),ell)));T=N('Tcode',A(mask,M(S(B,c(2)),targetsum,N0)))
 if bridge=='dense':
  endpower,geosum=geom(d,B,Kcode+1);N1=N('N1',M(c(4),endpower));NN=N('N',M(N0,N1))
  J=N('Jcode',A(M(c(2),P(A(P(B,cert.get('padding_exponent',0)),v['g']),2),Dcode),M(B,geosum)))
  Sc=N('Scode',A(v['g'],M(J,N0)));R=N('Rcode',A(M(A(Sc,T,c(1)),NN),T,c(1)));X=N('X',M(S(NN,c(1)),R));Y=N('Y',P(NN,2))
 elif bridge=='sparse_popcount':
  assert Kcode>=max(H)+2
  N1=N('N1',P(B,Kcode+1));NN=N('N',M(N0,N1));J=N('Jcode',A(M(c(2),P(A(P(B,cert.get('padding_exponent',0)),v['g']),2),Dcode),targetsum))
  Sc=N('Scode',A(v['g'],M(J,N0)));X=N('X',S(M(NN,A(NN,Sc,T,c(1))),A(Sc,c(1))))
  n=len(cert['weights']);assert n%2==1;half=(n+1)//2;hp=2*W+Kcode+3+len(H);exp=e*half+1-len(H);assert exp>=0 and hp>=half
  fixed['Y_scale']=1<<exp;recipes['Y_scale']={'power_of_two':exp};Y=N('Y',M(d.node('fixed','Y_scale'),P(B,hp-half),b))
 else:raise ValueError(bridge)
 cap=N('Ccap',M(b,top));out=tail(d,v,b,X,Y,cap,optimize,separator)
 nodes,out,names=d.export(out);degrees=[]
 for n in nodes:
  k=n['kind'];degrees.append(1 if k=='variable' else 0 if k in ('literal','fixed') else degrees[n['left']]+degrees[n['right']] if k=='mul' else max(degrees[n['left']],degrees[n['right']]))
 counts=dict(Counter(n['kind'] for n in nodes if 'left'in n))
 body={'schema':'proveit-round8-conditional-sun10-v1','domain':'unrestricted integers','variables':VARS,'nodes':nodes,'output':out,'named_nodes':names,'degree_upper_bound':degrees[out],'named_degree_upper_bounds':{k:degrees[i] for k,i in names.items()},'operation_counts':counts,'total_operations':sum(counts.values()),'positional_certificate':os.path.relpath(certpath,ROOT),'certificate_sha256':hashlib.sha256(certpath.read_bytes()).hexdigest(),'native_binding':'../native/COEFFICIENT_BINDING.json','fixed_binding':'FIXED_BINDING.json','source_mode':source_mode,'bridge':bridge,'separator':separator,'source_variant':cert.get('source_variant','all_shifted'),'tail_exact_factorization':optimize,'beta_source_exponent':e}
 return body,fixed,recipes,{'C_bit_length':C.bit_length(),'maximum_weighted_coefficient_bits':max(vals).bit_length(),'beta_source_exponent':e,'source_bound_multiplier':multiplier,'strict_bound':(1<<e)>multiplier*C}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('certificates',nargs='*');parser.add_argument('--separators',default='equal');parser.add_argument('--modes',default='global,homogeneous,hybrid');parser.add_argument('--bridge',default='sparse_popcount');args=parser.parse_args()
 paths=[Path(p).resolve() for p in args.certificates] or sorted((ROOT.parent/'packing').glob('CERTIFICATE_*selective12*.json'))
 assert paths,'No certificates specified or found'
 out=ROOT/'generated';out.mkdir(exist_ok=True)
 results=[];bindings={};bounds={};allfixed={}
 for cp in paths:
  cert=json.loads(cp.read_text())
  for mode in args.modes.split(','):
   if mode=='homogeneous' and min(cert['target_exponents'])<2*cert['maximum_weight']:continue
   for separator in args.separators.split(','):
    body,fixed,recipes,bound=build(cp,mode,separator=separator,bridge=args.bridge)
    fname=f"sun10_{cp.stem.removeprefix('CERTIFICATE_')}_{mode}_{args.bridge}_{separator}.json";(out/fname).write_text(json.dumps(body,separators=(',',':'))+'\n')
    results.append({'file':'generated/'+fname,'degree_upper_bound':body['degree_upper_bound'],'operations':body['total_operations'],'counts':body['operation_counts'],'separator':separator,'source_mode':mode})
    for name,value in fixed.items():assert name not in allfixed or allfixed[name]==value,'Incompatible fixed leaves'
    bindings.update(recipes);allfixed.update(fixed);bounds[fname]=bound
 fdir=ROOT/'fixed';fdir.mkdir(exist_ok=True)
 for name,val in allfixed.items():
  mag=abs(val).to_bytes((abs(val).bit_length()+7)//8 or 1,'little');gz=gzip.compress(mag,mtime=0);(fdir/f'{name}.bin.gz').write_bytes(gz)
  bindings[name].update({'sign':1 if val>=0 else -1,'magnitude_bytes':len(mag),'sha256':hashlib.sha256(mag).hexdigest(),'gzip_sha256':hashlib.sha256(gz).hexdigest(),'file':f'fixed/{name}.bin.gz'})
 (ROOT/'FIXED_BINDING.json').write_text(json.dumps({'schema':'fixed-integer-leaves-v1','native_binding':'../native/COEFFICIENT_BINDING.json','encoding':'Sign in manifest; unsigned little-endian absolute value in gzip payload.','leaves':bindings},indent=2)+'\n')
 (ROOT/'SOURCE_BOUNDS.json').write_text(json.dumps(bounds,indent=2)+'\n');(ROOT/'METRICS.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
if __name__=='__main__':main()
