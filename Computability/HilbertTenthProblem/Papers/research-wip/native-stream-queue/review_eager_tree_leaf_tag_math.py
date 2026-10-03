"""Independent mathematical/source-cut audit of finite Tree leaf-tag elimination."""
import argparse,hashlib,json,random,itertools
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'eager_tree_terminal_projection.py':'edee37e68cde72e65ecc6e903ab6d2aa359f01182fb3d4a5e744a49ab92e46bd','eager_tree_terminal_projection.json':'25f02a91b38b23f798a10d8c1fc88e014fa277a392281ea93aaa146a5bcade95','eager_tree_terminal_projection.md':'ad8439465f5def857e917b2e4df3d42f36f2e8ad5e4f740b5ca74cbf036a3e0b'}
def need(x,msg):
 if not x:raise AssertionError(msg)
def exact(a,b):
 return type(a)is type(b)and(a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)if type(a)is dict else len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))if type(a)in(list,tuple)else a==b)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def run(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return e
def ancestor(rows,ports):
 defs={r[0]:r[2:]for r in rows};live=set();todo=list(ports)
 while todo:
  n=todo.pop()
  if type(n)is str and n not in live:live.add(n);todo.extend(defs.get(n,()))
 return live
def sumtag(v,i,n):return sum(v[f'r{i}_t{j}']for j in range(1,3 if i==n-1 else 5))
def restore(p,v):return dict(v,**{f'r{i}_t0':1-sumtag(v,i,p['N'])for i in range(p['N'])})
def affine(rows,port):
 defs={r[0]:r for r in rows};cache={}
 def visit(n):
  if type(n)is int:return {'':n}if n else{}
  if n in cache:return cache[n]
  if n not in defs:return {n:1}
  _,op,a,b=defs[n];a=visit(a);b=visit(b)
  if op=='*':
   if set(a)<={''}:c=a.get('',0);out={k:c*v for k,v in b.items()}
   elif set(b)<={''}:c=b.get('',0);out={k:c*v for k,v in a.items()}
   else:raise AssertionError('Expected actual affine source cut')
  else:
   out=dict(a)
   for k,v in b.items():out[k]=out.get(k,0)+(v if op=='+'else-v)
  cache[n]={k:v for k,v in out.items()if v};return cache[n]
 return visit(port)
def independent_source(old):
 n=old['N'];rows=old['source'];defs={r[0]:r for r in rows};hot=[old['residuals'][5*i]for i in range(n)];leaf=[old['residuals'][5*i+2]for i in range(n)];unchanged=[r for r in old['residuals']if r not in hot+leaf]
 # t0 may occur only in one-hot and leaf residual cones.
 deleted=[f'r{i}_t0'for i in range(n)];need(not(set(deleted)&ancestor(rows,unchanged)),'leaf-tag privacy across all other source residuals')
 keep_other=ancestor(rows,[r for r in old['residuals']if r not in hot]);cut=set()
 for r in hot:cut.update(ancestor(rows,[r])-keep_other)
 cut &= set(defs)
 need(len(cut)==5*(n-1)+3 and all(defs[r][1]in('+','-')for r in cut),'actual private old tag-sum gates')
 insert={};leaf_map={};guards=[];sums=[]
 for i in range(n):
  s12=f'review_s12_{i}';s=f'review_s_{i}';sm=f'review_sm1_{i}';g=f'review_guard_{i}';new=[[s12,'+',f'r{i}_t1',f'r{i}_t2']]
  if i<n-1:
   active=next(r[0]for r in rows if r[1:]==['+',f'r{i}_t3',f'r{i}_t4']);new.append([s,'+',s12,active])
  else:s=s12
  new.extend([[sm,'-',s,1],[g,'*',s,sm]]);insert[hot[i]]=new;guards.append(g);sums.append(s)
  lr=defs[leaf[i]];need(lr[1]=='*'and lr[2]==f'r{i}_t0','actual original leaf residual')
  tags={f'r{i}_t{j}':1 for j in range(3 if i==n-1 else 5)};tags['']=-1
  need(affine(rows,hot[i])==tags,'exact old onehot coefficient identity')
  need(affine(rows,lr[3])=={f'r{i}_z':1,f'r{i}_y':-2,'':-1},'exact old leaf difference coefficient identity')
  leaf_map[leaf[i]]=[lr[0],'*',sm,lr[3]]
 new=[]
 for row in rows:
  name=row[0]
  if name in insert:new.extend(insert[name])
  elif name in cut:continue
  elif name in leaf_map:new.append(leaf_map[name])
  else:new.append(row[:])
 residuals=[r for r in old['residuals']if r not in hot];terms=[]
 for i,r in enumerate(residuals):p=f'review_square_{i}';new.append([p,'*',r,r]);terms.append(p)
 terms+=guards;out=terms[0]
 for i,t in enumerate(terms[1:],1):p=f'review_sum_{i}';new.append([p,'+',out,t]);out=p
 free=[x for x in old['free']if x not in deleted];live=ancestor(new,[out]);need(set(free)|{r[0]for r in new}<=live,'all audit-constructed operations and fields live')
 M=sum(r[1]=='*'for r in new);A=len(new)-M;need(M==old['polynomial_ledger']['M']and A==old['polynomial_ledger']['A']-(2*n-1),'complete same-M2Nminus1A saving')
 return dict(N=n,cleanup=old['cleanup'],free=free,rows=new,output=out,residuals=residuals,guards=guards,sums=sums,M=M,A=A,witnesses=len(free)-3)
def diagonal(rows,free):
 e={x:[0,1]for x in free}
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else[a];b=e[b]if type(b)is str else[b];c=[0]*(len(a)+len(b)-1 if o=='*'else max(len(a),len(b)))
  if o=='*':
   for i,x in enumerate(a):
    for j,y in enumerate(b):c[i+j]+=x*y
  else:
   for i,x in enumerate(a):c[i]+=x
   for i,x in enumerate(b):c[i]+=x if o=='+'else-x
  while len(c)>1 and not c[-1]:c.pop()
  e[n]=c
 return e

def verify(root):
 root=Path(root);data={}
 for f,pin in PINS.items():
  b=(root/f).read_bytes();need(hashlib.sha256(b).hexdigest()==pin,'Authenticate parent '+f);data[f]=b
 forms=json.loads(data['eager_tree_terminal_projection.json'])['forms'];keys=[(f['packet']['N'],f['packet']['cleanup'])for f in forms];need(len(keys)==16 and all(type(n)is int and type(c)is bool for n,c in keys)and set(keys)=={(n,c)for n in range(1,9)for c in(False,True)},'Exact sixteen parent forms');counts=dict(whole_source_cut_proofs=0,full_corrections=0,rational_corrections=0,exact_degrees=0,natural_zero_maps=0,integer_guard_cases=0);out=[];rng=random.Random(38117)
 for f in forms:
  old=f['packet'];p=independent_source(old);n=p['N'];need(p['witnesses']==12*n-5,'full natural witness count')
  degree={x:1 for x in p['free']}
  for reg,op,a,b in p['rows']:
   da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0;degree[reg]=da+db if op=='*'else max(da,db)
  coefficients=diagonal(p['rows'],p['free'])[p['output']];target=6 if n==1 else 10*n-8
  need(len(coefficients)-1==degree[p['output']]==target,'actual exact whole degree')
  leader=17 if n==1 else 8*2**(10*(n-1))+2**(8*(n-1));need(coefficients[-1]==leader,'unchanged whole leading coefficient');counts['exact_degrees']+=1
  for case in range(6):
   v={k:rng.randrange(-2,4)for k in p['free']}
   if case>=4:v={k:Fraction(x,3)for k,x in v.items()};counts['rational_corrections']+=1
   lifted=restore(p,v);before=run(old['polynomial_source'],lifted);after=run(p['rows'],v);guard=sum(sumtag(v,i,n)*(sumtag(v,i,n)-1)for i in range(n))
   need(after[p['output']]==before[old['output']]+guard,'complete all-value correction')
   for i in range(n):need(before[old['residuals'][5*i]]==0 and after[old['residuals'][5*i+2]]==-before[old['residuals'][5*i+2]],'onehot cancellation and leaf sign')
   counts['full_corrections']+=1
  # Genuine natural cases independently specified from the five rules.
  for tag in range(5):
   if tag>=3 and n<3:continue
   v={k:0 for k in old['free']}
   for i in range(n):v[f'r{i}_t0']=1;v[f'r{i}_z']=1
   if tag==0:v.update(program=0,argument=0,output=1)
   elif tag==1:v.update(program=1,argument=0,output=2,r0_x=1,r0_z=2,r0_t0=0,r0_t1=1)
   elif tag==2:v.update(program=2,argument=0,output=0,r0_x=2,r0_z=0,r0_t0=0,r0_t2=1)
   elif tag==3:v.update(program=4,argument=0,output=6,r0_x=4,r0_z=6,r0_u=1,r0_v=1,r0_t0=0,r0_t3=1,r2_x=1,r2_y=1,r2_z=6,r2_t0=0,r2_t1=1)
   else:v.update(program=8,argument=0,output=2,r0_x=8,r0_z=2,r0_u=1,r0_t0=0,r0_t4=1,r2_x=1,r2_z=2,r2_t0=0,r2_t1=1)
   need(set(v)==set(old['free']),'natural fixture exactly matches parent fields');need(run(old['polynomial_source'],v)[old['output']]==0,'genuine parent natural zero')
   child={k:v[k]for k in p['free']};need(run(p['rows'],child)[p['output']]==0 and restore(p,child)==v,'both zero maps and unique restored tag');counts['natural_zero_maps']+=1
  counts['whole_source_cut_proofs']+=1;out.append(dict(N=n,cleanup=p['cleanup'],M=p['M'],A=p['A'],witnesses=p['witnesses'],squared_residuals=len(p['residuals']),unsquared_guards=len(p['guards']),degree=target,leading_coefficient=leader,independent_source_sha256=digest(p['rows'])))
 for s in range(-20,21):need(s*(s-1)>=0 and(s*(s-1)==0)==(s in(0,1)),'integer guard theorem checks');counts['integer_guard_cases']+=1
 old=next(f['packet']for f in forms if f['packet']['N']==1 and f['packet']['cleanup']);p=independent_source(old);v={k:Fraction(0)for k in p['free']};v.update(r0_t1=Fraction(1,2),r0_x=Fraction(1,2),program=Fraction(1,2),r0_z=Fraction(2),output=Fraction(2))
 restored=restore(p,v);newval=run(p['rows'],v)[p['output']];oldval=run(old['polynomial_source'],restored)[old['output']];need(newval==0 and oldval==Fraction(1,4)and all(x>=0 for x in restored.values()),'nonnegative rational counterexample')
 signed={k:0 for k in old['free']};signed.update(r0_t0=-1,r0_t2=2,r0_b=1,r0_z=1,r0_x=12,program=12,argument=0,output=1)
 projected={k:signed[k]for k in p['free']};signed_old=run(old['polynomial_source'],signed)[old['output']];signed_new=run(p['rows'],projected)[p['output']]
 need(signed_old==0 and signed_new==2 and restore(p,projected)==signed,'signed parent reverse zero-map counterexample')
 return dict(status='PASS_LEAF_TAG_MATH_ONLY',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_pins=PINS,counts=counts,forms=out,rational_counterexample=dict(child={k:str(x)for k,x in v.items()},restored_parent={k:str(x)for k,x in restored.items()},child_value=str(newval),parent_value=str(oldval)),signed_parent_counterexample=dict(parent=signed,projected_child=projected,parent_value=signed_old,child_value=signed_new),scope='Independent math/source-cut audit against frozen terminal parent only. Does not import or review the new maintained child/API. Natural zero bijection; restoration may be negative off zeros; no rational zero equivalence.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
