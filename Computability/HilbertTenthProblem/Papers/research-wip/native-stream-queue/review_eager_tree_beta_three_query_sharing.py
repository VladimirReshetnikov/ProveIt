#!/usr/bin/env python3
"""Independent full-polynomial review of the local three-query beta batch."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PARENT={
'eager_tree_beta_membership_interface.py':'bdb27b56b8701a1e392e799e742d135a4c0f107abc987982c5eb59efe947be34',
'eager_tree_beta_membership_interface.json':'de8da8729d5167aa1196d374d4603dec865a9b6ae4529747afc632576dd83f7b',
'eager_tree_beta_membership_interface.md':'b7f3ef7c12f0ae0ff14cd49ec57802b06d6842bd5b30bc044397d02866a115e3',
}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def pins(root,manifest):
 out={}
 for n,h in manifest.items():
  b=(Path(root)/n).read_bytes();need(sha(b)==h,'Pinned blob '+n);out[n]=b
 return out

def run(rows,v):
 e=dict(v)
 for name,op,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b
  e[name]=a*b if op=='*'else a+b if op=='+'else a-b
 return e

class Ring:
 def __init__(self,names):self.names=names;self.zero=(0,)*len(names)
 def atom(self,x):
  if type(x)is int:return {self.zero:x}if x else{}
  v=list(self.zero);v[self.names.index(x)]=1;return {tuple(v):1}
 def add(self,a,b,sign=1):
  out=dict(a)
  for e,c in b.items():out[e]=out.get(e,0)+sign*c
  return {e:c for e,c in out.items()if c}
 def mul(self,a,b):
  out={}
  for u,c in a.items():
   for v,d in b.items():e=tuple(x+y for x,y in zip(u,v));out[e]=out.get(e,0)+c*d
  return {e:c for e,c in out.items()if c}
 def source(self,rows):
  e={n:self.atom(n)for n in self.names}
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.atom(a);b=e[b]if type(b)is str else self.atom(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else -1)
  return e
 def serialize(self,p):return [[list(e),c]for e,c in sorted(p.items())]

def inspect(p):
 known=set(p['inputs']+p['witnesses']);defs={};M=0
 for row in p['source']:
  need(type(row)is list and len(row)==4,'literal binary row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'fresh arithmetic gate')
  need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'source closure/exact numeral')
  known.add(n);defs[n]=(a,b);M+=o=='*'
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(defs.get(n,()))
 need(known<=live,'every gate and supplied coordinate live')
 return M,len(p['source'])-M


AUTHOR={
'eager_tree_beta_three_query_sharing.py':'498a9924f743905033be5e93a492ddf58b4cbbcf0c541f17a174690657fbf8b0',
'eager_tree_beta_three_query_sharing.json':'e5af329a782aab92b31da1ea2023e6e6965dc7ebd8ccb4ff71a78a6062ac7dc7',
'eager_tree_beta_three_query_sharing.md':'8ad5dfc4c20ca4116da16dd6136a61133af7e8088f77dbb6e03a10a9fa9026dd',
}
def canonical_literal(old,computed,shared):
 rows=[['active','+','t3','t4']]if computed else[]
 if shared:rows.append(['shared_i2','+','i',2])
 res=[];outs=[]
 for j in range(3):
  mapping={'A':'A','b':'b','i':'i','N':'N','D':f'D{j}','active':'active'if j<2 else't3'}
  mapping.update({n:f'{n}{j}'for n in old['witnesses']});mapping.update({n:f'query{j}_{n}'for n,o,a,b in old['source']})
  for n,o,a,b in old['source']:
   if shared and n=='ih':continue
   if shared and n=='j1':rows.append([mapping[n],'+','shared_i2',f'h{j}'])
   else:rows.append([mapping[n],o,mapping[a]if type(a)is str else a,mapping[b]if type(b)is str else b])
  res.extend(mapping[r]for r in old['residuals']);outs.append(mapping[old['output']])
 if shared:
  rows.extend([['first_pair','+',outs[0],outs[1]],['first_guard','*','active','first_pair'],['third_guard','*','t3',outs[2]],['output','+','first_guard','third_guard']])
 else:rows.extend([['baseline_pair','+',outs[0],outs[1]],['output','+','baseline_pair',outs[2]]])
 return rows,res

def verify(root,artifacts):
 parent=pins(root,PARENT);ab=pins(artifacts,AUTHOR);old=json.loads(parent['eager_tree_beta_membership_interface.json']);saved=json.loads(ab['eager_tree_beta_three_query_sharing.json'])
 need(old['source_sha256']==PARENT['eager_tree_beta_membership_interface.py']and saved['source_sha256']==AUTHOR['eager_tree_beta_three_query_sharing.py'],'literal source/receipt links')
 need(exact(saved['parent_pins'],PARENT)and len(saved['forms'])==2,'exact provenance and two modes')
 parent_ungated=old['forms'][0]['packet'];parent_gated=old['forms'][1]['packet']
 path=Path(artifacts)/'eager_tree_beta_three_query_sharing.py';author=types.ModuleType('_authenticated_three_query');author.__file__=str(path);exec(compile(ab[path.name],str(path),'exec'),author.__dict__)
 counts=dict(literal_complete_sources=0,complete_polynomial_identities=0,residual_identities=0,exact_leaders=0,paid_live_gates=0,numeric_identities=0,rational_identities=0,natural_zero_maps=0,inactive_empty_maps=0,coordinate_counterexamples=0,guards=0,copies=0,warm_pins=0)
 forms=[];rng=random.Random(90411)
 for computed in(False,True):
  p=author.build(computed,root=root);baseline=author.canonical_parent(computed,root=root);entry=saved['forms'][int(computed)]
  need(exact(p,entry['packet'])and exact(baseline,entry['baseline']),'entire saved actual packets')
  inputs=['A','b','i','N','D0','D1','D2']+(['t3','t4']if computed else['active','t3']);witnesses=[f'{s}{j}'for j in range(3)for s in('h','k','q','s')]
  need(p['inputs']==baseline['inputs']==inputs and p['witnesses']==baseline['witnesses']==witnesses,'unchanged complete scalar coordinates')
  for packet,model,shared in[(p,parent_ungated,True),(baseline,parent_gated,False)]:
   rows,residuals=canonical_literal(model,computed,shared)
   need(exact(packet['source'],rows)and exact(packet['residuals'],residuals)and packet['output']=='output','literal full reconstruction')
   M,A=inspect(packet);wantM=17 if shared else 18;wantA=(33 if shared else 35)+int(computed)
   need((M,A)==(wantM,wantA)and packet['ledger']==dict(M=M,A=A,operations=M+A,all_live=True),'whole paid baseline/child ledger')
   counts['literal_complete_sources']+=1;counts['paid_live_gates']+=M+A
  ring=Ring(inputs+witnesses);a=ring.add;m=ring.mul;v={n:ring.atom(n)for n in inputs+witnesses};constant=ring.atom
  act=a(v['t3'],v['t4'])if computed else v['active'];expected={};body=[]
  before=ring.source(baseline['source']);after=ring.source(p['source'])
  for j in range(3):
   index=a(a(v['i'],v[f'h{j}']),constant(2));g=m(v['b'],index)
   residuals=[a(a(v['A'],v[f'D{j}'],-1),m(v[f'q{j}'],a(g,constant(1))),-1),a(a(g,v[f'D{j}'],-1),v[f's{j}'],-1),a(a(v['N'],index,-1),v[f'k{j}'],-1)]
   S={}
   for k,r in enumerate(residuals):
    port=f'query{j}_r{k}';need(before[port]==after[port]==r,'full handwritten query residual');S=a(S,m(r,r));counts['residual_identities']+=1
   body.append(S);expected=a(expected,m(act if j<2 else v['t3'],S))
  need(before['output']==after['output']==expected,'exact complete all-value polynomial identity')
  leader={power:c for power,c in expected.items()if sum(power)==7};wantleader={}
  for j in range(3):
   term=m(m(v['b'],v[f'q{j}']),a(v['i'],v[f'h{j}']));term=m(term,term);wantleader=a(wantleader,m(act if j<2 else v['t3'],term))
  need(leader==wantleader and max(sum(power)for power in expected)==7==p['exact_degree']==baseline['exact_degree'],'exact degree and all highest coefficients')
  need(sum(leader.values())==(20 if computed else 12),'all-free diagonal leader')
  savedpoly={}
  for term in entry['expanded_polynomial']:
   powers=[0]*len(ring.names)
   for n in term['monomial']:powers[ring.names.index(n)]+=1
   need(tuple(powers)not in savedpoly,'saved coefficient uniqueness');savedpoly[tuple(powers)]=term['coefficient']
  need(savedpoly==expected,'every saved full coefficient')
  need(p['full_polynomial_identity']is True and p['natural_zero_tuple_bijection']=='Identity map on the same complete supplied natural tuple','current equality/domain metadata')
  need(exact(p['parent_pins'],PARENT)and exact(p['baseline_ledger'],baseline['ledger'])and p['baseline_source_sha256']==sha(json.dumps(baseline['source'],sort_keys=True,separators=(',',':')).encode()),'current provenance and full baseline')
  counts['complete_polynomial_identities']+=1;counts['exact_leaders']+=1
  for case in range(24):
   values={n:rng.randrange(5)if case<8 else rng.randrange(-3,5)for n in inputs+witnesses}
   if case>=20:values={n:Fraction(x,5)for n,x in values.items()};counts['rational_identities']+=1
   result=run(p['source'],values)['output'];need(run(baseline['source'],values)['output']==result,'complete numeric source identity');counts['numeric_identities']+=1
   if case<20:need(author.evaluate(p,values,signed=case>=8,root=root)==result,'canonical public evaluator')
  for A in(0,2,19,215):
   for b in(0,1,3):
    values=dict(A=A,b=b,i=1,N=6,t3=2)
    if computed:values['t4']=3
    else:values['active']=5
    for j,index in enumerate((2,4,5)):
     modulus=1+(index+1)*b;D=A%modulus;values.update({f'D{j}':D,f'h{j}':index-2,f'k{j}':5-index,f'q{j}':A//modulus,f's{j}':modulus-1-D})
    need(min(values.values())>=0 and author.evaluate(p,values,root=root)==run(baseline['source'],values)['output']==0,'three separate canonical natural member witnesses');counts['natural_zero_maps']+=1
  for N in(0,1,2):
   values={n:7 for n in inputs+witnesses};values.update(i=3,N=N,t3=0)
   values['t4'if computed else'active']=0
   need(author.evaluate(p,values,root=root)==run(baseline['source'],values)['output']==0,'inactive empty suffix remains unrestricted');counts['inactive_empty_maps']+=1
  forms.append(dict(computed_active=computed,operations=p['ledger']['operations'],baseline_operations=baseline['ledger']['operations'],inputs=inputs,witnesses=witnesses,exact_degree=7,highest_coefficients=ring.serialize(leader),full_coefficients=ring.serialize(expected)))
 # Exact syntactic side candidates: independently reconstruct the two failed substitutions.
 hbad=copy.deepcopy(parent_ungated);hbad['witnesses']=['H','k','q','s'];hbad['source']=[r for r in hbad['source']if r[0]!='ih'];hbad['source'][0]=['j1','+','H',2]
 sbad=copy.deepcopy(parent_ungated);sbad['witnesses']=['h','k','q','S'];sbad['source']=[r for r in sbad['source']if r[0]!='gD'];sbad['source']=[['r1','-','g','S']if r[0]=='r1'else r for r in sbad['source']]
 fixtures=[(hbad,dict(A=0,b=1,i=1,N=2,D=0,H=0,k=0,q=0,s=2),'inverse_h'),(sbad,dict(A=3,b=1,i=0,N=2,D=3,h=0,k=0,q=0,S=2),'inverse_s')]
 for entry,(packet,values,inverse)in zip(saved['invalid15gate_candidates'],fixtures):
  need(exact(entry['packet'],packet)and exact(entry['assignment'],values)and entry[inverse]==-1,'actual failed coordinate source and inverse')
  need(len(packet['source'])==15 and min(values.values())>=0 and run(packet['source'],values)['sos']==0,'full natural false zero of syntactic15 candidate')
  need(not any(values['A']%(1+(j+1)*values['b'])==values['D']for j in range(values['i']+1,values['N'])),'actual suffix predicate false');counts['coordinate_counterexamples']+=1
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise ValueError('Malformed public call accepted')
 for bad in(0,1,None,'yes',1.0):
  for fn in(author.build,author.canonical_parent):reject(lambda fn=fn,bad=bad:fn(bad,root=root))
 p=author.build(root=root);values={n:0 for n in p['inputs']+p['witnesses']}
 for key in p:
  q=copy.deepcopy(p);del q[key];reject(lambda q=q:author.checked(q,root=root))
 for key in('computed_active','full_polynomial_identity'):
  q=copy.deepcopy(p);q[key]=int(q[key]);reject(lambda q=q:author.checked(q,root=root))
 for key in('inputs','witnesses','source','residuals'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:author.checked(q,root=root))
 q=copy.deepcopy(p);q['exact_degree']=7.0;reject(lambda:author.checked(q,root=root))
 q=copy.deepcopy(p);q['source'][-1][1]='-';reject(lambda:author.checked(q,root=root))
 for val in(True,1.0,Fraction(1),-1):
  q=dict(values,A=val);reject(lambda q=q:author.evaluate(p,q,root=root))
 for mode in(0,1,None):reject(lambda mode=mode:author.evaluate(p,values,signed=mode,root=root))
 for q in({},dict(values,extra=0),list(values)):reject(lambda q=q:author.evaluate(p,q,root=root))
 for key,val in p.items():
  if type(val)in(dict,list):
   q=author.build(root=root);q[key].clear();need(exact(author.build(root=root),p),'fresh packet member copy');counts['copies']+=1
 for fn in(lambda:author.canonical_parent(root=root),lambda:author.checked(p,root=root)):
  q=fn();q['source'].clear();need(exact(author.build(root=root),p),'accessor source copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='beta_batch_independent_')as temp:
  temp=Path(temp)
  for n,b in parent.items():(temp/n).write_bytes(b)
  need(exact(author.build(root=temp),p),'warm valid parents')
  for n,b in parent.items():
   (temp/n).write_bytes(b+b'\n')
   for fn in(lambda:author.authenticate(temp),lambda:author.build(root=temp),lambda:author.canonical_parent(root=temp),lambda:author.checked(p,root=temp),lambda:author.evaluate(p,values,root=temp)):reject(fn);counts['warm_pins']+=1
   (temp/n).write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(path)],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'optimized Python reject');counts['optimized_rejections']=1
 return dict(status='PASS_INDEPENDENT_BETA_THREE_QUERY_SHARING',review_source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,parent_pins=PARENT,counts=counts,forms=forms,scope='Complete local50/51 sources equal complete53/54 baseline polynomials at all tuples. Same12 natural witnesses, exact degree7. No complete fixed-arity Tree count or generic15-gate improvement.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root,a.artifacts)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'exact saved review receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts'])
if __name__=='__main__':main()
