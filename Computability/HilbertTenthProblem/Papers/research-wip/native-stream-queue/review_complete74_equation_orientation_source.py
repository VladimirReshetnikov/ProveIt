#!/usr/bin/env python3
"""Independent full-source and two-way zero-set audit of 56 orientations.
Only the author CLI authentication rejection paths are executed; no census or historical module runs.
"""
import argparse,ast,copy,hashlib,itertools,json,random,subprocess,sys,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
AUTHOR={'complete74_equation_orientation_census.py': 'e4265e24f826fef6f4bfeebd2d5af2742b16f853b91f6f1a044ae3851099218e', 'complete74_equation_orientation_census.json': '627568df8674e3fbe32bac6881a9ef89587a902ed25476b2a541f1eff0875559', 'complete74_equation_orientation_census.md': '292f4b2ef80c9eca684e50e561efd21469a9ad9d0c9970aab537f30f93d0776d'}
PINS={'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete74_asymmetric_scale_transfer.py': 'c0f3852a1d4c50dba3d7aeb6c877290ebcf18b233dbf944d1870780ab942b8d6', 'complete74_asymmetric_scale_transfer.json': '14816c4da8738e3c27cc1ec0217c450075c0e47b20d77ec4c4d8159aac24dc88', 'complete74_asymmetric_scale_transfer.md': '0484dc71131d7d132e12c7961de731ca4c5bb91adc98447f72fed77882461fe3', 'review_complete74_asymmetric_scale_math.py': 'fbefd6b86533634894eb66daf16788a523c15bcfc2cb0fa813b4f91fe140702f', 'review_complete74_asymmetric_scale_math.json': '759a29961791ce779819250b3e54cfc3ae412ec26d7db63c0865705caa297ca3', 'review_complete74_asymmetric_scale_math.md': 'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58', 'complete75_auxiliary_degree_tradeoffs.md': '6c56201bff3cfc95eb5677bf24f0ea2c27033995d8753aadeebf99447db36dcc'}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def unused_pins(root,manifest):
 out={}
 for n,h in manifest.items():
  b=(Path(root)/n).read_bytes();need(sha(b)==h,'Pinned blob '+n);out[n]=b
 return out
def numeric(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return e

def ledger(rows,free,outputs,fixed=()):
 known=set(free);defs={};degree={x:0 if x in fixed else 1 for x in free}
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'fresh exact gate')
  need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'source closure')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0
  degree[n]=da+db if o=='*'else max(da,db);known.add(n);defs[n]=(a,b)
 live=set();stack=list(outputs)
 while stack:
  x=stack.pop()
  if type(x)is int or x in live:continue
  live.add(x);stack.extend(defs.get(x,()))
 need(set(defs)|set(free)<=live,'all paid rows/coordinates live')
 M=sum(r[1]=='*'for r in rows)
 return M,len(rows)-M,max(degree[x]if type(x)is str else 0 for x in outputs)
class RingDAG:
 # Linear combinations of opaque product atoms. Addition normalizes exact
 # coefficients; multiplication extracts scalar signs but never expands sums.
 def __init__(self):self.ids={('one',):0}
 def node(self,key):
  if key not in self.ids:self.ids[key]=len(self.ids)
  return self.ids[key]
 def val(self,x):return ((0,x),)if type(x)is int and x else()if type(x)is int else((self.node(('var',x)),1),)
 def scale(self,e,c):return tuple((k,v*c)for k,v in e)if c else()
 def add(self,a,b,sign=1):
  e=dict(a)
  for n,c in b:e[n]=e.get(n,0)+sign*c
  return tuple(sorted((n,c)for n,c in e.items()if c))
 def mul(self,a,b):
  if not a or not b:return()
  if len(a)==1 and a[0][0]==0:return self.scale(b,a[0][1])
  if len(b)==1 and b[0][0]==0:return self.scale(a,b[0][1])
  sa=-1 if a[0][1]<0 else 1;sb=-1 if b[0][1]<0 else 1
  a=self.scale(a,sa);b=self.scale(b,sb)
  if a>b:a,b=b,a
  return((self.node(('mul',a,b)),sa*sb),)
 def run(self,rows,free,replacements=None):
  e={n:self.val(n)for n in free};e.update(replacements or{})
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.val(a);b=e[b]if type(b)is str else self.val(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else -1)
  return e



def finalize(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 name='square_0'
 for i in range(1,len(pairs)):
  n=f'sum_{i}';out.append([n,'+',name,f'square_{i}']);name=n
 return out,name

def consumers(p,n):
 return {'source':[r[0]for r in p['source']if n in r[2:]],'comparisons':[i for i,pair in enumerate(p['comparisons'])if n in pair]}

FLAGS=('asymmetric','E_from_a','kY_from_c','kappa_from_gap','aux_root_rhs','aux_coefficient_rhs')
MODES=('raw30','positive22','signed20')

def authenticate(root,artifacts):
 need(len(AUTHOR)==3 and bool(PINS),'frozen review pins required')
 blobs={}
 for name,digest in PINS.items():
  p=Path(root)/name
  if not p.exists():p=Path(root)/Path(name).name
  b=p.read_bytes();need(sha(b)==digest,'reviewed parent pin '+name);blobs[name]=b
 for name,digest in AUTHOR.items():
  b=(Path(artifacts)/name).read_bytes();need(sha(b)==digest,'reviewed author pin '+name);blobs[name]=b
 return blobs

def manifest(source):
 tree=ast.parse(source)
 matches=[n for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='PINS'for t in n.targets)]
 need(len(matches)==1,'one literal pin inventory');return ast.literal_eval(matches[0].value)

def recipe_set():
 result=set()
 for mode in MODES:
  for scale in(False,True):
   for bits in itertools.product((False,True),repeat={'raw30':4,'positive22':3,'signed20':2}[mode]):
    E=C=K=False
    if mode=='raw30':E,C,H,D=bits
    elif mode=='positive22':K,H,D=bits
    else:H,D=bits
    result.add((mode,scale,E,C,K,H,D))
 need(len(result)==56,'independent recipe cardinality');return result

def reference(parent,asymmetric):
 p=copy.deepcopy(parent)
 if asymmetric:
  hits=[r for r in p['source']if r==['wn2','*','w','n2']];need(len(hits)==1,'literal asymmetric source cut');hits[0][3]='q'
 p['polynomial_source'],p['output']=finalize(p['source'],p['comparisons']);return p

def expected_edits(parent,flags):
 p=reference(parent,flags['asymmetric']);d={n:[n,o,a,b]for n,o,a,b in p['source']};pairs=copy.deepcopy(p['comparisons']);protected=[]
 if flags['E_from_a']:
  need(p['mode']=='raw30'and d['UM']==['UM','*','wn2','sn2']and d['R12']==['R12','+','UM','sn2'],'independent exact E orientation premise')
  d['UM']=['UM','-','a','sn2'];d['R12']=['R12','*','wn2','sn2'];i=pairs.index(['a','R12']);pairs[i]=['UM','R12'];protected.append(i)
 if flags['kY_from_c']:
  need(p['mode']=='raw30'and d['ksn2']==['ksn2','*','k','sn2']and d['R10a']==['R10a','+','ksn2','eta'],'independent exact kY orientation premise')
  d['ksn2']=['ksn2','-','c','eta'];d['R10a']=['R10a','*','k','sn2'];i=pairs.index(['c','R10a']);pairs[i]=['ksn2','R10a'];protected.append(i)
 if flags['kappa_from_gap']:
  need(p['mode']=='positive22'and d['pell_gap']==['pell_gap','+','index_rhs','phi'],'independent actual input gap premise')
  need(consumers(p,'index_rhs')=={'source':['pell_gap','difference_multiple','kappa2'],'comparisons':[]}and consumers(p,'phi')=={'source':['pell_gap'],'comparisons':[]},'all old kappa/phi consumers')
  d['pell_gap']=['pell_gap','-','R10a','phi'];d['difference_multiple']=['difference_multiple','*','pell_gap','R12'];d['kappa2']=['kappa2','*','pell_gap','pell_gap']
  i=pairs.index(['R10a','pell_gap']);pairs[i]=['pell_gap','index_rhs'];protected.append(i)
 if flags['aux_root_rhs']:
  need(d['H2']==['H2','*','H17','H17'],'actual auxiliary square producer');d['H2']=['H2','*','aux_u_rhs','aux_u_rhs'];protected.append(pairs.index(['H17','aux_u_rhs']))
 if flags['aux_coefficient_rhs']:
  need(d['L17']==['L17','*','ic22','aux_square_gap'],'actual auxiliary coefficient producer');d['L17']=['L17','*','R16','aux_square_gap'];protected.append(pairs.index(['ic22','R16']))
 return p,d,pairs,sorted(protected)

def protected_proof(old,new,flags,protected):
 ring=RingDAG();free=old['fixed_numerals']+old['witnesses']+[old['ordinary_input']]
 def run(rows,inputs=None,ports=None):
  e={n:ring.val(n)for n in free};e.update(inputs or{})
  for n,o,a,b in rows:
   if ports and n in ports:e[n]=ports[n];continue
   aa=e[a]if type(a)is str else ring.val(a);bb=e[b]if type(b)is str else ring.val(b)
   e[n]=ring.mul(aa,bb)if o=='*'else ring.add(aa,bb,1 if o=='+'else-1)
  return e
 plain_old=run(old['polynomial_source']);plain_new=run(new['polynomial_source'])
 for i in protected:need(plain_old[f'residual_{i}']==plain_new[f'residual_{i}'],'each actual protected residual is unconditionally the same polynomial')
 substitutions={};support=[]
 if flags['E_from_a']:
  substitutions['a']=plain_old['R12'];support.append(('a','R12'))
 if flags['kY_from_c']:
  substitutions['c']=plain_old['R10a'];support.append(('c','R10a'))
 if flags['kappa_from_gap']:
  substitutions['phi']=ring.add(plain_old['R10a'],plain_old['index_rhs'],-1);support.append(('phi','R10a'));support.append(('phi','index_rhs'))
 # Guard that each free-coordinate substitution is acyclic and exactly a
 # solved monic defining row, rather than silently presupposing another norm.
 defs={r[0]:r[2:]for r in old['source']}
 def leaves(n):
  if type(n)is int:return set()
  if n not in defs:return{n}
  return set().union(*(leaves(x)for x in defs[n]))
 for coordinate,port in support:need(coordinate not in leaves(port)and not(set(substitutions)&leaves(port)),'monic replacements have no dependent eliminated coordinate')
 a=run(old['source'],substitutions);b=run(new['source'],substitutions)
 ports={}
 if flags['aux_root_rhs']:
  need(a['aux_u_rhs']==b['aux_u_rhs'],'common protected root RHS after graph definitions');ports['H17']=a['aux_u_rhs']
 if flags['aux_coefficient_rhs']:
  need(a['R16']==b['R16'],'common protected coefficient RHS after graph definitions');ports['ic22']=a['R16']
 # Exact descendants of each cut must not be read to produce its RHS.
 def ancestors(n):
  if type(n)is int or n not in defs:return set()
  return {n}|set().union(*(ancestors(x)for x in defs[n]))
 if flags['aux_root_rhs']:need('H17'not in ancestors('aux_u_rhs')and'ic22'not in ancestors('aux_u_rhs'),'aux root RHS independent of the cuts')
 if flags['aux_coefficient_rhs']:need('ic22'not in ancestors('R16')and'H17'not in ancestors('R16'),'aux coefficient RHS independent of the cuts')
 a=run(old['polynomial_source'],substitutions,ports);b=run(new['polynomial_source'],substitutions,ports)
 for i in range(len(old['comparisons'])):need(a[f'residual_{i}']==b[f'residual_{i}'],'every residual equal on exactly the common retained locus')
 for i in protected:need(a[f'residual_{i}']==(),'each imposed condition really is its retained zero residual')
 need(a[old['output']]==b[new['output']],'whole finalizer equal on the common protected locus')
 return dict(unconditional_protected_residual_identities=len(protected),conditional_retained_residual_identities=len(old['comparisons']),
  complete_conditional_polynomial_identity=True,two_way_same_integer_and_positive_zero_equivalence=True,
  reasoning='Protected residuals are identical without assumptions. Every zero of either full SOS lies on that same locus; all other residuals agree on it.')

def conditioning(parent,flags,v):
 v=dict(v)
 if flags['E_from_a']:v['a']=numeric(parent['source'],v)['R12']
 if flags['kY_from_c']:v['c']=numeric(parent['source'],v)['R10a']
 if flags['kappa_from_gap']:
  e=numeric(parent['source'],v);v['phi']=e['R10a']-e['index_rhs']
 if flags['aux_coefficient_rhs']:v['i']=0;v['f']=1
 if flags['aux_root_rhs']:
  e=numeric(parent['source'],v);c=e['c']if parent['mode']=='raw30'else e['R10a'];v['r']=(v['j']+1)*c-v['o']*v['f']
 return v

def local_corrections(saved):
 def add(a,b,s=1):
  r=dict(a)
  for m,c in b.items():r[m]=r.get(m,0)+s*c
  return{m:c for m,c in r.items()if c}
 def mul(a,b):
  r={}
  for u,c in a.items():
   for v,d in b.items():
    m=tuple(sorted(u+v));r[m]=r.get(m,0)+c*d
  return{m:c for m,c in r.items()if c}
 encode=lambda p:[[list(m),c]for m,c in sorted(p.items())]
 term=lambda c,*variables:{tuple(sorted(variables)):c}
 def total(terms):
  p={}
  for t in terms:p=add(p,t)
  return p
 main=total([term(1,'X','X'),term(2,'X','a','c'),term(2,'X','G'),term(2,'a','c','G'),term(1,'G','G'),term(-1,'H','c','c'),term(-1)])
 inp=total([term(1,'W','W'),term(2,'a','W','k'),term(2,'rho','W','H'),term(2,'a','rho','k','H'),term(1,'rho','rho','H','H'),term(-1,'H','k','k'),term(-1)])
 need(encode(main)==saved['main']and encode(inp)==saved['input'],'exact saved main/input cancellation coefficients')
 one={():1};T,U,V,K,y=[term(1,n)for n in('T','U','V','K','y')];sq=lambda p:mul(p,p)
 residual=lambda c,u:add(mul(c,add(sq(u),sq(y),-1)),add(one,sq(y),-1),-1)
 old=residual(T,U);entries=[]
 for root,coef in((True,False),(False,True),(True,True)):
  new=residual(K if coef else T,V if root else U);delta=add(new,old,-1)
  need(add(sq(new),sq(old),-1)==mul(delta,add(add(old,old),delta)),'full changed-square correction')
  entries.append(dict(root=root,coefficient=coef,terms=encode(delta)))
 need(exact(entries,saved['auxiliary_corrections']),'all three actual auxiliary correction coefficient records')
 return dict(main_and_input_coefficient_records=2,auxiliary_residual_corrections=3,whole_square_corrections=3)

def verify(root,artifacts):
 blobs=authenticate(root,artifacts);author=blobs['complete74_equation_orientation_census.py'];saved=json.loads(blobs['complete74_equation_orientation_census.json'])
 declared=manifest(author);need(declared and all(n in PINS and PINS[n]==h for n,h in declared.items()),'independently authenticate every declared author dependency')
 need(exact(saved['pins'],declared)and saved['source_sha256']==sha(author),'saved receipt binds exact source and manifest')
 parents={f['mode']:f['packet']for f in json.loads(blobs['complete74_factored_first_norm.json'])['forms']}
 asym={f['packet']['mode']:f['packet']for f in json.loads(blobs['complete74_asymmetric_scale_transfer.json'])['forms']}
 expected=recipe_set();seen=set();records=[];counts=Counter();rng=random.Random(5674);local=local_corrections(saved['local_coefficient_identities'])
 for form in saved['forms']:
  p=form['packet'];flags=p['orientation'];need(type(flags)is dict and set(flags)==set(FLAGS)and all(type(x)is bool for x in flags.values()),'exact Boolean recipe fields')
  recipe=(p['mode'],*(flags[k]for k in FLAGS));need(recipe in expected and recipe not in seen,'unique independently allowed recipe');seen.add(recipe)
  old,definitions,pairs,protected=expected_edits(parents[p['mode']],flags)
  if flags['asymmetric']:
   a=asym[p['mode']];need(old['source']==a['source']and old['comparisons']==a['comparisons']and old['polynomial_source']==a['polynomial_source'],'actual proved asymmetric parent, not an unproved interface')
  need({r[0]:r for r in p['source']}==definitions and len(p['source'])==len(definitions),'every actual row and operand independently reconstructed')
  need(p['comparisons']==pairs and p['protected_comparison_indices']==protected,'all actual comparison substitutions and protected indices')
  for field in('mode','witnesses','fixed_numerals','ordinary_input'):need(exact(p[field],old[field]),'same full supplied interface '+field)
  need('exact_polynomial_degree'not in p and'transformation'not in p and'original_comparison_indices'not in p,'stale parent-only metadata removed')
  poly,out=finalize(p['source'],pairs);need(poly==p['polynomial_source']and out==p['output'],'every literal finalizer gate reconstructed')
  free=p['fixed_numerals']+p['witnesses']+[p['ordinary_input']]
  M,A,_=ledger(p['source'],free,[x for pair in pairs for x in pair],p['fixed_numerals']);PM,PA,_=ledger(poly,free,[out],p['fixed_numerals'])
  cl=dict(operations=M+A,M=M,A=A,all_gates_live=True);pl=dict(operations=PM+PA,M=PM,A=PA,all_gates_live=True)
  need(exact(cl,p['certificate_ledger'])and exact(pl,p['polynomial_ledger']),'both complete ledgers independently paid')
  need((M,A)==(40,34)and(PM,PA)=={'raw30':(59,71),'positive22':(51,55),'signed20':(49,51)}[p['mode']],'same complete costs after all consumers')
  proof=protected_proof(old,p,flags,protected)
  for n in('unconditional_protected_residual_identities','conditional_retained_residual_identities'):counts[n]+=proof[n]
  counts['whole_source_proofs']+=1;counts['live_paid_polynomial_gates']+=PM+PA
  positive_difference=False
  for case in range(8):
   v={n:rng.randrange(1,5)for n in free};v.update(Bm1=15,Kconstant=17,twice_cell_bits=8,inner_bits=3,MC=2,MF=19)
   if case>=4:v={n:Fraction(x,3)for n,x in v.items()}
   plain_old=numeric(old['polynomial_source'],v);plain_new=numeric(poly,v)
   if case<4 and plain_old[old['output']]!=plain_new[out]:positive_difference=True
   v=conditioning(old,flags,v);a=numeric(old['polynomial_source'],v);b=numeric(poly,v)
   for i in protected:need(a[f'residual_{i}']==b[f'residual_{i}']==0,'numeric fixture lies on actual shared protected locus')
   for i in range(len(pairs)):need(a[f'residual_{i}']==b[f'residual_{i}'],'complete conditional numeric residual identity');counts['numeric_residual_identities']+=1
   need(a[old['output']]==b[out],'entire conditional numeric SOS identity');counts['whole_conditional_numeric_identities']+=1;counts['rational_conditional_cases']+=case>=4
  active=any(flags[k]for k in FLAGS if k!='asymmetric')
  need(positive_difference==active,'unconditional polynomial distinction is explicit for every nontrivial orientation')
  counts['positive_off_zero_polynomial_difference_examples']+=positive_difference
  cp=form['conditional_proof'];need(cp['same_tuple_zero_equivalence']is True and cp['unconditional_polynomial_identity_claimed']is(not active),'truthful conditional-vs-all-value claims')
  need(type(p['degree']['exact_degree'])is int and p['degree']['exact_degree']>0,'current exact-degree metadata is typed; independent degree proof is a separate review')
  source_hash=sha(json.dumps(poly,sort_keys=True,separators=(',',':')).encode());need(source_hash==form['source_sha256'],'every complete source digest recomputed')
  records.append(dict(recipe=list(recipe),certificate_ledger=cl,polynomial_ledger=pl,protected_comparisons=protected,proof=proof,
   no_unconditional_polynomial_identity=active,source_sha256=source_hash))
 need(seen==expected and len(records)==56,'all and only 56 recipes independently covered')
 need(saved['counts']['whole_sources']==56 and saved['counts']['live_paid_gates']==counts['live_paid_polynomial_gates']and saved['counts']['retained_residual_identities']==counts['conditional_retained_residual_identities'],'saved structural aggregate counts independently reproduced')
 # The published author interface is a pinned CLI. Importable helper build is
 # not a canonical guarded API. Test entry rejection without running its suite.
 with tempfile.TemporaryDirectory(prefix='orientation_review_')as tmp:
  folder=Path(tmp)
  for n in declared:(folder/n).parent.mkdir(parents=True,exist_ok=True);(folder/n).write_bytes(blobs[n])
  source=Path(artifacts)/'complete74_equation_orientation_census.py'
  for n in declared:
   path=folder/n;data=path.read_bytes();path.write_bytes(data+b'\n')
   proc=subprocess.run([sys.executable,str(source),'--root',str(folder)],capture_output=True,text=True)
   need(proc.returncode!=0 and 'source pin '+n in proc.stderr,'CLI rejects changed dependency before source census');counts['cli_pin_rejections']+=1;path.write_bytes(data)
  proc=subprocess.run([sys.executable,'-O',str(source),'--root',str(folder)],capture_output=True,text=True)
  need(proc.returncode!=0 and 'Run without -O'in proc.stderr,'optimized-mode entry rejection');counts['optimized_mode_rejections']=1
 return dict(status='PASS_INDEPENDENT_EQUATION_ORIENTATION_SOURCE',source_sha256=sha(Path(__file__).read_bytes()),author_pins=copy.deepcopy(AUTHOR),parent_pins=copy.deepcopy(PINS),
  scope=dict(complete_sources=56,all_paid_finalizers=True,same_positive_tuple_zero_equivalence=True,
   author_arithmetic_verification_or_historical_suites_executed=False,author_cli_rejection_paths_only=True,
   uniform_degree_certification='Separate independent mathematical review; this checker authenticates current degree metadata without claiming its proof.',
   public_contract='Bounded pinned CLI, not a maintained callable build/checked/evaluate API.'),counts=dict(sorted(counts.items())),local_coefficient_checks=local,forms=records)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.artifacts)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed independent saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts']),sort_keys=True))
if __name__=='__main__':main()

