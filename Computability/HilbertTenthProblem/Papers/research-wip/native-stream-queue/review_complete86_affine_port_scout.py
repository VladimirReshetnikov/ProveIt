"""Independent finite grammar, paid source and cut-congruence review."""
import argparse,ast,hashlib,itertools,json,random,sys,subprocess,tempfile
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
SUBJECT={'complete86_affine_port_scout.py':'5abbc4ee9b44f83bf9d96b0e54f6d4ebe6c1fd461637fdd915ae71465a867e2c','complete86_affine_port_scout.json':'114301fbfdb40857b7e139a4ffa132c64b45a5f56d000b6d15a8893c57e5c7c1','complete86_affine_port_scout.md':'295dc976c0cffb71fe17be53c6bd541431fc7bb4d43a2f81e9f61c426b3cc558'}
def need(v,msg):
 if not v:raise ValueError(msg)
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
 if type(a)in(tuple,list):return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def digest(x):return sha(json.dumps(x,sort_keys=True,separators=(',',':')).encode())
def authenticated(root,pins):
 out={}
 for name,pin in pins.items():
  b=(Path(root)/name).read_bytes();need(sha(b)==pin,'Pinned bytes '+name);out[name]=b
 return out

class Algebra:
 def __init__(self):self.nodes=[];self.index={};self.fingerprints=[]
 def intern(self,node):
  if node not in self.index:
   n=len(self.nodes);self.index[node]=n;self.nodes.append(node)
   fp=digest(node)if node[0]in('var','int')else digest([node[0],self.fingerprints[node[1]],self.fingerprints[node[2]]]);self.fingerprints.append(fp)
  return self.index[node]
 def leaf(self,v):
  need(type(v)in(int,str),'Exact leaf');return self.intern(('int'if type(v)is int else'var',v))
 def op(self,o,a,b):
  aa,bb=self.nodes[a],self.nodes[b]
  if aa[0]==bb[0]=='int':return self.leaf(aa[1]+bb[1]if o=='+'else aa[1]-bb[1]if o=='-'else aa[1]*bb[1])
  if o=='+':
   if aa==('int',0):return b
   if bb==('int',0):return a
  elif o=='-':
   if a==b:return self.leaf(0)
   if bb==('int',0):return a
  else:
   if aa==('int',0)or bb==('int',0):return self.leaf(0)
   if aa==('int',1):return b
   if bb==('int',1):return a
  if o in('+','*')and self.fingerprints[a]>self.fingerprints[b]:a,b=b,a
  return self.intern((o,a,b))
 def parse(self,rows):
  env={}
  for n,o,a,b in rows:
   need(n not in env and o in('+','-','*'),'Literal row')
   env[n]=self.op(o,env.get(a,self.leaf(a)),env.get(b,self.leaf(b)))
  return env
 def walk(self,out):
  seen=set();stack=[out]
  while stack:
   n=stack.pop()
   if n in seen:continue
   seen.add(n);t=self.nodes[n]
   if t[0]in('+','-','*'):stack.extend(t[1:])
  return seen
 def replace(self,out,mapping):
  @lru_cache(None)
  def rec(n):
   if n in mapping:return rec(mapping[n])
   row=self.nodes[n]
   return self.op(row[0],rec(row[1]),rec(row[2]))if row[0]in('+','-','*')else n
  return rec(out)
 def emit(self,out):
  names={};rows=[];free=set()
  def rec(n):
   if n in names:return names[n]
   t=self.nodes[n]
   if t[0]in('var','int'):
    if t[0]=='var':free.add(t[1])
    return t[1]
   a,b=rec(t[1]),rec(t[2]);name='ind_'+str(len(rows));rows.append([name,t[0],a,b]);names[n]=name;return name
  final=rec(out);M=sum(r[1]=='*'for r in rows)
  return dict(source=rows,output=final,free_ports=sorted(free),M=M,A=len(rows)-M,operations=len(rows))
 def prove(self,left,right,cuts):
  # First test the stronger identity treating proposed cuts independently.
  # If overlap prevents that identity, expand dependent cuts and retry.
  cuts=set(cuts)
  choices=[cuts,{n for n in cuts if not((self.walk(n)-{n})&cuts)}]
  for boundary in choices:
   memo={}
   def poly(n):
    if n in memo:return memo[n]
    t=self.nodes[n]
    if t[0]=='int':p={():t[1]}if t[1]else{}
    elif n in boundary or t[0]=='var':p={(n,):1}
    else:
     a,b=poly(t[1]),poly(t[2]);p={}
     if t[0]=='*':
      for ma,va in a.items():
       for mb,vb in b.items():m=tuple(sorted(ma+mb));p[m]=p.get(m,0)+va*vb
     else:
      p=dict(a)
      for m,v in b.items():p[m]=p.get(m,0)+(v if t[0]=='+'else-v)
     p={m:v for m,v in p.items()if v}
    memo[n]=p;return p
   if poly(left)==poly(right):return len(poly(left))
  raise ValueError('Independent exact cut coefficient identity')


def candidates(g,out):
 one=g.leaf(1)
 for node in sorted(g.walk(out)):
  t=g.nodes[node]
  if t[0]not in('+','-','*'):continue
  o,a,b=t;aa,bb=g.nodes[a],g.nodes[b]
  if o in('+','-'):
   sign=1 if o=='+'else-1;triples=[]
   if aa[0]in('+','-'):triples.append(((aa[1],1),(aa[2],1 if aa[0]=='+'else-1),(b,sign)))
   if bb[0]in('+','-'):triples.append(((a,1),(bb[1],sign),(bb[2],sign if bb[0]=='+'else-sign)))
   for terms in triples:
    for order in itertools.permutations(terms):
     if order[0][1]!=1:continue
     (x,_),(y,ys),(z,zs)=order
     for new in(g.op('+'if zs==1 else'-',g.op('+'if ys==1 else'-',x,y),z),g.op('+'if ys==1 else'-',x,g.op('+'if ys*zs==1 else'-',y,z))):
      if new!=node:yield 'addition',node,new,(x,y,z)
   left=[(aa[1],aa[2]),(aa[2],aa[1])]if aa[0]=='*'else[(a,one)]
   right=[(bb[1],bb[2]),(bb[2],bb[1])]if bb[0]=='*'else[(b,one)]
   for f,x in left:
    for ff,y in right:
     if f==ff:
      new=g.op('*',f,g.op(o,x,y))
      if new!=node:yield 'factor',node,new,(f,x,y)
   if o=='-'and aa[0]=='*'and bb[0]=='*'and aa[1]==aa[2]and bb[1]==bb[2]:
    x,y=aa[1],bb[1];new=g.op('*',g.op('-',x,y),g.op('+',x,y))
    if new!=node:yield 'square_difference',node,new,(x,y)
  else:
   for inner,other in((aa,b),(bb,a)):
    if inner[0]=='*':
     x,y=inner[1:]
     for outer,first,second in((x,y,other),(y,x,other),(other,x,y)):
      new=g.op('*',outer,g.op('*',first,second))
      if new!=node:yield 'product',node,new,(x,y,other)
    if inner[0]in('+','-'):
     x,y=inner[1:];new=g.op(inner[0],g.op('*',x,other),g.op('*',y,other))
     if new!=node:yield 'distribute',node,new,(x,y,other)
   for plus,minus in((aa,bb),(bb,aa)):
    if plus[0]=='+'and minus[0]=='-'and set(plus[1:])==set(minus[1:]):
     x,y=minus[1:];new=g.op('-',g.op('*',x,x),g.op('*',y,y))
     if new!=node:yield 'conjugate',node,new,(x,y)

def validate(p):
 seen=set(p['free_ports']);deps={};M=0
 for n,o,a,b in p['source']:
  need(type(n)is str and n not in seen and o in('+','-','*'),'Paid row')
  need(all(type(v)is int or type(v)is str and v in seen for v in(a,b)),'Closed source')
  seen.add(n);deps[n]=(a,b);M+=o=='*'
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(deps.get(n,()))
 need(set(deps)<=live and set(p['free_ports'])<=live,'All gates and original inputs live')
 need((M,len(p['source'])-M,len(p['source']))==(p['M'],p['A'],p['operations']),'Entire paid ledger')
def evaluate(p,v):
 d=dict(v)
 for n,o,a,b in p['source']:
  a=d[a]if type(a)is str else a;b=d[b]if type(b)is str else b;d[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return d[p['output']]

def verify(root,subject):
 blobs=authenticated(subject,SUBJECT);syntax=ast.parse(blobs['complete86_affine_port_scout.py']);pin_expr=next(n.value for n in syntax.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='PINS'for t in n.targets));pins=ast.literal_eval(pin_expr);deps=authenticated(root,pins)
 saved=json.loads(blobs['complete86_affine_port_scout.json']);need(same(saved['pins'],pins)and saved['source_sha256']==SUBJECT['complete86_affine_port_scout.py'],'Complete subject lineage')
 old=json.loads(deps['complete86_factored_first_root.json'])['forms'][0];g=Algebra();env=g.parse(old['source']);out=env['polynomial'];baseline=g.emit(out);validate(baseline)
 need(old['normalized']is True and(baseline['M'],baseline['A'])==(48,38),'Actual normalized86 baseline')
 need(set(baseline['free_ports'])==set(old['witnesses']+old['ledger']['fixed_numerals']+['x']),'Entire26-port interface')
 h,a,b=env['a4m5'],env['D1'],env['exponent_partial'];rho,sigma=g.leaf('rho'),g.leaf('sigma');u=g.op('*',rho,h);v=g.op('*',sigma,h);w=g.op('*',g.op('+',rho,sigma),h);mu=g.op('+',b,u)
 roots=[('original',g.op('+',a,w),mu),('distributed_left',g.op('+',g.op('+',a,u),v),mu),('distributed_right',g.op('+',a,g.op('+',u,v)),mu),('through_input_left',g.op('+',g.op('+',mu,g.op('-',a,b)),v),mu),('through_input_right',g.op('+',mu,g.op('+',g.op('-',a,b),v)),mu),('recover_rho_product',g.op('+',a,w),g.op('+',b,g.op('-',w,v)))]
 raw=0;cut_proofs=0;allout={};records=[];counts=dict(seed_root_coefficients=0,complete_source_recounts=0,paid_gates=0,supplemental_full_outputs=0,saved_full_sources=0)
 rng=random.Random(260409);assignments=[]
 for case in range(3):
  q={n:rng.randint(1,4)for n in baseline['free_ports']};q.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19)
  if case==1:q={n:x*(-1 if i%2 else 1)for i,(n,x)in enumerate(q.items())}
  if case==2:q={n:Fraction(x,3)for n,x in q.items()}
  assignments.append(q)
 expected=[evaluate(baseline,q)for q in assignments]
 for name,main,inputroot in roots:
  for left,right in((env['R14'],main),(env['exponent_rhs'],inputroot)):g.prove(left,right,(a,b,h,rho,sigma));counts['seed_root_coefficients']+=1
  seed=g.replace(out,{n:r for n,r in((env['R14'],main),(env['exponent_rhs'],inputroot))if n!=r});need(g.parse(next(x['packet']for x in saved['seeds']if x['name']==name)['source'])[next(x['packet']['output']for x in saved['seeds']if x['name']==name)]==seed,'Authenticated complete seed DAG')
  forms={seed};raw_here=0
  for kind,node,replacement,cuts in list(candidates(g,seed)):
   raw_here+=1;g.prove(node,replacement,cuts);cut_proofs+=1;forms.add(g.replace(seed,{node:replacement}))
  histogram=Counter()
  for candidate in forms:
   p=g.emit(candidate);validate(p);need(p['free_ports']==baseline['free_ports'],'Complete coordinate set unchanged');histogram[str(p['operations'])]+=1;allout[candidate]=p
   for q,value in zip(assignments,expected):need(evaluate(p,q)==value,'Independent full signed/rational evaluation');counts['supplemental_full_outputs']+=1
   counts['complete_source_recounts']+=1;counts['paid_gates']+=p['operations']
  record=dict(seed=name,distinct_complete_sources=len(forms),cost_histogram=dict(sorted(histogram.items())),raw_moves=raw_here);author=next(x for x in saved['census']if x['seed']==name)
  need(record['distinct_complete_sources']==author['distinct_complete_sources']and record['cost_histogram']==author['cost_histogram'],'Independent full census agrees');records.append(record);raw+=raw_here
 need(len(allout)==saved['distinct_complete_sources_across_seeds']==874 and raw==saved['raw_generated_moves']==1300,'Complete union/raw counts')
 best=min(p['operations']for p in allout.values());winners=[p for p in allout.values()if p['operations']==best]
 need(best==86 and len(winners)==127 and{(p['M'],p['A'])for p in winners}=={(48,38)},'Exact bounded minimum/127winners')
 # Independently authenticate every saved emitted packet as a full member,
 # including the separate exact gap rebracketing.
 packets=[x['packet']for x in saved['seeds']]+[saved['one_best_complete_source']]
 for p in packets:
  validate(p);need(g.parse(p['source'])[p['output']]in allout,'Saved full source belongs to independent family');counts['saved_full_sources']+=1
 gap=g.op('-',g.op('*',env['q'],env['q_minus_F']),g.leaf('Z'));g.prove(env['gap'],gap,(env['repunit'],env['q_minus_F'],g.leaf('Z')));gp=g.replace(out,{env['gap']:gap});published=saved['gap_refactoring']['packet'];validate(published);need(g.parse(published['source'])[published['output']]==gp and published['operations']==86,'Full gap source');counts['saved_full_sources']+=1
 rows={n:[o,a,b]for n,o,a,b in old['source']};need([n for n,o,a,b in old['source']if 'F'in(a,b)]==['q_minus_F']and rows['q_minus_F']==['-','q','F'],'Original F privacy')
 comp=saved['complement_coordinate_unproved'];p=comp['syntactic_packet'];validate(p);replaced=g.replace(out,{env['q_minus_F']:g.leaf('complement_u')});need(g.parse(p['source'])[p['output']]==replaced and p['operations']==85,'Literal complete85 expression')
 # Algebraic pullback must be simultaneous: introduce the new coordinate,
 # expand its signed inverse F=q-u, then prove the private consumer equalsu.
 ff=g.op('-',env['q'],g.leaf('complement_u'));oldconsumer=g.op('-',env['q'],ff);g.prove(oldconsumer,g.leaf('complement_u'),(env['q'],g.leaf('complement_u')))
 inverse=g.replace(out,{g.leaf('F'):ff});g.prove(g.op('-',env['q'],ff),g.leaf('complement_u'),(env['q'],g.leaf('complement_u')))
 # Full congruence identity by a proved local q-(q-u)=u cut.
 normalized=g.replace(inverse,{oldconsumer:g.leaf('complement_u')});need(normalized==replaced,'Whole complement graph identity after exact private cut')
 bad=comp['positive_offzero_inverse_example'];need(all(type(x)is int and x>0 for x in bad['assignment'].values()),'Actually positive offzero tuple');need(bad['assignment']['Bm1']*bad['assignment']['Jrep']+1-bad['assignment']['complement_u']==bad['restored_F']==-1,'Explicit negative inverse');need(evaluate(p,bad['assignment'])==bad['complete_output']!=0,'Only offzero domain warning');need(comp['not_a_certified_bound']is True,'85 remains unproved in this report');counts['saved_full_sources']+=1
 with tempfile.TemporaryDirectory(prefix='affine_review_pins_')as temp:
  for n,b in blobs.items():(Path(temp)/n).write_bytes(b)
  for n,b in blobs.items():
   (Path(temp)/n).write_bytes(b+b' ')
   try:authenticated(temp,SUBJECT)
   except ValueError:pass
   else:raise AssertionError('Changed subject accepted')
   (Path(temp)/n).write_bytes(b)
 counts['subject_pin_rejections']=3
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'Optimized guard');counts['optimized_rejections']=1
 return dict(status='PASS_INDEPENDENT_COMPLETE86_AFFINE_PORT_SCOUT',review_source_sha256=sha(Path(__file__).read_bytes()),subject_pins=SUBJECT,dependency_pins=pins,counts=counts,census=records,distinct_complete_sources=len(allout),raw_moves=raw,exact_local_occurrence_proofs=cut_proofs,minimum=best,distinct_best_sources=len(winners),best_ledgers=[[48,38,127]],scope='Independent reconstruction of the declared six-seed single-local-move grammar. Exact cut proofs lift to whole outputs by congruence; no unrestricted lower bound, no universal zero materialized. Frozen85 is only a signed-coordinate expression with positive inverse obligation unproved; later obstruction outside this review.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--subject-root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root,a.subject_root)
 if a.expect:need(same(out,json.loads(a.expect.read_text())),'Exact typed review receipt')
 if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print(out['status'],out['counts']);print('census',out['distinct_complete_sources'],out['raw_moves'],out['minimum'])
if __name__=='__main__':main()
