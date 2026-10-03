#!/usr/bin/env python3
"""Independent all-16 U9 saved-source tail-shift audit; standard library only.
The generic ledger, affine RingDAG and polynomial routines are copied from
pinned prior independent reviewer 723ca1ac; its verify/API tests are not called.
"""
import argparse,ast,copy,hashlib,json,random
from pathlib import Path
from fractions import Fraction
from collections import Counter
if not __debug__:raise RuntimeError('run without -O')
PINS={'../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
 '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90',
 'binary_tag_parameterized_compressed_compiler.py': '13da39c3292f8e19f7881f4543fa704c42edec12f29bd10b06f2df555385c0df',
 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27',
 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a',
 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610',
 'native_binary_positive_scale.md': 'd958feffa5d82ede3096d8c792fbf861385f2c7c011057c587663ead4ad2ce97',
 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c',
 'neary_woods_universal_history_scale257.md': 'dcc467b4b00a013c315856a271307459b694b69d4bd2a66c925312a042247e42',
 'neary_woods_universal_history_units260.md': '73d3787dcc10acc037f80699ec3f8bde1fb721613abac5ce489762aab339057c',
 'neary_woods_universal_initial_bound254.md': '9e1a0fd5559dc72420a5123eb4f67753576f7b06d93aff6b7b650cd40dba1f90',
 'neary_woods_universal_joint_and_coupled.md': '02333114dd0cc4396d0a82098e71fde02cc76654c5b5751041f1237732d77868',
 'neary_woods_universal_native_bound254.md': '93b723d6cbbe42e07a9e57979105cffa08f332f4e8d028e5b0aa34890e189952',
 'neary_woods_universal_product_scale253.json': 'a32b58aee2baf3d6d1a66489784f9cc9f5ab2bac296b9a7eb0a116785a3eef1b',
 'neary_woods_universal_product_scale253.md': '9b3b0566dd1365d9acf4b97b6b290b951d56eb51392e85e48f06f83b1604434f',
 'neary_woods_universal_product_scale253.py': 'eb3e8f41f79f69199bd7b620a2b8908e60915b3976898def9d59c25d92a4675e',
 'neary_woods_universal_u9_tag_chain.json': 'b4d78b1be42f6e8c16180311ce371c486d75f9de646b4d78edaf0bcd2491b727',
 'neary_woods_universal_u9_tag_chain.py': '36794dccbad7de48eebcc10ff95311a451205828b1e13f2e2415997246b5d1b8'}

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

def smadd(a,b,s=1):
 r=dict(a)
 for k,v in b.items():r[k]=r.get(k,0)+s*v
 return{k:v for k,v in r.items()if v}

def smmul(a,b):
 r={}
 for u,x in a.items():
  for v,y in b.items():
   k=tuple(i+j for i,j in zip(u,v));r[k]=r.get(k,0)+x*y
 return{k:v for k,v in r.items()if v}

def scalar(n):return{(0,0,0,0):n}if n else{}

def main_identity():
 X,a,c,g=[{tuple(int(j==i)for j in range(4)):1}for i in range(4)];ac=smmul(a,c);H=smadd(smmul(scalar(4),a),scalar(3));Delta=smadd(smmul(a,a),H);d=smadd(smadd(X,ac),g)
 original=smadd(smmul(d,d),smmul(Delta,smmul(c,c)),-1);u=smadd(X,g);new=smadd(smmul(u,smadd(smmul(scalar(2),ac),u)),smmul(H,smmul(c,c)),-1)
 need(original==new,'independent exact main factorization (X+gamma)*(2ac+X+gamma)-Hc²')
 return len(original)

def full_coefficients(p,weights,prime,constants):
 def trim(v):
  while len(v)>1 and v[-1]==0:v.pop()
  return v
 def add(a,b,sgn=1):
  n=max(len(a),len(b));r=[0]*n
  for i,v in enumerate(a):r[i]=v
  for i,v in enumerate(b):r[i]=(r[i]+sgn*v)%prime
  return trim(r)
 def mul(a,b):
  if len(a)>len(b):a,b=b,a
  r=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   if x:
    for j,y in enumerate(b):r[i+j]+=x*y
  return trim([x%prime for x in r])
 e={n:[0,w%prime]for n,w in weights.items()};e.update({n:[v%prime]for n,v in constants.items()})
 for n,o,a,b in p['source']:
  a=e[a]if type(a)is str else[a%prime];b=e[b]if type(b)is str else[b%prime];e[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else -1)
 return e

FIXED=['history_radix','lower_constant','lower_difference','production_offset','recoder_radix','repunit_divisor','terminal_offset','terminal_scale','upper_constant','upper_difference','upper_offset']

def normal_rows(rows):
 def at(x):
  if type(x)is dict:
   need(set(x)=={'fixed_numeral'}and type(x['fixed_numeral'])is str and x['fixed_numeral']in FIXED,'exact named compiler numeral leaf')
   return '@fixed:'+x['fixed_numeral']
  need(type(x)in(str,int),'exact gate operand type');return x
 return[[n,o,at(a),at(b)]for n,o,a,b in rows]

def independent_child(old):
 rows=copy.deepcopy(old['source']);idx=next(i for i,r in enumerate(rows)if r[0]=='and__bs_X_bound')
 need(rows[idx]==['and__bs_X_bound','+','factored_pack_inner','and__bound_beta'],'literal old beta shift')
 rows[idx]=['and__bs_X_bound','+','factored_pack_Z','and__bound_beta'];return rows

PINS.update({
 'review_neary_woods_tail_quotient_source.py':'723ca1ac99468efa8821b322b812c95b9430cf7861247a5f58390e656782b36e',
 'review_neary_woods_tail_quotient_math.py':'c2d8d1c5dfaa7e8dba42fa579e22f8b7f591ad3e27faf0ac73a02e79dc36c22b',
 'review_neary_woods_tail_quotient_math.json':'a4628a89462a1073be7c50c4aa5b119c66e80b7e5cdb6803be19c16c6839e8f3',
 'review_neary_woods_tail_quotient_math.md':'4efffe5d793992c4e2fc3dc9112482cda55780ab7746b2d5e98d0b3275eedda5'})
EXPECTED_COST=[259,256,258,255,258,255,257,253]
EXPECTED_DEG=[795,802,837,848,957,964,975,982]
EXPECTED_M=[132,131,133,132,133,132,134,132]

def stable(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def digest(v):return sha(stable(v).encode())
def ancestors(rows,ports):
 D={n:(a,b)for n,o,a,b in rows};done=set();todo=list(ports)
 while todo:
  n=todo.pop()
  if type(n)is str and n not in done:
   done.add(n);todo.extend(D.get(n,()))
 return done

def whole_finalizer(rows,out,factors,residuals):
 # Small exact coefficient ring in formal factor/residual atoms, independently
 # derived from every literal tail row. It is a proof for all scalar values.
 n=len(factors)+len(residuals);zero=(0,)*n
 def C(v):return {zero:v}if v else{}
 def V(i):return {tuple(int(i==j)for j in range(n)):1}
 env={f:V(i)for i,f in enumerate(factors)}
 env.update({r:V(len(factors)+i)for i,r in enumerate(residuals)})
 for name,op,a,b in rows:
  if name in env:continue
  if not all(type(v)is int or type(v)is str and v in env for v in(a,b)):continue
  aa=C(a)if type(a)is int else env[a];bb=C(b)if type(b)is int else env[b]
  env[name]=smmul(aa,bb)if op=='*'else smadd(aa,bb,1 if op=='+'else -1)
 product=C(1)
 for i in range(len(factors)):product=smmul(product,V(i))
 sos=C(1)
 for i in range(len(residuals)):sos=smadd(sos,smmul(V(len(factors)+i),V(len(factors)+i)))
 expected=smadd(smmul(product,sos),C(1),-1)
 need(env[out]==expected,'literal complete anchored SOS/product polynomial')
 return len(expected)

def degrees_and_shape(rows,free,fixed,old):
 D={n:(o,a,b)for n,o,a,b in rows};d={n:1 for n in free};d.update({n:0 for n in fixed})
 norms=old['ledger']['normalized_prefixes'];scales=old['ledger']['positive_scale_prefixes']
 req={'and__bs_X_bound':('+','factored_pack_Z','and__bound_beta'),
 'and__wn2':('*','and__bs_X_bound','and__q'),
 'factored_pack_q_minus_one':('-','and__q',1),'factored_pack_q_plus_one':('+','and__q',1),
 'factored_pack_Z':('*','factored_pack_q_minus_one','and__F3'),
 'factored_pack_B':('+','and__padded_B','factored_pack_Z'),
 'factored_pack_scaled_B':('*','factored_pack_q_plus_one','factored_pack_B'),
 'factored_pack_inner':('+','factored_pack_A_plus_one','factored_pack_scaled_B'),
 'and__bs_packed':('*','factored_pack_q_minus_one','factored_pack_inner')}
 for pref in ('geo__','and__'):
  X,a,c,G,H=[pref+x for x in ('wn2','R12','R10a','gam','a4m5')]
  req.update({pref+'R15':('-',pref+'L15',pref+'Ac2'),pref+'L15':('*',pref+'R14',pref+'R14'),
    pref+'R14':('+',pref+'D1',G),pref+'D1':('+',X,pref+'cam2'),pref+'cam2':('*',c,a),
    pref+'A':('+',pref+'a_square',H),pref+'a_square':('*',a,a),H:('+',pref+'a4',3),
    pref+'a4':('*',4,a),G:('*',pref+'ga',H),pref+'Ac2':('*',pref+'A',pref+'c2'),pref+'c2':('*',c,c),
    pref+'ic2':('*',pref+'i',pref+'c2'),pref+'ic22':('*',pref+'ic2',pref+'ic2'),
    pref+'L16':('*',pref+'f',pref+'f'),pref+'of':('*',pref+'o',pref+'f'),
    pref+'aux_u_rhs':('-',pref+'of',c),pref+'H2':('*',pref+'aux_u_rhs',pref+'aux_u_rhs'),
    pref+'aux_y2':('*',pref+'y_aux',pref+'y_aux'),pref+'aux_square_gap':('-',pref+'H2',pref+'aux_y2'),
    pref+'L17':('*',pref+'R16',pref+'aux_square_gap'),pref+'P17':('+',pref+'L17',pref+'aux_y2'),
    pref+'gap_square':('*',pref+'tau_gap',pref+'tau_gap'),pref+'signed_gap':('-',pref+'tau_gap',pref+'R10b'),
    pref+'root_base':('*',pref+'UM',pref+'ksn2'),pref+'gap_cross':('*',pref+'root_base',pref+'signed_gap'),
    pref+'four_cross':('*',4,pref+'gap_cross'),pref+'first_unit':('+',pref+'gap_square',pref+'four_cross'),
    pref+'R10b':('+',pref+'eta',pref+'zeta'),pref+'UM':('*',X,pref+'sn2'),
    a:('+',pref+'UM',pref+'sn2'),pref+'ksn2':('*',pref+'R10b',pref+'sn2'),c:('+',pref+'ksn2',pref+'eta')})
  if pref in norms:
   req.update({pref+'normalized_strong_Q':('*',pref+'A',pref+'ic22'),
    pref+'f_square_minus_one':('-',pref+'L16',pref+'normalized_strong_Q'),pref+'R16':('*',pref+'A',pref+'normalized_strong_Q')})
  else:req.update({pref+'f_square_minus_one':('-',pref+'L16',1),pref+'R16':('*',pref+'A',pref+'f_square_minus_one')})
 need(all(D.get(n)==v for n,v in req.items()),'literal main/first/ordinary/normalized strong/auxiliary identities')
 for n,o,a,b in rows:
  da=d[a]if type(a)is str else 0;db=d[b]if type(b)is str else 0
  if n in ('geo__R15','and__R15'):
   pref=n[:-3];X,a,c,G,H=[d[pref+x]for x in('wn2','R12','R10a','gam','a4m5')]
   u=max(X,G);d[n]=max(u+max(a+c,u),H+2*c)
  else:d[n]=da+db if o=='*'else max(da,db)
 need([d['and__'+n]for n in('q','F3','wn2','R12','R10a')]==[15,14,44,60,17],'actual tail scale interface')
 need([d['geo__'+n]for n in('wn2','R12','R10a')]==([3,5,3]if 'geo__'in scales else[2,4,3]),'actual geometry scale interface')
 factors=list(old['ledger']['degree']['factor_degree_bounds'])
 res=[n for n,o,a,b in rows if n.startswith('loader_residual_')]
 for pref in ('geo__','and__'):
  if pref in norms:need(pref+'f_square_minus_one'in factors,'normalized strong is full product unit')
  else:need(any(D[r]==('-',pref+'ic22',pref+'R16')for r in res),'ordinary strong retained as squared equation')
 if 'geo__'not in scales:need(any(D[r]==('-','geo__geometry_X_bound','geo__wn2')for r in res),'unprojected geometry equation retained')
 # Uniform nonvanishing native leader templates. Their actual upstream a,c
 # leaders are nonzero for positive fixed radix coefficients; g,k,ga,i,f,h
 # have the private supplied coordinates indicated in the companion proof.
 cert=[]
 for pref in ('geo__','and__'):
  da=d[pref+'R12'];dc=d[pref+'R10a'];norm=pref in norms
  values={pref+'R15':1+2*da+dc,pref+'first_unit':1+da+dc,
    pref+'P17':4*da+2+6*dc if norm else 2*da+2+2*dc,
    pref+'index_unit':1+da,pref+'linear_unit':1+da}
  if norm:values[pref+'f_square_minus_one']=2*da+2+4*dc
  need(all(d[n]==v for n,v in values.items()),'uniform native leader degree formula')
  for r in res:
   if D[r]==('-',pref+'ic22',pref+'R16'):
    lhs=2+4*dc;rhs=2*da+2;need(lhs!=rhs and d[r]==max(lhs,rhs),'unique ordinary strong leading term')
    cert.append(dict(port=r,leader='i²c*⁴'if lhs>rhs else '−a*²f²',degree=d[r]))
 return d,factors,res,cert,len(req)


def run_parent_audit(blobs):
 parents=json.loads(blobs['neary_woods_universal_product_scale253.json'])['canonical_sources']
 need(len(parents)==16,'eight bases times two interfaces')
 tree=ast.parse(blobs['binary_tag_parameterized_compressed_compiler.py']);recipes=[ast.literal_eval(n.value)for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='NUMERALS'for t in n.targets)]
 need(len(recipes)==1 and sorted(recipes[0])==FIXED,'eleven compiler numeral recipe names')
 u9=json.loads(blobs['neary_woods_universal_u9_tag_chain.json'])['fixed_recipe']
 fixed=['@fixed:'+n for n in FIXED];rng=random.Random(2531616);counts=Counter();forms=[]
 counts['main_identity_terms']=main_identity()
 for idx,old in enumerate(parents):
  child=independent_child(old);rows=normal_rows(child);orig=normal_rows(old['source']);free=old['parameters']+old['auxiliaries']
  need(old['ledger']['bound_is_program_E']==(idx>=8),'actual interface order')
  need(old['parameters']==['x','program_A','program_B','program_T','program_E']+([]if idx>=8 else['program_bound']),'ordinary input and actual program interface')
  need(set(v['fixed_numeral']for row in child for v in row[2:]if type(v)is dict)==set(FIXED),'every named fixed port retained')
  need([n for n,o,a,b in orig if 'and__bound_beta'in(a,b)]==['and__bs_X_bound'],'only changed witness consumer')
  need([n for n,o,a,b in orig if 'and__bs_X_bound'in(a,b)]==['and__wn2'],'only shifted quotient consumer')
  need('and__bound_beta'not in ancestors(orig,['factored_pack_Z','factored_pack_inner']),'offsets do not depend on changed coordinate')
  R=RingDAG();new=R.run(rows,free+fixed);pull=R.add(R.add(R.val('and__bound_beta'),new['factored_pack_Z']),new['factored_pack_inner'],-1);oldrun=R.run(orig,free+fixed,{'and__bound_beta':pull})
  need(all(new[n]==oldrun[n]for n,o,a,b in rows),'entire source graph under signed affine substitution')
  need(new[old['output']]==oldrun[old['output']],'complete polynomial pullback')
  counts['all_register_identities']+=len(rows)
  M,A,naive=ledger(rows,free+fixed,[old['output']],fixed)
  need([M,A,M+A]==[EXPECTED_M[idx%8],EXPECTED_COST[idx%8]-EXPECTED_M[idx%8],EXPECTED_COST[idx%8]],'independent paid source totals')
  need(old['ledger']['polynomial']['operations']==M+A and old['ledger']['polynomial']['multiplications']==M,'unchanged immediate parent paid ledger')
  d,factors,res,leaders,shapechecks=degrees_and_shape(rows,free,fixed,old)
  counts['literal_shape_premises']+=shapechecks
  counts['formal_finalizer_terms']+=whole_finalizer(rows,old['output'],factors,res)
  need(d[old['output']]==EXPECTED_DEG[idx%8],'complete upper bound')
  need(d[old['output']]==sum(d[n]for n in factors)+2*max([d[n]for n in res],default=0),'actual product/SOS degree formula')
  # Diagnostic complete expansion supplies a lower bound at a deliberately
  # non-compiler specialization; uniform validity of the upper bound above
  # does not rely on this coefficient test or a valid huge Pell tuple.
  constants={n:2+j for j,n in enumerate(fixed)};weights={n:2+rng.randrange(1,17)for n in free}
  for pref in ('geo__','and__'):weights[pref+'tau_gap']=weights[pref+'eta']+weights[pref+'zeta']+1
  e=full_coefficients({'source':rows},weights,1000000007,constants)
  need(len(e[old['output']])-1==d[old['output']],'full coefficient expansion reaches bound on symbolic-program diagnostic')
  need(all(len(e[n])-1==d[n]for n in factors+res),'all actual factor/residual diagnostic degrees')
  for j in range(4):
   rational=j==3;v={n:Fraction(rng.randrange(-3,5),rng.randrange(1,5))if rational else rng.randrange(-3,5)for n in free};v.update(constants)
   ne=numeric(rows,v);pv=dict(v);pv['and__bound_beta']=v['and__bound_beta']+ne['factored_pack_Z']-ne['factored_pack_inner'];oe=numeric(orig,pv)
   need(all(oe[n]==ne[n]for n,o,a,b in rows),'whole signed/rational source pullback diagnostic')
   counts['numeric_cases']+=1;counts['rational_cases']+=int(rational)
  counts['complete_sources']+=1;counts['paid_live_gates']+=len(rows);counts['factor_ports']+=len(factors);counts['ordinary_rows']+=len(res);counts['full_expansions']+=1
  forms.append(dict(index=idx,merged=idx>=8,normalized=old['ledger']['normalized_prefixes'],positive_scales=old['ledger']['positive_scale_prefixes'],operations=M+A,M=M,A=A,witnesses=len(old['auxiliaries']),parameters=len(old['parameters']),source_sha256=digest(child),output=old['output'],gate_degree_bound=naive,degree_upper=d[old['output']],factor_bounds={n:d[n]for n in factors},residual_bounds={n:d[n]for n in res},ordinary_leader_certificates=leaders,coefficient_diagnostic=dict(prime=1000000007,degree=len(e[old['output']])-1,coefficient_sha256=digest(e[old['output']]))))
 return parents,forms,dict(counts),recipes[0],u9

PINS.update({
 'neary_woods_universal_tail_quotient253.py':'291b3e22c7d1f8db99cb55c3f2e3bc6e83f92e377d44028bf8e56f1c39d7cf50',
 'neary_woods_universal_tail_quotient253.json':'48d604caf52af6cc6e37f77614787b1a02a549b03c1f5acdb53a5a7277c7504f',
 'neary_woods_universal_tail_quotient253.md':'328b9a3d62a989f78cd3c7b388eba01800a9d92e7cb8df6ac58184df9982653b'})
AUTHOR={
 'neary_woods_tail_quotient_all16.py':'0ed907103449c2fea80113ef39c407531c4350c8e8207a888c23f5a299f664b9',
 'neary_woods_tail_quotient_all16.json':'13282605960e782b2389042f2ebd6ce12f3961c8c48e579a86739bc1e77ee6da',
 'neary_woods_tail_quotient_all16.md':'c0cb462011e78cbb879ca64300f48d3dfb25241de66b0de08dcc5d9d1d7f47e4'}

def literal_assignment(blob,name):
 T=ast.parse(blob);v=[ast.literal_eval(n.value)for n in T.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id==name for t in n.targets)]
 need(len(v)==1,'one literal source assignment '+name);return v[0]

def compare_saved(parents,forms,saved,recipes,u9,blobs):
 need(len(saved['forms'])==16,'author sixteen actual saved complete forms')
 pair=json.loads(blobs['neary_woods_universal_tail_quotient253.json']);overlap={f['packet']['saved_parent_index']:f['packet']['source']for f in pair['forms']}
 paidcores=0;certpaid=0
 for i,(old,r,p)in enumerate(zip(parents,forms,saved['forms'])):
  rows=independent_child(old);D={n:(o,a,b)for n,o,a,b in rows};factors=list(r['factor_bounds']);res=list(r['residual_bounds']);ordinary=[[D[n][1],D[n][2]]for n in res]
  need(p['saved_parent_index']==i and exact(p['source'],rows),'every literal child source independently reconstructed')
  need(p['parameters']==old['parameters']and p['auxiliaries']==old['auxiliaries']and p['output']==old['output'],'complete coordinate/output conservation')
  need(exact(p['fixed_numeral_recipes'],recipes)and exact(p['fixed_u9_recipe'],u9),'exact eleven numeral recipes and concrete fixed U9 interface')
  need(exact(p['historical_parent_ledger'],old['ledger']),'historical metadata conserved and named historical')
  need(p['source_sha256']==digest(rows),'literal saved source digest')
  first=next(j for j,row in enumerate(rows)if row[0].startswith('loader_residual_')or row[0]=='lower_unit_output')
  inv=dict(native_base=i%8,merged_duration=i>=8,normalized_prefixes=r['normalized'],positive_scale_prefixes=r['positive_scales'],factor_ports=factors,ordinary_comparisons=ordinary,comparisons=[['lower_history_product',1]]+ordinary,certificate_boundary=first,finalizer_source=rows[first:],finalizer_formula='product(factors)*(1+sum(ordinary_residual^2))-1')
  need(exact(p['inventory'],inv),'all actual comparison/finalizer inventory metadata')
  roots=factors+[v for ab in ordinary for v in ab];live=ancestors(normal_rows(rows),roots);core=[row for row in rows if row[0]in live];cm=sum(row[1]=='*'for row in core)
  coreled=dict(operations=len(core),M=cm,A=len(core)-cm,scope='dependency closure of all factors and ordinary operand ports; excludes grouping and finalizer')
  need(exact(p['core_source'],core)and exact(p['core_ledger'],coreled),'actual full core closure and paid count')
  need(len(core)==235+len(r['normalized'])and len(core)-cm==120,'eight actual shared core variants')
  led=dict(operations=r['operations'],M=r['M'],A=r['A'],all_gates_live=True,witnesses=r['witnesses'],supplied_parameters=r['parameters'],fixed_numeral_roles=11,certificate_operations=first,certificate_M=sum(row[1]=='*'for row in rows[:first]),certificate_A=sum(row[1]!='*'for row in rows[:first]),comparisons=1+len(res),finalizer_operations=len(rows)-first)
  need(exact(p['ledger'],led),'every active complete/certificate/finalizer ledger')
  deg=dict(degree_upper_bound=r['degree_upper'],exact_degree_claimed=False,factor_degree_bounds=r['factor_bounds'],ordinary_residual_degree_bounds=list(r['residual_bounds'].values()),anchor_degree_bound=sum(r['factor_bounds'].values()),SOS_degree_bound=2*max(list(r['residual_bounds'].values()),default=0),supplied_coordinate_degree=1,fixed_numeral_degree=0)
  need(exact(p['degree'],deg),'full active upper-degree metadata')
  need(p['signed_pullback']=='beta_parent=beta_child+factored_pack_Z-factored_pack_inner','actual signed coordinate map')
  need(p['positive_zero_bijection_scope']=='same valid shifted U9 program/input slice; inverse positive after native recovery; beta only','positive theorem scope')
  need(p['domains']=={'parameters':'positive; program coefficients fixed on inherited valid shifted U9 slices','auxiliaries':'strictly positive'},'supplied domain scope')
  oldrow=['and__bs_X_bound','+','factored_pack_inner','and__bound_beta'];newrow=['and__bs_X_bound','+','factored_pack_Z','and__bound_beta']
  proof=dict(changed_rows=[[oldrow,newrow]],whole_register_identities=len(rows),factor_identities=len(factors),comparison_identities=len(ordinary)+1,full_signed_graph_identity=True,same_coordinate_polynomial_identity=False)
  need(exact(p['whole_graph_proof'],proof),'truthful graph proof metadata')
  free=old['parameters']+old['auxiliaries'];v={n:1 for n in free+['@fixed:'+n for n in FIXED]};env=numeric(normal_rows(rows),v);beta=1+env['factored_pack_Z']-env['factored_pack_inner']
  need(p['offzero_inverse_beta']==beta<0 and env[old['output']]!=0,'negative inverse only at an off-zero diagnostic')
  if i in overlap:need(exact(rows,overlap[i]),'two original frozen layouts unchanged')
  paidcores+=len(core);certpaid+=first
 for i in range(8):
  a,b=saved['forms'][i],saved['forms'][i+8]
  need(a['source'][1:]==b['source'][1:]and a['source'][0]==['program_duration_bound','+','program_bound','program_duration_gap']and b['source'][0]==['program_duration_bound','+','program_E','program_duration_gap'],'exact two-interface distinction')
 return dict(core_gates=paidcores,certificate_gates=certpaid,checked_full_source_records=16,overlap_sources=2,interface_pairs=8)

def verify(root,artifacts):
 blobs=pins(root,PINS);author=pins(artifacts,AUTHOR);saved=json.loads(author['neary_woods_tail_quotient_all16.json'])
 need(saved['source_sha256']==AUTHOR['neary_woods_tail_quotient_all16.py'],'author source receipt pin')
 ap=literal_assignment(author['neary_woods_tail_quotient_all16.py'],'PINS')
 need(exact(ap,saved['pins'])and all(PINS.get(n)==h for n,h in ap.items()),'author dependencies independently authenticated')
 parents,forms,counts,recipes,u9=run_parent_audit(blobs)
 extra=compare_saved(parents,forms,saved,recipes,u9,blobs);counts.update(extra)
 expected=dict(whole_register_identities=4102,factor_identities=240,comparison_identities=40,complete_forms=16,numeric_full_identities=192,numeric_finalizers=192,rational_cases=32,negative_offzero_inverse_cases=16,frozen_overlap_matches=2)
 need(exact(saved['counts'],expected),'author receipt counters distinguished from independent checks')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),author_pins=copy.deepcopy(AUTHOR),counts=counts,forms=forms,scope='Sixteen actual complete source schedules = eight eligible native bases times two duration interfaces. Full all-value signed graph identities and paid upper-degree ledgers; no author/historical Python executes, no partition census or maintained API audit. Diagnostic lower-degree witnesses are not exact degree assertions on fixed program slices. Positive-zero theorem inherited from pinned all16 math review.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.artifacts)
 need(exact(r,json.loads(json.dumps(r))),'exact JSON type roundtrip')
 if a.expect:need(exact(r,json.loads(a.expect.read_bytes())),'fresh exact saved independent receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'])))
if __name__=='__main__':main()
