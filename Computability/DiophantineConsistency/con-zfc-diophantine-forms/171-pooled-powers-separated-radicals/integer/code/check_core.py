"""Independent arithmetic checker; imports no construction modules.

Checks literal stage boundaries, all residual identities of the algebraic
steps, exact square-frame membership, and every final quartic coefficient.
The cofinality and unbounded Pell arguments remain mathematical proofs.
"""
from pathlib import Path
from collections import defaultdict
import argparse,copy,hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def need(ok,msg):
 if not ok:raise ValueError(msg)
def unique_object(pairs):
 result={}
 for key,value in pairs:
  need(key not in result,'duplicate JSON object key: '+key)
  result[key]=value
 return result
def nonfinite_json(value):raise ValueError('nonfinite JSON number: '+value)
def read(path):return json.loads(path.read_text(),object_pairs_hook=unique_object,parse_constant=nonfinite_json)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def P(ts):
 # Validate before forming a dictionary: duplicates must never be overwritten.
 need(type(ts) is list,'polynomial terms must be a JSON array')
 result={};previous=None
 for term in ts:
  need(type(term) is list and len(term)==2,'term must be [integer coefficient, monomial]')
  coef,mon=term
  need(type(coef) is int and coef!=0,'coefficient must be a nonzero integer, not a Boolean')
  need(type(mon) is list,'monomial must be a JSON array')
  need(all(type(i) is int and i>=0 for i in mon),'indices must be nonnegative integers, not Booleans')
  need(mon==sorted(mon),'monomial indices must be sorted')
  key=tuple(mon)
  need(previous is None or previous<key,'terms must have strictly increasing, unique monomials')
  previous=key;result[key]=coef
 return result

def validate_equation(eq,label='equation'):
 need(type(eq) is dict,label+': expected JSON object')
 need(eq.get('domain')=='unrestricted integers',label+': incorrect domain')
 need(eq.get('polynomial')=='sum(square(row) for row in residuals)',label+': incorrect polynomial convention')
 vs=eq.get('variables');rs=eq.get('residuals')
 need(type(vs) is list and len(vs)>0,label+': nonempty variables array required')
 need(type(rs) is list and len(rs)>0,label+': nonempty residual array required')
 names=[]
 for v in vs:
  need(type(v) is dict and type(v.get('name')) is str and bool(v['name']),label+': variable name')
  need(type(v.get('kind')) is str and bool(v['kind']),label+': variable kind')
  names.append(v['name'])
 need(len(set(names))==len(names),label+': duplicate variable names')
 used=set()
 for j,row in enumerate(rs):
  need(type(row) is dict and type(row.get('label')) is str and bool(row['label']),label+': residual label')
  poly=P(row.get('terms'))
  need(bool(poly),label+': empty residual '+str(j))
  for mon in poly:
   need(len(mon)<=2,label+': residual exceeds degree two')
   need(all(i<len(vs) for i in mon),label+': coordinate out of range')
   used.update(mon)
 need(used==set(range(len(vs))),label+': declared coordinates must all occur')
 return {'declared_coordinates':len(vs),'distinct_used_coordinates':len(used)}
def plus(*args):
 r=defaultdict(int)
 for p in args:
  for m,c in p.items():r[m]+=c
 return {m:c for m,c in r.items() if c}
def times(p,q):
 r=defaultdict(int)
 for a,ca in p.items():
  for b,cb in q.items():r[tuple(sorted(a+b))]+=ca*cb
 return {m:c for m,c in r.items() if c}
def k(c,p):return {m:c*x for m,x in p.items() if c*x}
def V(i):return {(i,):1}
def C(c):return {():c} if c else {}
def minus(p,q):return plus(p,k(-1,q))
def pull(p,mp):
 result={}
 for m,c in p.items():
  t=C(c)
  for i in m:t=times(t,mp.get(i,V(i)))
  result=plus(result,t)
 return result
def rows(eq):return [P(r['terms']) for r in eq['residuals']]
def renumber(p,mp):
 r=defaultdict(int)
 for m,c in p.items():r[tuple(sorted(mp[i] for i in m))]+=c
 return {m:c for m,c in r.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def require_rows(actual,expected,label):
 need(len(actual)==len(expected),label+' row count')
 for j,(a,b) in enumerate(zip(actual,expected)):need(a==b,label+' row '+str(j))
def expanded(rs):
 # Independent unordered term-pair collection: coefficient2 for offdiagonals.
 result=defaultdict(int)
 for row in rs:
  ts=list(row.items())
  for j,(m,c) in enumerate(ts):
   result[tuple(sorted(m+m))]+=c*c
   for n,d in ts[j+1:]:result[tuple(sorted(m+n))]+=2*c*d
 return {m:c for m,c in result.items() if c}
def measure(eq):
 rs=rows(eq);ex=expanded(rs)
 return {'variables':len(eq['variables']),'rows':len(rs),'degree':max(map(len,ex)),'monomials':len(ex),'height':max(abs(x) for x in ex.values()),'row_height':max(abs(x) for r in rs for x in r.values())},ex

def check_pools(parent,child,cert,frame):
 old=rows(parent);names={v['name']:i for i,v in enumerate(parent['variables'])};N=lambda s,z=0:plus(V(names[s]),C(z));A=N('shared.A',1);q=plus(k(4,N('radix.odd_square_root_half')),C(1))
 atoms=[P(a['terms']) for a in frame['atoms']];W=N('shared.W');squares=C(2)
 h=P(frame['verified_h_binding']);F=N('crt.growth_majorant_F');t=N('t0')
 atom_expected=[t,plus(F,t),N('x'),N('y'),F,N('choose0.output'),N('crt.encoded.a',-1)]
 atom_expected +=[N('crt.encoded.'+s)for s in ['b','c','d','S','Sp','u','vq']]
 atom_expected +=[N('crt.encoded_index_minus_one'),N('pow1.output'),h,q,plus(q,C(1)),N('self_radix.BH')]
 atom_expected +=[N('pow'+str(i)+'.output')for i in [3,4,5,7,8,9,10,11,12,13,14,15,16,17]]
 need(atoms==atom_expected,'all actual frame atoms and offsets')
 for a in atoms:squares=plus(squares,times(a,a))
 frame_rows=plus(*(k(c,old[i]) for i,c in frame['row_combination']))
 need(frame_rows==minus(W,squares),'exact retained-row square frame')
 need(len(atoms)==34,'square frame atom count')
 need(not(set(i for i,_ in frame['row_combination'])&set(cert['removed_rows'])),'frame uses a deleted pool row')
 need(cert.get('frame_strengthened') is False,'principal must retain original frame')
 for edit in cert['frame_edits']:need(P(edit['old'])==old[edit['row']]==P(edit['new']),'frame unexpectedly changed')
 index={0:N('t0'),2:plus(N('t0'),N('crt.growth_majorant_F')),3:N('crt.encoded.a',-1),5:N('crt.encoded.b'),6:N('crt.encoded.c'),7:N('crt.encoded.d'),8:N('crt.encoded.S'),9:N('y'),10:N('crt.encoded.Sp'),11:N('crt.encoded.u'),12:N('x'),13:N('crt.encoded.vq'),14:N('crt.encoded_index_minus_one'),15:next(P(a['terms'])for a in frame['atoms']if a['label']=='h')}
 expected_groups=[[3,5,7,8,9,10,12,13,15,16,17],[4,11,14]]
 rmrows=set();rmvars=set();newrows=[]
 for gn,g in enumerate(cert['groups']):
  base=plus(q,C(1)) if gn==0 else q;need(P(g['base'])==base and P(g['A'])==A,'pool base')
  need([r['request'] for r in g['requests']]==expected_groups[gn],'pool exact membership')
  need(base in atoms,'base outside frame')
  T=plus(k(2,times(A,base)),k(-1,times(base,base)),C(-1));need(T==P(g['T']),'pool modulus')
  mod=g['modulus_coordinate'];modrow=g['modulus_row'];modexpr=V(mod) if gn==0 else plus(V(mod),k(-2,A),k(2,q),C(1));need(P(g['modulus_expression'])==modexpr,'q modulus affine expression');need(old[modrow] in (minus(modexpr,T),minus(T,modexpr)),'modulus definition')
  H={};S={};sy={};errors={};remainders={};normsum={}
  rmrows.add(modrow);rmvars.add(mod)
  for r in g['requests']:
   m,X,Y,Z=[P(r[s]) for s in ('output','X','Y','Z')];request=r['request'];pair=r['pair'];qi=r['removed_quotient'];jj=r['removed_row']
   need(m==N('pow'+str(request)+'.output'),'output identity')
   need(qi==names['pow'+str(request)+'.quotient'],'quotient identity')
   need(m in atoms and index[pair] in atoms,'output/index outside square frame')
   AY=minus(Z,times(A,Y));need(old[r['retained_AY_row']] in (AY,k(-1,AY)),'A times Y certificate')
   norm=plus(times(X,X),times(Y,Y),k(-1,times(Z,Z)),C(-1));need(old[r['retained_norm_row']] in (norm,k(-1,norm)),'Pell norm certificate')
   e=plus(m,k(-1,X),Z,k(-1,times(base,Y)));oldtest=times(modexpr,V(qi))
   need(old[jj] in (plus(e,oldtest),minus(e,oldtest),k(-1,plus(e,oldtest)),k(-1,minus(e,oldtest))),'old power congruence')
   rmrows.add(jj);rmvars.add(qi);H=plus(H,times(Y,minus(m,X)));D=plus(m,k(-1,X),Z);S=plus(S,times(D,D),k(-1,times(Y,Y)));sy=plus(sy,times(Y,Y));errors=plus(errors,times(e,e));remainders=plus(remainders,k(-2,times(times(base,Y),AY)))
   if g['norm_reduced']:S=plus(S,norm);normsum=plus(normsum,norm)
  need(H==P(g['H']) and S==P(g['S']) and sy==P(g['sumY2']),'pool aggregates')
  target=plus(S,k(-2,times(base,H)),k(-1,times(T,sy)),remainders,k(-1,normsum))
  need(errors==target,'exact pooled square identity')
  K,L=V(g['new_K']),V(g['new_L']);rK=plus(K,k(-2,H),k(-1,times(plus(k(2,A),k(-1,base)),L)));rL=plus(S,k(-1,times(base,K)),L)
  need([P(z['terms']) for z in g['new_rows']]==[rK,rL],'pooled two-row formula');newrows.extend([rK,rL])
 need(rmrows==set(cert['removed_rows']) and rmvars==set(cert['removed_variables']),'pool removal boundary')
 mapping=dict(cert['old_to_new']);expect=[r for j,r in enumerate(old) if j not in rmrows]+newrows
 require_rows(rows(child),[renumber(r,mapping) for r in expect],'power pools')
 need(len(child['variables'])==len(parent['variables'])-11,'pool dimension')

def check_shear(parent,child,cert):
 old=rows(parent);maps={i:P(p) for i,p in cert['old_in_new']};inverse={i:P(p) for i,p in cert['new_in_old']};j=cert['orientation_row'];edited=old.copy()
 need(P(cert['orientation_parent_terms'])==old[j],'orientation source')
 for _,n,sign in cert['norm_subtractions']:edited[j]=plus(edited[j],k(-sign,old[n]))
 need(len(cert['norm_subtractions'])==14 and len(maps)==14,'shear membership')
 new=[pull(r,maps) for r in edited];require_rows(rows(child),new,'Pell coordinate shear')
 for i,p in maps.items():need(pull(p,inverse)==V(i),'unimodular inverse')
 for a,b in zip(edited,new):need(pull(b,inverse)==a,'residual inverse')

