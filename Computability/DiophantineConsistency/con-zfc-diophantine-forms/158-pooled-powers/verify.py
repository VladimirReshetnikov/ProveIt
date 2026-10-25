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

def check_strict(parent,child,cert):
 need(len(parent['variables'])==245,'parent dimension')
 removed={114,172,173,235};discard={124,125,175};redir={93,94,95,96,103}
 need(cert['removed_variables']==sorted(removed),'strict variable boundary')
 need(cert['removed_rows']==sorted(discard),'strict row boundary')
 need(cert['range_rows_redirected']==sorted(redir),'strict range boundary')
 mapping={i:j for j,i in enumerate(i for i in range(245) if i not in removed)}
 need({int(i):j for i,j in cert['old_to_new'].items()}==mapping,'strict reindex')
 expected=[]
 for j,r in enumerate(rows(parent)):
  if j in discard:continue
  if j==159:
   need(r.get((114,114))==-1,'removed power atom');r=dict(r);del r[(114,114)]
  if j in redir:r=pull(r,{235:V(234)})
  need(not any(i in removed for m in r for i in m),'strict dangling index')
  expected.append(renumber(r,mapping))
 require_rows(rows(child),expected,'strict')
 need(child['variables']==[x for i,x in enumerate(parent['variables']) if i not in removed],'strict variable list')

def check_basis(parent,child,cert):
 old=rows(parent);n=len(parent['variables']);mapping=dict(cert['old_to_new']);inv={v:i for i,v in mapping.items()};new=[renumber(r,inv) for r in rows(child)]
 need(cert['deleted_parent_coordinates']==[83,84,85,89],'basis deleted coords')
 need(cert['deleted_parent_rows']==[67,68,70,73],'basis deleted rows')
 forward={i:P(p) for i,p in cert['forward_polynomials']};reverse={i:P(p) for i,p in cert['reverse_polynomials']}
 need(forward=={81:plus(V(81),V(83)),n:times(V(3),V(14))},'basis forward map')
 a,b,S,Sp=V(10),V(11),V(14),V(15);d=plus(k(6,a),k(8,b),k(2,V(21)));aa=plus(a,C(-1))
 orig=cert['new_row_parent_indices'];byold={j:r for j,r in zip(orig,new) if j is not None};newJ=new[-1]
 for j,r in zip(orig,new):
  actual=pull(r,forward)
  if j is None:expected={}
  elif j==65:expected=plus(old[65],old[67])
  elif j==69:expected=plus(old[69],times(Sp,old[68]),k(-1,times(b,old[54])))
  elif j==72:expected=plus(old[72],times(S,old[70]))
  elif j==74:expected=plus(old[74],k(-1,times(S,old[68])),times(Sp,old[73]),k(-1,times(d,old[54])))
  else:expected=old[j]
  need(actual==expected,'basis forward residual identity '+str(j))
 for j,r in enumerate(old):
  actual=pull(r,reverse)
  if j in (65,68,70,73):expected={}
  elif j==67:expected=byold[65]
  elif j==69:expected=plus(byold[69],times(b,old[54]))
  elif j==72:expected=plus(byold[72],times(aa,newJ))
  elif j==74:expected=plus(byold[74],k(-1,times(b,newJ)),times(d,old[54]))
  else:expected=byold[j]
  need(actual==expected,'basis reverse residual identity '+str(j))
 need(len(child['variables'])==n-3,'basis dimension')

def check_pools(parent,child,cert,frame):
 old=rows(parent);names={v['name']:i for i,v in enumerate(parent['variables'])};N=lambda s,z=0:plus(V(names[s]),C(z));A=N('shared.A',1);q=N('pow2.output',-1)
 atoms=[P(a) for a in frame['atoms']];W=N('shared.W');squares=C(2)
 for a in atoms:squares=plus(squares,times(a,a))
 need(old[frame['row']]==minus(W,squares),'exact36-atom square frame')
 need(len(atoms)==36,'square frame atom count')
 need(cert.get('frame_strengthened') is False,'principal must retain original frame')
 for edit in cert['frame_edits']:need(P(edit['old'])==old[edit['row']]==P(edit['new']),'frame unexpectedly changed')
 index={0:N('t0'),2:plus(N('t0'),N('mul.1')),3:N('crt.encoded.a',-1),5:N('crt.encoded.b'),6:N('crt.encoded.c'),7:N('crt.encoded.d'),8:N('crt.encoded.S'),9:N('y'),10:N('crt.encoded.Sp'),11:N('crt.encoded.u'),12:N('x'),13:N('crt.encoded.vq'),14:N('crt.encoded_index_minus_one'),15:N('add.380')}
 expected_groups=[[3,5,7,8,9,10,12,13,15,16,17],[4,11,14]]
 rmrows=set();rmvars=set();newrows=[]
 for gn,g in enumerate(cert['groups']):
  base=plus(q,C(1)) if gn==0 else q;need(P(g['base'])==base and P(g['A'])==A,'pool base')
  need([r['request'] for r in g['requests']]==expected_groups[gn],'pool exact membership')
  need(base in atoms,'base outside frame')
  T=plus(k(2,times(A,base)),k(-1,times(base,base)),C(-1));need(T==P(g['T']),'pool modulus')
  mod=g['modulus_coordinate'];modrow=g['modulus_row'];need(old[modrow] in (minus(V(mod),T),minus(T,V(mod))),'modulus definition')
  H={};S={};sy={};errors={};remainders={};normsum={}
  rmrows.add(modrow);rmvars.add(mod)
  for r in g['requests']:
   m,X,Y,Z=[P(r[s]) for s in ('output','X','Y','Z')];request=r['request'];pair=r['pair'];qi=r['removed_quotient'];jj=r['removed_row']
   need(m==N('pow'+str(request)+'.output'),'output identity')
   need(qi==names['pow'+str(request)+'.quotient'],'quotient identity')
   need(m in atoms and index[pair] in atoms,'output/index outside square frame')
   AY=minus(Z,times(A,Y));need(old[r['retained_AY_row']] in (AY,k(-1,AY)),'A times Y certificate')
   norm=plus(times(X,X),times(Y,Y),k(-1,times(Z,Z)),C(-1));need(old[r['retained_norm_row']] in (norm,k(-1,norm)),'Pell norm certificate')
   e=plus(m,k(-1,X),Z,k(-1,times(base,Y)));oldtest=times(V(mod),V(qi))
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
 need(len(child['variables'])==len(parent['variables'])-12,'pool dimension')

def check_shear(parent,child,cert):
 old=rows(parent);maps={i:P(p) for i,p in cert['old_in_new']};inverse={i:P(p) for i,p in cert['new_in_old']};j=cert['orientation_row'];edited=old.copy()
 need(P(cert['orientation_parent_terms'])==old[j],'orientation source')
 for _,n,sign in cert['norm_subtractions']:edited[j]=plus(edited[j],k(-sign,old[n]))
 need(len(cert['norm_subtractions'])==14 and len(maps)==14,'shear membership')
 new=[pull(r,maps) for r in edited];require_rows(rows(child),new,'Pell coordinate shear')
 for i,p in maps.items():need(pull(p,inverse)==V(i),'unimodular inverse')
 for a,b in zip(edited,new):need(pull(b,inverse)==a,'residual inverse')

def check_beta(parent,child,cert):
 old=rows(parent);names={v['name']:i for i,v in enumerate(parent['variables'])};a,b=names['y'],names['pow0.output'];j=cert['semantic_row']
 need(old[j]==plus(C(-1),V(a),V(b),k(-1,times(V(b),V(b)))),'beta source relation')
 need(cert['eliminated_variable']==a and cert['restoration_variable']==b,'beta coordinates')
 mapping=dict(cert['old_to_new']);expected=[renumber(pull(r,{a:V(b)}),mapping) for i,r in enumerate(old) if i!=j]
 require_rows(rows(child),expected,'beta contraction');need(len(child['variables'])==len(parent['variables'])-1,'beta dimension')

def main(stage_root,rebuild=False):
 p0=ROOT/'inputs'/'parent245.json';need(digest(p0)=='1a42dd3a148c3084cd95a367869d251ed92e2f9852397215e4909e70b03d278e','source pin')
 paths=[p0,stage_root/'strict241'/'equation241.json',stage_root/'basis238'/'equation.json',stage_root/'pooled226'/'equation.json',stage_root/'differences226'/'equation.json',stage_root/'principal225'/'equation.json'];eq=[read(p) for p in paths]
 format_checks=[validate_equation(e,'stage'+str(i)) for i,e in enumerate(eq)]
 cert=[read(stage_root/'strict241'/'certificate241.json'),read(stage_root/'basis238'/'basis_certificate.json'),read(stage_root/'pooled226'/'pool_certificate.json'),read(stage_root/'differences226'/'shear_certificate.json'),read(stage_root/'principal225'/'beta_certificate.json')]
 for i,x in enumerate(cert):need(x.get('parent_equation_sha256',x.get('parent_sha256'))==digest(paths[i]),'certificate parent hash'+str(i))
 check_strict(eq[0],eq[1],cert[0]);check_basis(eq[1],eq[2],cert[1]);frame=read(ROOT/'inputs'/'square_frame_atoms.json');need(frame['equation_sha256']==digest(paths[2]),'square frame source hash');check_pools(eq[2],eq[3],cert[2],frame);check_shear(eq[3],eq[4],cert[3]);check_beta(eq[4],eq[5],cert[4])
 stages=[]
 for i,e in enumerate(eq):
  met,ex=measure(e)
  need(met['degree']==4 and met['row_height']<=256,'literal degree or residual height')
  if i:
   ep=paths[i].parent/('expanded241.json' if i==1 else 'expanded_polynomial.json');xp=read(ep);want=P(xp if isinstance(xp,list) else xp['terms']);need(ex==want,'complete polynomial expansion '+str(i))
   mp=paths[i].parent/('metrics241.json' if i==1 else 'METRICS.json');need(read(mp)==met,'metrics '+str(i))
  stages.append(met)
 need(stages[-1]=={'variables':225,'rows':162,'degree':4,'monomials':7867,'height':128446,'row_height':256},'principal metrics')
 rebuilt=0
 if rebuild:
  with tempfile.TemporaryDirectory(prefix='conzfc-rebuild-') as td:
   dest=Path(td)/'stages';rr=subprocess.run([sys.executable,'-B',str(ROOT/'build.py'),'--output',str(dest)],capture_output=True,text=True)
   need(rr.returncode==0,'rebuild process: '+rr.stderr)
   for p in stage_root.rglob('*.json'):
    relative=p.relative_to(stage_root);need((dest/relative).read_bytes()==p.read_bytes(),'byte reproduction '+str(relative));rebuilt+=1
 return {'result':'passed','stages':stages,'format_checks':format_checks,'exact_frame_atoms':36,'pooled_power_requests':[11,3],'basis_forward_identities':175,'basis_reverse_identities':178,'pell_coordinate_inverses':14,'reconstructed_json_files':rebuilt,'proof_scope':'Finite literal and polynomial identities. Unbounded arithmetic and cofinality arguments are in the accompanying proofs.'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--stages',type=Path,default=ROOT/'stages');ap.add_argument('--rebuild',action='store_true');ap.add_argument('--receipt',type=Path);a=ap.parse_args();r=main(a.stages,a.rebuild)
 if a.receipt:a.receipt.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r,indent=2))
