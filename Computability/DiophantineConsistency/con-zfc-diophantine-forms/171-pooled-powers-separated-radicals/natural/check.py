#!/usr/bin/env python3
"""Independent verifier: no import of producer or third-party packages."""
from pathlib import Path
from hashlib import sha256
from collections import defaultdict
import json,argparse,copy,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def require(ok,msg):
 if not ok:raise ValueError(msg)
def read(p):return json.loads(p.read_text())
def canon(o):return json.dumps(o,sort_keys=True,separators=(',',':')).encode()
def col(ts):
 d=defaultdict(int)
 for c,m in ts:
  require(type(c)is int and all(type(v)is int and v>=0 for v in m),'integer polynomial format')
  d[tuple(sorted(m))]+=c
 return [[c,list(m)] for m,c in sorted(d.items()) if c]
def plus(*ps):return col([t for p in ps for t in p])
def times(p,q):return col([[c*d,m+n] for c,m in p for d,n in q])
def sc(c,p):return col([[c*d,m] for d,m in p])
def sub(p,maps):
 terms=[]
 for c,m in p:
  ts=[[c,[]]]
  for v in m:ts=times(ts,maps.get(v,[[1,[v]]]))
  terms+=ts
 return col(terms)
def rename(p,ren):return col([[c,[ren[v] for v in m]] for c,m in p])
def atom(ns,n):return [[1,[ns[n]]]]
def allpositive(p):return all(c>=0 for c,m in p)
def metrics(e):
 p=plus(*[times(r['terms'],r['terms']) for r in e['residuals']]); used={v for r in e['residuals'] for c,m in r['terms'] for v in m}
 require(used==set(range(len(e['variables']))),'unused or invalid coordinate')
 require(e['domain']=='nonnegative integers','natural domain')
 require(all(len(m)<=2 for r in e['residuals'] for c,m in r['terms']),'nonquadratic residual')
 return {'variables':len(e['variables']),'quadratic_rows':len(e['residuals']),'exact_degree':max(len(m) for c,m in p),'expanded_monomials':len(p),'max_abs_expanded_coefficient':max(abs(c) for c,m in p),'max_abs_row_coefficient':max(abs(c) for r in e['residuals'] for c,m in r['terms'])},p

def check_sharing(source,target,cert):
 require(cert['parent_sha256']==sha256(canon(source)).hexdigest(),'sharing parent pin');require(cert['target_sha256']==sha256(canon(target)).hexdigest(),'sharing target pin')
 ns={v['name']:i for i,v in enumerate(source['variables'])}; a=lambda n:atom(ns,n)
 L=plus(sc(2,a('crt.encoded.b')),a('mul.36')); h=a('mul.143')
 require(cert['alpha']==26 and cert['beta']==42,'calibrated shifted square')
 g=plus(sc(4,times(L,L)),sc(26,L),[[42,[]]])
 expected={ns['mul.43']:plus(h,sc(8,L),[[30,[]]]),ns['mul.143']:plus(h,sc(4,L),[[14,[]]]),ns['mul.370']:plus(a('mul.366'),sc(2,a('fact0.output')))}
 third='mul.166' if 'mul.166'in ns else 'add.171'
 expected[ns[third]]=plus(sc(4,h),sc(-4,L),[[-12,[]]]) if third=='mul.166' else plus(sc(8,h),sc(4,a('crt.encoded.b')),sc(2,a('mul.60')),[[13,[]]])
 require(cert['affine_parent_restorations']=={str(v):p for v,p in expected.items()},'sharing literal maps')
 for v,p in expected.items():require(allpositive(sub(p,{ns['mul.143']:g})),'sharing natural restoration')
 core=plus(h,sc(-1,g)); images=[sub(r['terms'],expected) for r in source['residuals']]
 square_rows=cert['parent_square_rows'];require(len(square_rows)==3,'three shared square rows')
 for i,c in square_rows:require(images[i]==sc(c,core),'shared row identity')
 d1,d2=cert['duplicate_parent_rows'];require(images[d1]==images[d2],'factorial multiple duplicate')
 deleted={square_rows[1][0],square_rows[2][0],d2};require(sorted(deleted)==cert['deleted_parent_rows'],'sharing deletions')
 rowids=[i for i in range(len(images)) if i not in deleted];require(rowids==cert['target_parent_row_ids'],'sharing row coverage')
 used=cert['retained_extended_indices'];ren={v:i for i,v in enumerate(used)}
 require(len(target['residuals'])==len(rowids),'sharing row count')
 for row,i in zip(target['residuals'],rowids):
  require(row['terms']==rename(core if i==square_rows[0][0] else images[i],ren),'sharing target row')
 oldvs=copy.deepcopy(source['variables']);oldvs[ns['mul.143']]={'name':'syntax.shared_shifted_square','kind':'shared nonnegative shifted square'}
 require(target['variables']==[oldvs[v] for v in used],'sharing variable map')
 return {'all_parent_rows_checked':len(images),'removed_coordinates':3,'natural_gate_identity':g,'parent_sha256':cert['parent_sha256']}

def check_pool(source,target,cert):
 require(cert['parent_sha256']==sha256(canon(source)).hexdigest(),'pool parent pin');require(cert['target_sha256']==sha256(canon(target)).hexdigest(),'pool target pin')
 ns={v['name']:i for i,v in enumerate(source['variables'])}; a=lambda n:atom(ns,n)
 A=plus(a('shared.lower_A'),a('shared.A_slack'));n=a('pow2.output');T=a('base3.T');z=ns['shared.Zminus1']
 bspec=[('index0.Y','index0.previous_Y',['choose0.modular_remainder','pooled_digits.t0.slack','crt.range.index.modular_remainder']),('index2.Y','index2.previous_Y',['crt.range.S.modular_remainder','pooled_digits.y.slack','crt.range.Sp.modular_remainder']),('index1.Y','index1.previous_Y',['crt.range.u.modular_remainder','pooled_digits.x.slack','crt.range.vq.modular_remainder'])]
 require(cert['block_names']==[[y,z,m] for y,z,m in bspec],'pool block specification')
 req=[(a(y),a(z),plus([[1,[]]],*[a(s) for s in m])) for y,z,m in bspec]
 gone=['base3.T','pow3.quotient','pow4.quotient','pow5.quotient'];gids={ns[s] for s in gone}
 deleted=[i for i,r in enumerate(source['residuals']) if any(v in gids for c,m in r['terms'] for v in m)]
 require(len(deleted)==4 and deleted==cert['deleted_parent_rows'] and sorted(gone)==cert['deleted_parent_variables'],'pool removal coverage')
 oldexpected=[plus([[1,[]]],times(n,n),sc(-2,times(A,n)),T)]
 for (Y,Z,m),qn in zip(req,gone[1:]):oldexpected.append(plus(times(n,Y),sc(-1,Z),sc(-1,m),sc(-1,times(T,a(qn)))))
 actual=[source['residuals'][i]['terms'] for i in deleted]
 for p in oldexpected:require(p in actual or sc(-1,p)in actual,'removed exact power row')
 maps={z:plus(sc(2,[[1,[z]]]),[[1,[]]])}
 require(cert['frame_substitution']=={'variable_original_index':z,'old_value':'2*new_value+1'},'frame literal substitution')
 oldvs=source['variables']; newvs=oldvs+[{'name':'pooled_power.'+s,'kind':'natural pooled power witness'}for s in ('U','M','K')]
 U,M,K=[[[1,[len(oldvs)+i]]]for i in range(3)]
 Y2=plus(*[times(Y,Y)for Y,Z,m in req]);D2=plus(*[times(plus(m,Z),plus(m,Z))for Y,Z,m in req]);H=plus(*[times(Y,plus(m,Z))for Y,Z,m in req])
 fresh=[plus(U,sc(-1,Y2)),plus(K,sc(-2,H),sc(-1,times(plus(sc(2,A),sc(-1,n)),M)),times(n,U)),plus(D2,M,sc(-1,times(n,K)))]
 images=[sub(r['terms'],maps)for i,r in enumerate(source['residuals'])if i not in deleted]+fresh
 used=cert['retained_extended_indices'];ren={v:i for i,v in enumerate(used)}
 require(target['variables']==[newvs[v]for v in used],'pool variable map');require(len(images)==len(target['residuals']),'pool row count')
 for p,r in zip(images,target['residuals']):require(rename(p,ren)==r['terms'],'pool exact target row')
 # Direct formal identity: E-TM = last+n*middle+n^2*first, requiring no Pell norm.
 E=plus(*[times(plus(m,Z,sc(-1,times(n,Y))),plus(m,Z,sc(-1,times(n,Y))))for Y,Z,m in req])
 tpoly=plus(sc(2,times(A,n)),sc(-1,times(n,n)),[[-1,[]]])
 # middle K-2H-(2A-n)M+nU, last D2+M-nK
 lhs=plus(E,sc(-1,times(tpoly,M)))
 rhs=plus(fresh[2],times(n,fresh[1]),sc(-1,times(times(n,n),fresh[0])))
 require(lhs==rhs,'aggregate sum-of-error-squares identity')
 # Authenticate the literal old frame W and its three lower rows.
 mi=ns['mul.423'];zi=ns['shared.Zminus1']; frame_rows=[r['terms']for r in source['residuals']if [1,[mi]]in r['terms'] and any(zi in m for c,m in r['terms'])]
 require(len(frame_rows)==1,'one lower product row')
 W=col([[-c,[v for v in mon if v!=zi]]for c,mon in frame_rows[0]if zi in mon]);require(allpositive(W),'natural frame')
 require(frame_rows[0]==plus(a('mul.423'),sc(-1,times(W,plus(a('shared.Zminus1'),[[1,[]]])))),'frame product WZ')
 second=plus(a('mul.424'),sc(-1,times(plus(W,[[1,[]]]),a('mul.423'))));norm=plus(times(a('shared.lower_A'),a('shared.lower_A')),times(a('mul.423'),a('mul.423')),sc(-1,times(a('mul.424'),a('mul.424'))),[[-1,[]]])
 require(second in [r['terms']for r in source['residuals']],'lower second product');require(norm in [r['terms']for r in source['residuals']],'lower Pell norm')
 W_bound=W
 for _ in range(len(source['variables'])):
  changed=False
  for name,v in ns.items():
   if name!='add.594' or not any(v in mon for c,mon in W_bound):continue
   for row in source['residuals']:
    if [1,[v]]not in row['terms']:continue
    rest=col([[-c,mon]for c,mon in row['terms']if mon!=[v]])
    if all(len(mon)<=2 and v not in mon for c,mon in rest)and allpositive(rest):
     W_bound=sub(W_bound,{v:rest});changed=True;break
  if not changed:break
 # In projected endpoints add.594 still uses V=F*B+r. Its retained
 # cofinal/floor row is the literal identity V=y+1; use it only for bounds.
 if 'add.594'in ns:
  floor=plus([[1,[]]],a('y'),sc(-1,a('fact0.output')),sc(-1,times(a('fact0.output'),plus(a('fact0.remainder'),a('fact0.slack')))),sc(-1,a('fact0.remainder')))
  require(floor in [r['terms']for r in source['residuals']],'literal cofinal frame restoration')
  W_bound=plus(W_bound,floor)
 indices=[plus(sc(2,a('t0')),[[4,[]]]),plus(a('y'),[[1,[]]]),a('x')]
 atoms=[n]+[m for Y,Z,m in req]+indices
 for p in atoms:require(allpositive(plus(W_bound,sc(-1,p))),'pooled atom frame membership')
 require(dict((tuple(mon),c)for c,mon in W_bound).get((),0)>=2,'frame W>=2')
 c=indices[1]
 for k in indices:require(allpositive(plus(W_bound,sc(-1,c),sc(-1,k),[[-1,[]]])),'cleared exponent additive frame bound')
 require(allpositive(plus(W_bound,sc(-1,c),[[-2,[]]])),'cleared output additive frame bound')
 # The t and x consecutive pairs retain a positive output incidence.
 for idx,base,qn in [(0,a('fact0.square_minus1'),'pow0.quotient'),(1,plus(a('fact0.remainder'),a('fact0.slack'),[[1,[]]]),'pow1.quotient')]:
  Y=a('index'+str(idx)+'.Y');Z=a('index'+str(idx)+'.previous_Y');qi=ns[qn]
  rs=[r['terms']for r in source['residuals']if any(qi in mon for coef,mon in r['terms'])]
  require(len(rs)==1,'retained orientation incidence')
  rp=rs[0];sgn=next(coef for coef,mon in rp if qi in mon)
  require(sgn in(-1,1),'orientation quotient unit coefficient')
  rest=plus(sc(sgn,rp),times(base,Y),sc(-1,Z))
  require(allpositive(rest),'positive retained orientation remainder')
  require(allpositive(plus(W_bound,sc(-1,base))),'retained orientation base in frame')
 return {'cleared_exponent_bounds_checked':4,'retained_predecessor_incidences_checked':2,'all_parent_rows_checked':len(source['residuals']),'removed_old_coordinates':4,'new_natural_coordinates':3,'formal_error_identity':True,'frame_atoms_checked':len(atoms),'literal_frame':W,'expanded_frame_bound':W_bound,'parent_sha256':cert['parent_sha256']}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--rebuild',action='store_true');args=ap.parse_args();out={}
 for parent,shared,pool in [('dimension206','dimension203','pooled202'),('projected207','projected204','pooled203'),('projected208','projected205','pooled204')]:
  s=read(ROOT/'inherited'/parent/'equation.json');e=read(ROOT/shared/'equation.json');p=read(ROOT/pool/'equation.json')
  out[shared]=check_sharing(s,e,read(ROOT/shared/'sharing_certificate.json'));out[pool]=check_pool(e,p,read(ROOT/pool/'pooling_certificate.json'))
  for label,obj in [(shared,e),(pool,p)]:
   mm,terms=metrics(obj);require(mm==obj['metrics'],'metric census');recorded=read(ROOT/label/'expanded_polynomial.json');require(recorded['terms']==terms and recorded['variables']==len(obj['variables'])and recorded['domain']==obj['domain'],'full coefficient collection');out[label]['metrics']=mm
  # Negative control: dropping source evaluation row must be rejected by exact replay.
  bad=copy.deepcopy(p);bad['residuals']=[r for r in bad['residuals']if r['label']!='crt.oriented_nonnegative_evaluation'];badcert=read(ROOT/pool/'pooling_certificate.json');badcert['target_sha256']=sha256(canon(bad)).hexdigest()
  try:check_pool(e,bad,badcert)
  except ValueError:out[pool]['negative_control_deleted_evaluation_rejected']=True
  else:raise ValueError('negative control accepted')
 if args.rebuild:
  with tempfile.TemporaryDirectory()as d:
   subprocess.run([sys.executable,'-B',str(ROOT/'build.py'),'--output',d],check=True,stdout=subprocess.DEVNULL)
   for label in out:
    for file in (ROOT/label).glob('*.json'):require(file.read_bytes()==(Path(d)/label/file.name).read_bytes(),'byte rebuild '+str(file))
   require((ROOT/'SUMMARY.json').read_bytes()==(Path(d)/'SUMMARY.json').read_bytes(),'summary byte rebuild')
  out['rebuild']='all 18 endpoint JSON files and SUMMARY byte-identical'
 out['verified']=True;print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
