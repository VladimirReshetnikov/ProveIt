"""Third-party-in-session audit of natural syntax sharing and pooled powers.
No producer/author-checker imports. Exact sparse arithmetic is local review code.
"""
from pathlib import Path
from hashlib import sha256
from copy import deepcopy
import json,argparse
from check_frame import add,scale,mul,terms
ROOT=Path(__file__).resolve().parents[2]/'natural'
def P(ts):return {tuple(m):c for c,m in ts if c}
def C(n):return {():n}if n else{}
def canon(o):return json.dumps(o,sort_keys=True,separators=(',',':')).encode()
def eq(a,b,msg):
 if a!=b:raise ValueError(msg)
def need(b,msg):
 if not b:raise ValueError(msg)
def sub(p,mapping):
 out={}
 for mon,c in p.items():
  term=C(c)
  for v in mon:term=mul(term,mapping.get(v,{(v,):1}))
  out=add(out,term)
 return out
def pos(p):return all(c>=0 for c in p.values())
def renumber(p,ren):return {tuple(ren[v]for v in m):c for m,c in p.items()}
def load(p):return json.loads(p.read_text())
def unique(ps,p,label):
 hits=[i for i,r in enumerate(ps)if r in (p,scale(-1,p))]
 need(len(hits)==1,('unique row',label,hits));return hits[0]
def check_sharing(source,target,cert):
 ns={v['name']:i for i,v in enumerate(source['variables'])};a=lambda n:{(ns[n],):1};ps=[P(r['terms'])for r in source['residuals']]
 eq(cert['parent_sha256'],sha256(canon(source)).hexdigest(),'shared parent pin');eq(cert['target_sha256'],sha256(canon(target)).hexdigest(),'shared target pin')
 L=add(scale(2,a('crt.encoded.b')),a('mul.36'));h=a('mul.143');g=add(scale(4,mul(L,L)),scale(26,L),C(42));core=add(h,scale(-1,g))
 maps={ns['mul.43']:add(h,scale(8,L),C(30)),ns['mul.143']:add(h,scale(4,L),C(14)),ns['mul.370']:add(a('mul.366'),scale(2,a('fact0.output')))}
 third='mul.166'if'mul.166'in ns else'add.171';factor=4 if third=='mul.166' else 8
 maps[ns[third]]=add(scale(4,h),scale(-4,L),C(-12))if factor==4 else add(scale(8,h),scale(4,a('crt.encoded.b')),scale(2,a('mul.60')),C(13))
 eq(cert['affine_parent_restorations'],{str(v):terms(p)for v,p in maps.items()},'all literal sharing maps')
 for name,p in maps.items():need(pos(sub(p,{ns['mul.143']:g})),('nonnegative restoration',name))
 need(pos(g),'nonnegative new coordinate')
 images=[sub(p,maps)for p in ps]
 # Locate expected source defining rows independently by the named monic coordinate.
 def definition(n):
  ids=[i for i,r in enumerate(source['residuals'])if r['label']in('multiplication','addition')and ps[i].get((ns[n],))==1]
  need(len(ids)==1,('monic definition',n,ids));return ids[0]
 r43,r143,rthird,r366,r370=[definition(n)for n in('mul.43','mul.143',third,'mul.366','mul.370')]
 eq(images[r43],core,'first square graph');eq(images[r143],core,'second square graph');eq(images[rthird],scale(factor,core),'third square graph');eq(images[r366],images[r370],'duplicate F graph')
 deleted={r143,rthird,r370};eq(cert['deleted_parent_rows'],sorted(deleted),'sharing deletion manifest')
 expected=[(i,core if i==r43 else p)for i,p in enumerate(images)if i not in deleted]
 used=sorted({v for _,p in expected for m in p for v in m});eq(used,cert['retained_extended_indices'],'shared used coords');ren={v:i for i,v in enumerate(used)}
 eq(len(expected),len(target['residuals']),'sharing row count')
 for (i,p),r in zip(expected,target['residuals']):
  eq(r['label'],'syntax.shared_square_definition'if i==r43 else source['residuals'][i]['label'],'shared row label');eq(P(r['terms']),renumber(p,ren),'shared exact output row')
 vs=deepcopy(source['variables']);vs[ns['mul.143']]={'name':'syntax.shared_shifted_square','kind':'shared nonnegative shifted square'};eq(target['variables'],[vs[v]for v in used],'sharing variables')
 return {'source_sha256':sha256(canon(source)).hexdigest(),'target_sha256':sha256(canon(target)).hexdigest(),'exact_rows_replayed':len(ps),'all_restorations_natural_on_shared_square':True}
def check_pool(source,target,cert):
 ns={v['name']:i for i,v in enumerate(source['variables'])};a=lambda n:{(ns[n],):1};ps=[P(r['terms'])for r in source['residuals']]
 eq(cert['parent_sha256'],sha256(canon(source)).hexdigest(),'pool source pin');eq(cert['target_sha256'],sha256(canon(target)).hexdigest(),'pool target pin')
 A=add(a('shared.lower_A'),a('shared.A_slack'));n=a('pow2.output');T=add(scale(2,mul(A,n)),scale(-1,mul(n,n)),C(-1));Tc=a('base3.T')
 bspec=[('index0.Y','index0.previous_Y',['choose0.modular_remainder','pooled_digits.t0.slack','crt.range.index.modular_remainder']),('index2.Y','index2.previous_Y',['crt.range.S.modular_remainder','pooled_digits.y.slack','crt.range.Sp.modular_remainder']),('index1.Y','index1.previous_Y',['crt.range.u.modular_remainder','pooled_digits.x.slack','crt.range.vq.modular_remainder'])]
 req=[(a(yn),a(zn),add(C(1),*[a(k)for k in m]))for yn,zn,m in bspec]
 removed={unique(ps,add(Tc,scale(-1,T)),'q modulus')}
 for qn,(Y,Z,m)in zip(['pow3.quotient','pow4.quotient','pow5.quotient'],req):removed.add(unique(ps,add(mul(n,Y),scale(-1,Z),scale(-1,m),scale(-1,mul(Tc,a(qn)))),'exact old power'))
 gids={ns[s]for s in ['base3.T','pow3.quotient','pow4.quotient','pow5.quotient']}
 eq(sorted(removed),cert['deleted_parent_rows'],'pool deleted rows');eq(sorted(gids),sorted(ns[s]for s in cert['deleted_parent_variables']),'pool deleted variables')
 for i,p in enumerate(ps):
  if i not in removed:need(not any(v in gids for m in p for v in m),'deleted coordinate still used')
 z=ns['shared.Zminus1'];maps={z:add(C(1),scale(2,{(z,):1}))};eq(cert['frame_substitution'],{'variable_original_index':z,'old_value':'2*new_value+1'},'frame edit')
 U,M,K=[{(len(source['variables'])+i,):1}for i in range(3)];Y2=add(*[mul(Y,Y)for Y,Z,m in req]);D2=add(*[mul(add(m,Z),add(m,Z))for Y,Z,m in req]);H=add(*[mul(Y,add(m,Z))for Y,Z,m in req])
 fresh=[add(U,scale(-1,Y2)),add(K,scale(-2,H),scale(-1,mul(add(scale(2,A),scale(-1,n)),M)),mul(n,U)),add(D2,M,scale(-1,mul(n,K)))]
 E=add(*[mul(add(m,Z,scale(-1,mul(n,Y))),add(m,Z,scale(-1,mul(n,Y))))for Y,Z,m in req]);eq(add(E,scale(-1,mul(T,M))),add(fresh[2],mul(n,fresh[1]),scale(-1,mul(mul(n,n),fresh[0]))),'literal aggregate identity')
 expected=[(r['label'],sub(p,maps))for i,(r,p)in enumerate(zip(source['residuals'],ps))if i not in removed]+list(zip(['pooled_power.sum_Y_squares','pooled_power.pooled_quotient_linearization','pooled_power.sum_power_errors'],fresh))
 used=sorted({v for _,p in expected for m in p for v in m});eq(used,cert['retained_extended_indices'],'pool used coordinates');ren={v:i for i,v in enumerate(used)};eq(len(expected),len(target['residuals']),'pool row census')
 for(label,p),r in zip(expected,target['residuals']):eq(r['label'],label,'pooled row label');eq(P(r['terms']),renumber(p,ren),'pooled exact row')
 vs=source['variables']+[{'name':'pooled_power.'+s,'kind':'natural pooled power witness'}for s in['U','M','K']];eq(target['variables'],[vs[i]for i in used],'pool variables')
 # The old lower ordinate is W*(z+1), strictly positive; decode W independently.
 hits=[p for p in ps if p.get((ns['mul.423'],))==1 and any(z in m for m in p)]
 need(len(hits)==1,'unique lower product');fr=hits[0];W={tuple(v for v in m if v!=z):-c for m,c in fr.items()if z in m};need(pos(W),'nonnegative W');eq(fr,add(a('mul.423'),scale(-1,mul(W,add(a('shared.Zminus1'),C(1))))),'literal W(z+1)')
 unique(ps,add(a('mul.424'),scale(-1,mul(add(W,C(1)),a('mul.423')))),'lower second product');unique(ps,add(mul(a('shared.lower_A'),a('shared.lower_A')),mul(a('mul.423'),a('mul.423')),scale(-1,mul(a('mul.424'),a('mul.424'))),C(-1)),'lower Pell norm')
 Wb=W;expansion=[]
 if'add.594'in ns:
  j=ns['add.594'];defs=[(i,add(scale(-1,p),{(j,):1}))for i,p in enumerate(ps)if p.get((j,))==1 and all(j not in m for m in p if m!=(j,))]
  defs=[(i,p)for i,p in defs if pos(p)];need(len(defs)==1,'unique frame partial sum');i,repl=defs[0];Wb=sub(Wb,{j:repl});expansion.append(i)
 # Projected branches store V through the floor relation, not a second y term.
 floor=add(C(1),a('y'),scale(-1,a('fact0.output')),scale(-1,mul(a('fact0.output'),a('fact0.remainder'))),scale(-1,mul(a('fact0.output'),a('fact0.slack'))),scale(-1,a('fact0.remainder')))
 fi=unique(ps,floor,'cofinal beta floor');c=add(a('y'),C(1));ks=[add(scale(2,a('t0')),C(4)),c,a('x')]
 bounds=[('n',n)]+[('output'+str(i),m)for i,(_,_,m)in enumerate(req)]+[('index'+str(i),k)for i,k in enumerate(ks)]+[('clear_plus_index'+str(i),add(c,k,C(1)))for i,k in enumerate(ks)]+[('clear_plus_two',add(c,C(2)))]
 boundproofs=[]
 for name,b in bounds:
  for k in [0,1,-1]:
   d=add(Wb,scale(k,floor),scale(-1,b))
   if pos(d):boundproofs.append({'name':name,'floor_row_multiplier':k,'nonnegative_difference':terms(d)});break
  else:raise ValueError(('missing linear frame bound',name,terms(add(Wb,scale(-1,b)))))
 need(Wb.get((),0)>=2,'W>=2')
 # All three consecutive norms/product gates survive; no orientation assumption for index2.
 seedrows=[]
 for idx,pn in [(0,'mul.447'),(1,'mul.456'),(2,'mul.481')]:
  Y=a('index'+str(idx)+'.Y');Z=a('index'+str(idx)+'.previous_Y');P0=a(pn)
  seedrows.append(unique(ps,add(P0,scale(-1,mul(Y,Z))),'seed product'))
  seedrows.append(unique(ps,add(mul(Y,Y),mul(Z,Z),scale(-2,mul(A,P0)),C(-1)),'seed norm'))
 # Existing incidence for t seed and x seed proves their positive abscissae.
 B=add(a('fact0.remainder'),a('fact0.slack'),C(1));Y0,Z0,_=req[0];Y1,Z1,_=req[2]
 orient0poly=add(mul(a('fact0.square_minus1'),Y0),scale(-1,Z0),scale(-1,add(a('y'),C(1))),scale(-1,mul(a('base0.T'),a('pow0.quotient'))))
 orient0hits=[(i,k)for k in [0,1,-1]for i,p in enumerate(ps)if p in (add(orient0poly,scale(k,floor)),scale(-1,add(orient0poly,scale(k,floor))))];need(len(orient0hits)==1,'retained t orientation up to authenticated floor');orient0,orient0floor=orient0hits[0]
 orient1=unique(ps,add(mul(B,Y1),scale(-1,Z1),scale(-1,a('pow1.output')),scale(-1,mul(a('base1.T'),a('pow1.quotient')))),'retained x orientation')
 need(orient0 not in removed and orient1 not in removed,'orientation row removed')
 return {'source_sha256':sha256(canon(source)).hexdigest(),'target_sha256':sha256(canon(target)).hexdigest(),'exact_rows_replayed':len(ps),'frame':terms(W),'frame_expansion_rows':expansion,'bound_proofs':boundproofs,'retained_orientation_rows':[orient0,orient1],'t_orientation_floor_multiplier':orient0floor,'index2_orientation_recovered_by_cleared_positive_error':True,'retained_consecutive_norm_rows':seedrows}
def census(e,expanded):
 need(e['domain']=='nonnegative integers','domain');need(all(len(m)<=2 for r in e['residuals']for _,m in r['terms']),'quadratic rows')
 pp=add(*(mul(P(r['terms']),P(r['terms']))for r in e['residuals']));eq(pp,P(expanded['terms']),'entire quartic collection')
 used={v for r in e['residuals']for _,m in r['terms']for v in m};eq(used,set(range(len(e['variables']))),'coordinate liveness')
 met={'variables':len(e['variables']),'quadratic_rows':len(e['residuals']),'exact_degree':max(map(len,pp)),'expanded_monomials':len(pp),'max_abs_expanded_coefficient':max(map(abs,pp.values())),'max_abs_row_coefficient':max(abs(c)for r in e['residuals']for c,_ in r['terms'])};eq(met,e['metrics'],'metrics');return met

def main():
 result={}
 for parent,shared,pool in [('dimension206','dimension203','pooled202'),('projected207','projected204','pooled203'),('projected208','projected205','pooled204')]:
  src=load(ROOT/'inherited'/parent/'equation.json');mid=load(ROOT/shared/'equation.json');out=load(ROOT/pool/'equation.json')
  sr=check_sharing(src,mid,load(ROOT/shared/'sharing_certificate.json'));pr=check_pool(mid,out,load(ROOT/pool/'pooling_certificate.json'))
  sr['metrics']=census(mid,load(ROOT/shared/'expanded_polynomial.json'));pr['metrics']=census(out,load(ROOT/pool/'expanded_polynomial.json'));result[shared]=sr;result[pool]=pr
  # Corrupt the aggregate sign but refresh the target pin: exact polynomial check must reject.
  bad=deepcopy(out);bad['residuals'][-1]['terms'][0][0]+=1;bc=load(ROOT/pool/'pooling_certificate.json');bc['target_sha256']=sha256(canon(bad)).hexdigest()
  try:check_pool(mid,bad,bc)
  except ValueError:pr['negative_control_rejected']=True
  else:raise ValueError('aggregate sign corruption accepted')
 result['passed']=True;return result
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);a=ap.parse_args();r=main();s=json.dumps(r,sort_keys=True,indent=2)+'\n';print(s)
 if a.output:a.output.write_text(s)
