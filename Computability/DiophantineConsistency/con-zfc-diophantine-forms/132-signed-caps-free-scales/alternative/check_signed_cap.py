#!/usr/bin/env python3
"""Independent finite identities and domain-interface checks for signed cap."""
from pathlib import Path
from collections import defaultdict,Counter
import json,hashlib,sys,copy
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'vendor'))
import terminal_elimination as E
import audit_prior_horn as PH

def need(x,msg):
 if not x:raise ValueError(msg)
def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def scale(p,c):return {m:c*v for m,v in p.items()}
def var(i):return {(i,):1}
def check(root):
 a=json.loads((P/'source/parent_source.json').read_text()); b=json.loads((root/'raw_equation.json').read_text()); c=json.loads((root/'cap_certificate.json').read_text())
 need(hashlib.sha256(E.canonical_bytes(a)).hexdigest()==c['parent_sha256'],'parent hash')
 need(c['parent_sha256']=='af0086e4133239359eb1a69888e1a122394f587bf50d81ebfdbb64982117b8ff','frozen parent pin')
 removed={q['row']:q['literal'] for q in c['parent_rows_removed']}; retained=c['parent_rows_retained']
 need(set(removed)|set(retained)==set(range(len(a['residuals']))),'partition')
 need(not(set(removed)&set(retained)),'partition disjoint')
 for i,r in removed.items():need(a['residuals'][i]==r,'removed literal')
 need(b['residuals'][:len(retained)]==[a['residuals'][i] for i in retained],'retained literals')
 seeds=c['seed_indices'];W=c['W'];A=c['A'];cap=c['cap_variables']; n={v['name']:i for i,v in enumerate(a['variables'])}
 need(len(seeds)==16,'sixteen seeds')
 expected_seed_rows=[i for i,r in enumerate(a['residuals']) if r['label'].endswith('.index_at_most_Y')]
 need([ss['row'] for ss in seeds]==expected_seed_rows,'seed row binding')
 for ss in seeds:
  row=a['residuals'][ss['row']];prefix=row['label'].split('.')[0]
  need(ss['Y']==n[prefix+'.Y'] and ss['slack']==n[prefix+'.YminusK'],'seed coordinate binding')
  need(E.normalize(row['terms'])==add(var(ss['Y']),scale(var(ss['slack']),-1),scale(E.normalize(ss['exponent']),-1)),'literal seed exponent binding')
 gaps={s['slack'] for s in seeds};allowed_guards=gaps|{n['shared_index.q4minus1'],n['shared_index.Vquotient_minus1']}
 expected_removed={i for i,r in enumerate(a['residuals']) if r['label'].startswith('shared_index.') or (r['label'].startswith('index') and r['label'].split('.')[-1] in ['index_at_most_Y','norm3','S_mod_U','R_mod_4Y']) or (r['label'].startswith('nonnegative.') and int(r['label'].split('.')[1]) in allowed_guards)}
 need(set(removed)==expected_removed,'exact deletion inventory')
 for r in removed.values():
  lab=r['label'];allowed=lab.startswith('shared_index.') or (lab.startswith('index') and lab.split('.')[-1] in ['index_at_most_Y','norm3','S_mod_U','R_mod_4Y']) or (lab.startswith('nonnegative.') and int(lab.split('.')[1]) in allowed_guards)
  need(allowed,'forbidden deletion '+lab)
 br={r['label']:E.normalize(r['terms']) for r in b['residuals']}
 U,V,H,J,B,S,R,d,e,f,g,h,slack,Q=[cap[x] for x in ('U','V','H','J','B','S','R','d','e','f','g','h','slack','Q')]
 names={v['name']:i for i,v in enumerate(b['variables'])}
 need(all(v==names['cap.'+key] for key,v in cap.items()),'cap coordinate binding')
 AV=names['cap.AV'];AJ=names['cap.AJ'];BR=names['cap.BR'];VV=names['cap.VV']
 expect={
 'norm':{(U,U):1,(V,V):1,(AV,AV):-1,():-1},
 'auxiliary_norm':{(H,H):1,(J,J):1,(AJ,AJ):-1,():-1},
 'comparison_norm':{(S,S):1,(R,R):1,(BR,BR):-1,():-1},
 'comparison_progression':{(B,):1,():-1,tuple(sorted((V,d))):-4},
 'auxiliary_divisibility':{(J,):1,(VV,):-1,tuple(sorted((VV,e))):(-2 if c.get('odd_auxiliary') else -1)},
 'comparison_base':{(B,):1,(A,):-1,tuple(sorted((H,f))):-1},
 'comparison_abscissa':{(S,):1,(U,):-1,tuple(sorted((H,g))):-1},
 'comparison_ordinate':{(R,):1,(W,):-2,tuple(sorted((V,h))):-4},
 'squared_aggregate':{(V,):1,(W,):-2,():-1,(slack,):-1},
 'pooled_index_residue':{tuple(sorted((A,Q))):-1,(Q,):1}}
 for label,(z,x,y) in {'AV':(AV,A,V),'AJ':(AJ,A,J),'BR':(BR,B,R),'VV':(VV,V,V)}.items():expect[label]={(z,):1,tuple(sorted((x,y))):-1}
 for ss in seeds:
  yy=ss['Y'];expect['squared_aggregate'][(yy,yy)]=-1
  diff=add(var(yy),scale(E.normalize(ss['exponent']),-1));expect['pooled_index_residue']=add(expect['pooled_index_residue'],E.multiply(diff,diff))
 for label,poly in expect.items():need(br['cap.'+label]==poly,'cap literal '+label)
 for target,key in ([(slack,'slack')] if c.get('odd_auxiliary') else [(slack,'slack'),(e,'e')]):
  aa,bb,cc=c['cap_guard_witnesses'][key];need([aa,bb,cc]==[names['cap.nonnegative.'+str(target)+'.'+z] for z in 'abc'],'fresh guard binding');need(br['cap.nonnegative.'+str(target)]=={(target,):1,(aa,aa):-1,(bb,bb):-1,(cc,cc):-1,(cc,):-1},'guard '+key)
 appended=b['residuals'][len(retained):]
 expected_labels={'cap.'+x for x in expect}|{'cap.nonnegative.'+str(slack)}
 if not c.get('odd_auxiliary'):expected_labels.add('cap.nonnegative.'+str(e))
 need(len(appended)==len(expected_labels) and {r['label'] for r in appended}==expected_labels,'strict new cap row inventory')
 expected_new_names=['cap.'+x for x in ['U','V','H','J','B','S','R','d','e','f','g','h','slack','Q','AV','AJ','BR','VV']]
 for key,target in [('slack',slack)]+([] if c.get('odd_auxiliary') else [('e',e)]):expected_new_names += ['cap.nonnegative.'+str(target)+'.'+z for z in 'abc']
 need([v['name'] for v in b['variables'][len(a['variables']):]]==expected_new_names,'strict cap variable inventory')
 need(b['variables'][:len(a['variables'])]==a['variables'],'parent variable metadata retained')
 # Read nineteen requests independently from the documented semantic atom order.
 t={():16,(0,):1};K={(26,):2};q=var(183);qp={():1,(183,):1}
 data=[({():1,(5,):1},t,7,0),(var(28),K,29,1),({():1,(7,):1,(29,):1},K,182,1),(qp,add(t,var(5)),184,2),(q,t,185,0),(qp,add(t,var(27)),192,3),(qp,{():1,(17,):1},199,4),(q,add(t,{():1}),200,None),(qp,{():1,(18,):1},206,5),(qp,{():1,(19,):1},211,6),(qp,{():1,(20,):1},216,7),(qp,{():1,(21,):1},221,8),(q,{():1,(2,):1},222,9),(qp,{():1,(22,):1},228,10),(qp,{():1,(23,):1},233,11),(q,{():1,(1,):1},234,12),(qp,{():1,(24,):1},240,13),(qp,{():1,(25,):1},245,14),(qp,{():1,(174,):1},251,15)]
 atoms={tuple(sorted(p.items())):p for bs,k,m,seed in data for p in (bs,k,var(m))}
 frame={():2}
 for p in atoms.values():frame=add(frame,E.multiply(p,p))
 need(br['shared.frame_definition']==add(var(W),scale(frame,-1)),'exact frame atom identity')
 need({z[3] for z in data if z[3] is not None}==set(range(16)),'seed coverage')
 coverage=[]
 for number,(base,k,m,seed) in enumerate(data):
  lab='pow'+str(number)+'.power_congruence';need(lab in br,'power row retained')
  if seed is not None:
   need(k==E.normalize(seeds[seed]['exponent']),'seed exponent match')
   yi=seeds[seed]['Y'];xi=yi-1;poly=br[lab]
   need(poly.get((xi,))==1,'power main X')
   need(poly.get((m,))==-1,'power output')
  coverage.append({'request':number,'base':E.as_terms(base),'exponent':E.as_terms(k),'output':m,'seed':seed})
 # Fresh lower bounds from actually retained scalar guards and raw definitions.
 leaves={int(r['label'].split('.')[1]) for r in b['residuals'] if r['label'].startswith('nonnegative.')};bounds={v:0 for v in leaves};steps=[]
 def lower(poly):
  total=0
  for mon,c0 in poly.items():
   if not mon:total+=c0;continue
   if c0<0:return None
   z=c0
   for v,k in Counter(mon).items():
    if v not in bounds:
     if k%2:return None
     z=0
    else:z*=bounds[v]**k
   total+=z
  return total
 for _ in range(len(b['variables'])):
  change=False
  for ri,r in enumerate(b['residuals']):
   pp=E.normalize(r['terms'])
   for mon,co in pp.items():
    if len(mon)!=1 or mon[0] in bounds:continue
    restore=E.candidate(pp,mon[0],False)
    if restore is None:continue
    lb=lower(restore)
    if lb is not None and lb>=0:
     bounds[mon[0]]=min(lb,64);steps.append({'variable':mon[0],'row':ri,'lower':min(lb,64)});change=True
  if not change:break
 seed_lower=[lower(E.normalize(s['exponent'])) for s in seeds]
 need(all(x is not None and x>=1 for x in seed_lower),'positive seeds without omitted guards')
 fac=json.loads((root/'factored_source.json').read_text());final=json.loads((root/'equation.json').read_text());pc=json.loads((root/'projection_certificate.json').read_text())
 fc=json.loads((root/'factorization_certificate.json').read_text())
 need(hashlib.sha256(E.canonical_bytes(b)).hexdigest()==fc['input_sha256'],'factor input hash')
 need(hashlib.sha256(E.canonical_bytes(fac)).hexdigest()==fc['output_sha256'],'factor output hash')
 replay=copy.deepcopy(b['residuals'])
 for change in fc['changes']:
  ri=change['row'];need(replay[ri]['terms']==change['old'],'factor old literal');replay[ri]['terms']=change['new']
 replay.append({'label':'factored.horn','terms':fc['new_row']})
 replay=[r for i,r in enumerate(replay) if i not in fc['deleted_rows']]
 need(replay==fac['residuals'],'factor replay')
 for ss,rt in fc['square_roots'].items():
  si=int(ss);hits=[r for r in b['residuals'] if r['label']=='nonnegative_square_difference' and E.normalize(r['terms']).get((si,))==1]
  need(len(hits)==1,'factor square identity unique')
  need(E.candidate(E.normalize(hits[0]['terms']),si,False)==E.multiply(E.normalize(rt),E.normalize(rt)),'factor affine square identity')
 independent_factor,factor_metrics=PH.check_factor(b,root)
 independent_projection=PH.check_projection(independent_factor,root)
 E.verify(fac,final,pc)
 expected_count=352 if c.get('odd_auxiliary') else 355
 need(len(final['variables'])==expected_count,'exact endpoint variable count')
 need({v for r in final['residuals'] for coeff,m in r['terms'] for v in m}==set(range(expected_count)),'all final variables live')
 need(E.expand(final)==json.loads((root/'expanded_polynomial.json').read_text()),'exact expansion')
 receipt={'status':'PASS','variables':len(final['variables']),'rows':len(final['residuals']),'requests':19,'independent_seeds':16,'seed_lower_bounds':seed_lower,'frame_unique_atoms':len(atoms),'projection_steps':len(pc['steps']),'independent_horn':factor_metrics,'independent_projection':{k:v for k,v in independent_projection.items() if k!='free_coordinates'}}
 (root/'POWER_COVERAGE.json').write_bytes(E.canonical_bytes(coverage));(root/'PRESEMANTIC_BOUNDS.json').write_bytes(E.canonical_bytes({'steps':steps,'seed_lower_bounds':seed_lower,'leaves':sorted(leaves)}));return receipt

def pell(A,n):
 x,y=1,0
 for _ in range(n):x,y=A*x+(A*A-1)*y,x+A*y
 return x,y

def finite():
 count=0
 for W in (4,5,6):
  for A in (9*W**3+2,10*W**3+1):
   V=pell(A,2*W)[1];ks=list(range(1,W));ys=[pell(A,k)[1] for k in ks]
   need(V-2*W-1-sum(y*y for y in ys)>=0,'canonical cap')
   need(sum((y-k)**2 for y,k in zip(ys,ks))%(A-1)==0,'canonical pool');count+=1
 # These exact counterexamples show which hypotheses cannot just be omitted.
 W,A,k=4,1000,1;V=pell(A,2*W)[1]
 need(V-2*W-1>=0,'missing-pool counterexample y=0')
 j=A-1-k;x,y=pell(A,j);y=-y
 need(V-2*W-1-y>=0 and (y-k)**2%(A-1)==0,'signed-linear cap negative control')
 W,A,k=4,2,1;V=pell(A,2*W)[1];y=pell(A,2)[1]
 need(V-2*W-1-y*y>=0 and (y-k)**2%(A-1)==0,'missing-scale negative control')
 return {'canonical_cases':count,'negative_controls':['omitting pool permits zero-index seed','linear signed aggregate permits wrong negative seed','omitting scale permits wrong positive seed']}
if __name__=='__main__':
 root=Path(sys.argv[1]) if len(sys.argv)>1 else P/'signed_cap'
 receipt=check(root);receipt['finite']=finite();(root/'CHECK.json').write_bytes(E.canonical_bytes(receipt));print(json.dumps(receipt,indent=2))
