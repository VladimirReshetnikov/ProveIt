#!/usr/bin/env python3
"""Independent finite binding for doubled Pell ranks and squared power outputs."""
import argparse, collections, copy, hashlib, json, pathlib, sys
sys.dont_write_bytecode=True
from independent_algebra import require, load, bytesof, sha, poly, terms, plus, scale, mul, sub, guard_row, verify_domain, verify_projection, verify_quartic, expect_rejection

HERE=pathlib.Path(__file__).resolve().parent
SOURCE=HERE/'source/signsharing'
PACKET=HERE
CERT=HERE/'source/call_certificate.json'
RAW=HERE/'source/raw_builder.json'
DROPPED=[825,891,934,964,994,1024,1054,1084,1114,1144,1174]
def atom(v):return {(v,):1}
def const(n):return {():n}if n else{}
def sum_polys(ps):
 out={}
 for p in ps:out=plus(out,p)
 return out
def ideal(rows,combination):
 return sum_polys(mul(poly(x['multiplier']),poly(rows[x['row']]['terms']))for x in combination)
def check_cut(rows,cut,expected):
 require(ideal(rows,cut['row_combination'])==expected,'complete actual-row polynomial cut')
def nonnegative(p,known,strict=False):
 shifted={}
 for m,c in p.items():
  term=const(c)
  for v in m:term=mul(term,plus(atom(v),const(known.get(v,0))))
  shifted=plus(shifted,term)
 require(all(c>0 for c in shifted.values()),'nonnegative coefficients after known lower bounds')
 require(all(m.count(v)%2==0 or v in known for m in shifted for v in set(m)),'sign of every odd factor established')
 if strict:require(shifted.get((),0)>0,'strict positive constant after lower bounds')
def prefix_sign(rows,item,known):
 v,c,r=item['variable'],item['coefficient'],item['row'];rhs=poly(item['rhs'])
 require(v<643 and v not in known and c>0 and r<594,'fresh semantic-prefix sign target')
 require(all(x<643 and x!=v for m in rhs for x in m),'prefix-only sign inputs')
 expected=plus({(v,):c},scale(rhs,-1));actual=poly(rows[r]['terms'])
 require(actual==expected or actual==scale(expected,-1),'literal prefix sign equation')
 if item['kind']=='affine_square':
  root=poly(item['square_root']);require(max(map(len,root),default=0)<=1 and mul(root,root)==rhs,'full affine-square identity');deps=set()
 else:
  require(item['kind']=='positive_monomials'and all(c>0 for c in rhs.values()),'nonnegative monomial rule')
  deps={v for m in rhs for v in m if m.count(v)%2}
 require(item['dependencies']==sorted(deps)and deps<=set(known),'acyclic prefix signs')
 known[v]=0
def prefix_bound(rows,item,known,prefix=True):
 v,L=item['variable'],item['lower'];F=poly(item['factor']);G=poly(item['rhs'])
 require(v not in known and L>=0 and all(v not in m for p in(F,G)for m in p),'fresh lower-bound variable')
 if prefix:require(v<643 and all(x<643 for p in(F,G)for m in p for x in m)and all(i['row']<594 for i in item['row_combination']),'prefix-only lower-bound rule')
 require(ideal(rows,item['row_combination'])==plus(mul(atom(v),F),scale(G,-1)),'literal complete lower-bound ideal')
 nonnegative(F,known,True);nonnegative(plus(G,scale(F,-(L-1))),known,True);known[v]=L

def verify_front(new,ledger,raw,certificate,old68,domain68):
 # The seven equal-sum identities precede all arithmetic semantics.
 old75=load(SOURCE/'source/parent.json');domain75=load(SOURCE/'source/domain.json')
 verify_domain(old75,domain75,old68,domain68)
 require(new['residuals'][:594]==old68['residuals'][:594],'entire semantic prefix unchanged')
 predicates=[g['predicate']for g in domain68['guards']if not(g['predicate']['kind']=='retained_scalar'and g['predicate']['raw_variables'][0]in DROPPED)and g['predicate']['kind']!='paired_index_slacks']
 require(len(predicates)==56 and [g['predicate']for g in ledger['guards']]==predicates,'exact56-predicate boundary')
 require(ledger['drop_scalar_guards']==DROPPED and ledger['drop_product_guard']==[674,861],'exact dropped index conditions')
 require(len(new['variables'])==1427 and len(new['residuals'])==1233,'new parent dimensions')
 for j,g in enumerate(ledger['guards']):
  ids=list(range(1259+3*j,1259+3*j+3));require(g['auxiliary']==ids,'fresh consecutive guard triple')
  require(poly(new['residuals'][1177+j]['terms'])==guard_row(g['predicate'],ids),'entire new guard row')
 direct={p['raw_variables'][0]for p in predicates if p['kind']=='retained_scalar'}
 require(all(p in predicates for p in[{'kind':'equal_sum_product','raw_variables':[r,s],'terms':[[1,[r,s]]]}for r,s,*_ in domain68['changed_pairs']]),'all seven product predicates retained')
 restored={v for r,s,*_ in domain68['changed_pairs']for v in(r,s)}
 require(all(a in direct or a==91 for _,_,_,_,(a,b,_)in domain68['changed_pairs'])and all(b in direct for _,_,_,_,(a,b,_)in domain68['changed_pairs'])and {94,95}<=direct,'all equal-sum anchors before semantics')
 scalar=direct|restored
 fguard=[p for p in predicates if p['kind']=='factorial_lower_bound'];require(len(fguard)==1 and poly(fguard[0]['terms'])=={(87,):1,():-2},'literal f>=2 predicate')
 vguard=[p for p in predicates if p['kind']=='strict_common_V'];require(len(vguard)==1 and poly(vguard[0]['terms'])=={(656,):1,():-1},'literal V>=1 predicate')
 require({94,95}<=scalar,'early output sign prerequisites')
 # N - f*r -(f-1)*s - f is a literal eight-row ideal.
 front=new['residuals'];R=sum_polys(poly(front[i]['terms'])for i in[83,84,85]);F=sum_polys(scale(poly(front[i]['terms']),c)for i,c in[(78,-1),(79,1),(80,1),(81,1),(82,1)])
 expected={(93,):1,(87,94):-1,(87,95):-1,(95,):1,(87,):-1}
 require(plus(F,mul(plus(atom(87),const(-1)),R))==expected,'early N-sign ideal')
 lower={87:2,94:0,95:0};nonnegative(plus(scale(expected,-1),atom(93)),lower,True)
 scalar.add(93)
 p=certificate['prefix_proof'];initial=p['initial_semantic_guard_indices']
 require(len(initial)==61 and set(initial)<=scalar and all(v<643 for v in initial),'all61 original prefix signs restored before use')
 known={v:0 for v in initial}
 for item in p['preliminary_t_n_bounds']:prefix_bound(front,item,known)
 for stage in p['five_stages']:
  for item in stage['preceding_sign_steps']:prefix_sign(front,item,known)
  prefix_bound(front,stage,known)
 for item in p['final_sign_steps']:prefix_sign(front,item,known)
 require(set(known)==set(range(643))and p['required_nonnegative_coordinates']==list(range(643)),'all643 semantic-prefix signs established')
 positive=certificate['positive_prefix'];M=plus(const(1),mul(atom(87),plus(atom(59),const(1))))
 check_cut(front,positive['canonical_modulus_cut'],plus(M,scale(atom(129),-1)));nonnegative(M,known,True)
 strict={4,5,129}
 for item in positive['steps']:
  v,r=item['variable'],item['row'];q=poly(front[r]['terms'])
  require(v not in strict and v in known and r<594 and raw['rows'][r].get('gate')==v and q.get((v,))==1,'actual positive prefix constructor')
  rhs=scale({m:c for m,c in q.items()if m!=(v,)},-1);mon=tuple(sorted(item['positive_monomial']))
  require(all(c>0 for c in rhs.values())and mon in rhs and set(mon)<=strict,'positive monomial from earlier positive factors');strict.add(v)
 require(sorted(strict)==positive['known_after'],'entire positivity ledger')
 require(all(s['aliases']['k']in strict for s in certificate['seeds']),'all15 seed exponents positive')
 require(all(c['base']in strict or c['base']==87 for c in certificate['power_calls']),'all21 power bases positive, including f>=2')
 # Seed orientation uses only selected bases that are at least two.
 radius_cut=sum_polys([poly(front[77]['terms']),poly(front[75]['terms']),mul(atom(87),poly(front[74]['terms']))])
 require(radius_cut==sum_polys([atom(92),const(-1),scale(mul(atom(87),mul(atom(86),atom(86))),-1)]),'literal radius base n92=1+f*K^2')
 radix_cut=sum_polys([poly(front[508]['terms']),mul(atom(129),poly(front[507]['terms'])),mul(atom(129),poly(front[506]['terms']))])
 require(radix_cut==plus(atom(530),scale(mul(atom(129),sum_polys([const(1),atom(93),atom(113)])),-1)),'literal common radix base')
 require(poly(front[509]['terms'])=={(531,):1,(530,):-1,():-1},'literal successor radix base')
 selected=[]
 for seed in certificate['seeds']:
  j=seed['selected_power_call'];call=certificate['power_calls'][j];a=seed['aliases']
  require(call['base']in[5,92,530,531]and[call['exponent'],call['X'],call['Y']]==[a['k'],a['X'],a['Y']],'same-seed supporting call with an independently at-least-two base');selected.append(j)
 require(len(set(selected))==15,'fifteen selected calls orient all seeds')
 # The initial carrier lower bounds use only the retained T0 guard.
 require(694 in direct,'base0.T is retained');known[694]=0
 for item in certificate['initial_A_D_bounds']:prefix_bound(front,item,known,False)
 require(known[644]>=2 and known[917]>=2,'A>=2 before any Pell classification')
 return {'semantic_signs':643,'initial_signs':61,'positive_seed_exponents':[s['aliases']['k']for s in certificate['seeds']],'early_output_sign':93,'selected_seed_orientation_calls':selected,'retained_private_predicates':['base0.T>=0','V>=1','f>=2'],'prefix_uses_no_private_index_slack':True}

def verify_edits(old,new,ledger,certificate,raw):
 require(old['variables'][:1259]==new['variables'][:1259]==raw['variables'],'all1259 original body variable records')
 require(all(poly(r['terms'])==poly(old['residuals'][j]['terms'])for j,r in enumerate(raw['rows'])),'whole raw metadata coefficient binding')
 expected=copy.deepcopy(old['residuals'][:1177]);changed={}
 def setrow(i,ts):
  require(i not in changed,'distinct prescribed edit');changed[i]={'row':i,'before':copy.deepcopy(expected[i]),'after':{'label':expected[i]['label'],'terms':ts}}
  expected[i]['terms']=ts
 for c,p in zip(certificate['power_calls'],raw['powers']):
  require([c['base'],c['exponent'],c['output']]==[p[k][1]for k in['base','exponent','output']],'literal power tuple agrees across independent ledgers')
  m=c['output'];rows=[x['row']for x in c['cut']['row_combination']if [-1,[m]]in expected[x['row']]['terms']]
  require(len(rows)==1,'unique power output precursor');r=rows[0];setrow(r,[[coef,[m,m]if mon==[m]else mon]for coef,mon in expected[r]['terms']])
 for s,p in zip(certificate['seeds'],raw['seeds']):
  a=s['aliases'];require(a['k']==p['exponent'][1]and[a['X'],a['Y']]==[v[1]for v in p['pair']],'literal seed tuple agrees')
  r=s['rows']['R_mod_4Y']-1;k=a['k'];require([-1,[k]]in expected[r]['terms'],'actual seed index precursor')
  setrow(r,[[-2 if mon==[k]else coef,mon]for coef,mon in expected[r]['terms']])
 setrow(856,[[1,[921]],[-2,[644,919]],[-2,[644,920]],[1,[670]]]);setrow(857,[[1,[922]],[-2,[919]],[-2,[650,671]],[1,[671]]])
 outputs={c['output']for c in certificate['power_calls']}
 for r in range(1134,1176):
  oldterms=expected[r]['terms'];ts=[[coef,[mon[0],mon[0]]if len(mon)==1 and mon[0]in outputs else mon]for coef,mon in oldterms]
  if ts!=oldterms:setrow(r,ts)
 setrow(1176,[[1,[643]],[-2,[1258]]])
 require(expected==new['residuals'][:1177]and len(changed)==60,'all and only60 intended body edits')
 require([{k:x[k]for k in['row','before','after']}for x in ledger['edits']]==[changed[i]for i in sorted(changed)],'complete literal edit ledger')
 require(ledger['power_calls']==certificate['power_calls']and ledger['seeds']==certificate['seeds'],'all call/seed rows retained in ledger')
 rows=new['residuals'];A=atom(644);D=plus(mul(A,A),const(-1))
 for c in certificate['power_calls']:
  X,Y,n,m,T,q=map(atom,[c[k]for k in['X','Y','base','output','modulus','quotient']])
  expected=sum_polys([X,mul(n,Y),scale(mul(A,Y),-1),scale(mul(m,m),-1),scale(mul(T,q),-1)])
  check_cut(rows,c['cut'],expected)
 for s in certificate['seeds']:
  a=s['aliases'];X,Y,S,R,k,sq,rq=map(atom,[a[z]for z in['X','Y','S','R','k','Squotient','Rquotient']]);B=atom(667)
  target={'norm1':sum_polys([mul(X,X),scale(mul(D,mul(Y,Y)),-1),const(-1)]),'norm3':sum_polys([mul(S,S),scale(mul(plus(mul(B,B),const(-1)),mul(R,R)),-1),const(-1)]),'S_mod_U':sum_polys([S,scale(X,-1),scale(mul(atom(655),sq),-1)]),'R_mod_4Y':sum_polys([R,scale(k,-2),scale(mul(Y,rq),-4)]),'index_at_most_Y':sum_polys([Y,scale(k,-1),scale(atom(a['YminusK']),-1)])}
  for name,t in target.items():check_cut(rows,s['cuts'][name],t)
 # All frame arguments are included, with each output squared and the frame doubled.
 args=sorted({p[k][1]for p in raw['powers']for k in['base','exponent','output']})
 require(args==certificate['frame_arguments']==ledger['frame_arguments']and len(args)==43 and len(outputs)==21,'complete43-argument frame')
 frame=sum_polys([atom(643),const(-4)]+[scale(mul(atom(v),atom(v))if v in outputs else atom(v),-2)for v in args])
 comb=copy.deepcopy(certificate['frame_cut']['row_combination'])
 for item in comb:
  if item['row']!=1176:item['multiplier']=terms(scale(poly(item['multiplier']),2))
 require(ideal(rows,comb)==frame==poly(ledger['frame_formula']),'unconditional doubled square-output frame identity')
 require(not(outputs&{s['aliases']['k']for s in certificate['seeds']}),'all doubled indices occur linearly in frame')
 # The derived t+1 pair takes two unit steps, not one.
 require(len(raw['derivations'])==1 and raw['derivations'][0]['kind']=='shift'and raw['derivations'][0]['shift']==1,'only one inherited derived index')
 X,Y=atom(670),atom(671);AX=mul(A,X);DY=mul(D,Y)
 require(poly(rows[598]['terms'])==plus(atom(650),scale(mul(A,A),-1)),'stored A-square identity')
 require(sum_polys(poly(rows[j]['terms'])for j in[852,853])==sum_polys([atom(650),scale(atom(917),-1),const(-1)]),'stored D identity')
 require(poly(rows[854]['terms'])==plus(atom(919),scale(AX,-1))and poly(rows[855]['terms'])==plus(atom(920),scale(mul(atom(917),Y),-1)),'stored first-step products')
 substituted={650:mul(A,A),917:D,919:AX,920:DY}
 results=[]
 for row,target in [(856,921),(857,922)]:
  p=poly(rows[row]['terms'])
  for v,f in substituted.items():p=sub(p,v,f)
  rhs=scale({m:c for m,c in p.items()if m!=(target,)},-1);results.append(rhs)
 require(results[0]==sum_polys([mul(plus(scale(mul(A,A),2),const(-1)),X),scale(mul(A,mul(D,Y)),2)]),'entire two-step abscissa polynomial')
 require(results[1]==sum_polys([scale(AX,2),mul(plus(scale(mul(A,A),2),const(-1)),Y)]),'entire two-step ordinate polynomial')
 # Original norm and congruence interfaces are unchanged and completely bound.
 require(ideal(rows,certificate['bootstrap_norm']['row_combination'])==poly(certificate['bootstrap_norm']['expanded_polynomial']),'entire bootstrap norm ideal')
 for name in['unit_norm_cut','comparison_base_constructor','comparison_base_congruence','positive_V_product']:
  require(ideal(rows,certificate[name]['row_combination'])==poly(certificate[name]['polynomial']),'unchanged common Pell interface '+name)
 for m in certificate['moduli']:require(ideal(rows,m['cut']['row_combination'])==poly(m['cut']['polynomial']),'unchanged exact base modulus')
 return {'exact_body_edits':60,'squared_output_calls':21,'doubled_seed_indices':15,'corrected_two_step_pairs':1,'distinct_frame_arguments':43,'frame_outputs_squared':21}

def verify_odd_control(path):
 fixture=load(path)
 require(fixture['scope']=='generic one-call counterexample, not a ZFC-source zero','negative control scope')
 v={k:int(x)for k,x in fixture['values'].items()}
 n,k,m,W,A,Z,U,V,B,X,Y,S,R,T,q=[v[x]for x in['n','k','m','W','A','Z','U','V','B','X','Y','S','R','T','qpower']]
 require(W==2*(2+n+k+m*m)and T==2*A*n-n*n-1,'exact generic frame and modulus constructors')
 checks={
  'frame':A*A-W**3*(W+2)*Z*Z==1,
  'large_frame':A>W**W,
  'main_norm':X*X-(A*A-1)*Y*Y==1,
  'common_norm':U*U-(A*A-1)*V*V==1,
  'comparison_norm':S*S-(B*B-1)*R*R==1,
  'shared_B_mod_U':(B-A)%U==0,
  'shared_B_mod_4V':(B-1)%(4*V)==0,
  'S_mod_U':(S-X)%U==0,
  'odd_index_congruence':(R-k)%(4*Y)==0,
  'modified_squared_power':X+n*Y==A*Y+m*m+T*q,
  'front_signs':n>=2 and k>=1 and m>=0 and V>=1 and n<W and 2*k<W and m*m<W,
  'deleted_index_guard_fails':Y<k,
  'false_power':m!=n**k,
  'even_index_congruence_fails':(R-2*k)%(4*Y)!=0}
 require(checks==fixture['checks']and all(checks.values()),'all generic odd-index counterexample identities')
 return {'scope':fixture['scope'],'checked_conditions':len(checks),'rejected_by_even_index':True}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=pathlib.Path,default=PACKET/'INDEPENDENT_CHECK.json');args=ap.parse_args()
 old=load(SOURCE/'parent.json');domain=load(SOURCE/'domain.json');new=load(PACKET/'parent.json');ledger=load(PACKET/'ledger.json');raw=load(RAW);certificate=load(CERT)
 require(sha(SOURCE/'parent.json')==ledger['parent68_sha256']and sha(SOURCE/'domain.json')==ledger['domain68_sha256']and sha(RAW)==ledger['raw_builder_sha256']and sha(CERT)==ledger['old_call_certificate_sha256'],'all whole upstream bytes pinned')
 finite=verify_edits(old,new,ledger,certificate,raw);front=verify_front(new,ledger,raw,certificate,old,domain)
 framed=load(PACKET/'frame_parent.json');fc=load(PACKET/'frame_projection.json');frame_steps=verify_projection(new,framed,fc);require(frame_steps==42,'exact frame contraction size')
 profiles={}
 for path in sorted(PACKET.glob('support*/equation.json')):
  child=load(path);projection=load(path.with_name('projection.json'));expanded=load(path.with_name('polynomial.json'));steps=verify_projection(framed,child,projection);metrics=verify_quartic(child,expanded)
  profiles[path.parent.name]={'metrics':metrics,'unique_signed_restorations':frame_steps+steps,'equation_sha256':sha(path),'polynomial_sha256':sha(path.with_name('polynomial.json'))};print(path.parent.name,metrics,flush=True)
 wrong=copy.deepcopy(new);wrong['residuals'][637]['terms'][0][0]=-1
 missing_shift=copy.deepcopy(new);missing_shift['residuals'][856]=copy.deepcopy(old['residuals'][856])
 bad_frame=copy.deepcopy(new);bad_frame['residuals'][1176]['terms'][1][0]=-1
 controls=[expect_rejection(lambda:verify_edits(old,wrong,ledger,certificate,raw),'odd seed rank restored'),expect_rejection(lambda:verify_edits(old,missing_shift,ledger,certificate,raw),'one-step derived pair restored'),expect_rejection(lambda:verify_edits(old,bad_frame,ledger,certificate,raw),'undoubled frame restored')]
 negative=verify_odd_control(PACKET/'odd_index_negative_control.json')
 result={'status':'PASS','optimized_python':not __debug__,'literal_interfaces':finite,'early_front':front,'frame_restorations':frame_steps,'profiles':profiles,'rejected_corruptions':controls,'odd_index_control':negative,'scope':'Finite exact source/guard/interface/prefix checks and full integer projections. Unbounded even-rank and canonical reconstruction proof is separate; no source-root search or new kernel formalization.'}
 args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_bytes(bytesof(result));print(json.dumps({'status':'PASS','profiles':len(profiles),'rejected_corruptions':len(controls)},indent=2))
if __name__=='__main__':main()
