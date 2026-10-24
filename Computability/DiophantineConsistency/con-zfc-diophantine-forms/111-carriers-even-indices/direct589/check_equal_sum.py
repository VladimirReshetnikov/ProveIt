#!/usr/bin/env python3
"""Independent exact checker; imports neither builder nor projection engine."""
import argparse, collections, copy, hashlib, json, pathlib

HERE=pathlib.Path(__file__).resolve().parent
SOURCE=HERE/'source'
PACKET=HERE
EXPECTED_PAIRS=[(562,563,537,547,(549,550,526)),(585,586,553,574,(576,577,547)),(593,594,559,574,(576,577,547)),(601,602,565,574,(576,577,547)),(619,620,578,608,(610,611,572)),(637,638,591,626,(628,629,585)),(123,564,540,530,(91,537,518))]
def require(b,message):
 if not b:raise ValueError(message)
def load(p):return json.loads(p.read_bytes())
def bytesof(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def poly(terms):
 ans=collections.defaultdict(int)
 for c,m in terms:
  require(type(c) is int and all(type(v) is int and v>=0 for v in m),'integral syntax')
  ans[tuple(sorted(m))]+=c
 return {m:c for m,c in ans.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def plus(a,b):
 r=dict(a)
 for m,c in b.items():r[m]=r.get(m,0)+c
 return {m:c for m,c in r.items() if c}
def scale(p,c):return {m:c*v for m,v in p.items() if c*v}
def mul(a,b):
 r=collections.defaultdict(int)
 for x,c in a.items():
  for y,d in b.items():r[tuple(sorted(x+y))]+=c*d
 return {m:c for m,c in r.items() if c}
def sub(p,v,f):
 r={}
 for mon,c in p.items():
  if v not in mon:r=plus(r,{mon:c});continue
  term={():c}
  for x in mon:term=mul(term,f if x==v else {(x,):1})
  r=plus(r,term)
 return r
def cut(old,start):
 r={}
 for j in range(start,start+3):r=plus(r,poly(old['residuals'][j]['terms']))
 return r
def guard_row(predicate,ids):
 a,b,c=ids
 return plus(poly(predicate['terms']),{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})

def verify_domain(old,old_domain,new,new_domain):
 n=1259;nr=1177
 require(old_domain['baseline_body_variables']==n and old_domain['baseline_body_rows']==nr,'old body dimensions')
 require(new_domain['baseline_body_variables']==n and new_domain['baseline_body_rows']==nr,'new body dimensions')
 require(old['variables'][:n]==new['variables'][:n],'unchanged complete body metadata')
 require(old['residuals'][:nr]==new['residuals'][:nr],'unchanged complete body coefficients')
 require(len(old['variables'])==1484 and len(old['residuals'])==1252,'old parent shape')
 require(len(new['variables'])==1463 and len(new['residuals'])==1245,'new parent shape')
 require(len(old_domain['guards'])==75 and len(new_domain['guards'])==68,'complete guard counts')
 for label,eq,domain in [('old',old,old_domain),('new',new,new_domain)]:
  for j,g in enumerate(domain['guards']):
   ids=list(range(n+3*j,n+3*j+3))
   require(g['auxiliary']==ids,label+' guard coordinate partition')
   require(poly(eq['residuals'][nr+j]['terms'])==guard_row(g['predicate'],ids),label+' complete guard coefficient identity')
   require(all(eq['variables'][i]['kind']=='nonnegative_guard' for i in ids),label+' guard variable metadata')
 require(json.loads(json.dumps(EXPECTED_PAIRS))==new_domain['changed_pairs'],'exact seven intended pairs')
 removed={v for r,s,*_ in EXPECTED_PAIRS for v in (r,s)}
 retained=[g['predicate'] for g in old_domain['guards'] if not(g['predicate']['kind']=='retained_scalar' and g['predicate']['raw_variables'][0] in removed)]
 require(len(retained)==61 and [g['predicate'] for g in new_domain['guards'][:61]]==retained,'all61 predicates copied verbatim')
 available={g['raw_variables'][0] for g in retained if g['kind']=='retained_scalar'}
 require({94,95}.issubset(available),'factorial0 anchor sign premises retained')
 require(cut(old,83)=={(91,):1,(94,):-1,(95,):-1,():-1},'raw91 positive affine consequence')
 available.add(91)
 cuts=[]
 for j,(r,s,start,q,(a,b,anchor_start)) in enumerate(EXPECTED_PAIRS):
  require(a in available and b in available,'both equal-sum anchor signs available before semantics')
  require(cut(old,start)=={(q,):1,(r,):-1,(s,):-1,():-1},'full changed-pair row ideal')
  require(cut(old,anchor_start)=={(q,):1,(a,):-1,(b,):-1,():-1},'full anchor row ideal')
  predicate={'kind':'equal_sum_product','raw_variables':[r,s],'terms':[[1,[r,s]]]}
  require(new_domain['guards'][61+j]['predicate']==predicate,'literal product predicate')
  cuts.append({'pair':[r,s],'anchor':[a,b],'denominator':q,'source_rows':list(range(start,start+3)),'anchor_rows':list(range(anchor_start,anchor_start+3))})
 require(all(sum(g['predicate'].get('raw_variables')==[v] for g in old_domain['guards'])==1 for v in removed),'each removed sign occurs exactly once')
 return {'copied_body_variables':n,'copied_body_rows':nr,'copied_predicates':61,'product_predicates':7,'restored_scalar_signs':14,'cuts':cuts}

def verify_projection(parent,child,certificate):
 require(hashlib.sha256(bytesof(parent)).hexdigest()==certificate['input_sha256'],'projection input hash')
 require(hashlib.sha256(bytesof(child)).hexdigest()==certificate['output_sha256'],'projection output hash')
 rows={i:poly(r['terms']) for i,r in enumerate(parent['residuals'])};dead=set()
 for step in certificate['steps']:
  i=step['row_id'];v=step['variable'];f=poly(step['restoration'])
  require(i in rows and v not in dead,'valid distinct projection target')
  require(not any(x in dead or x==v for mon in f for x in mon),'triangular integer restoration')
  require(max(map(len,f),default=0)<=2,'quadratic restoration bound')
  identity=plus({(v,):1},scale(f,-1))
  require(rows[i]==identity or rows[i]==scale(identity,-1),'exact unit-leading deleted equation')
  del rows[i]
  for k,p in list(rows.items()):
   if any(v in mon for mon in p):
    changed=sub(p,v,f)
    require(max(map(len,changed),default=0)<=2,'every substituted residual remains quadratic')
    if changed:rows[k]=changed
    else:del rows[k]
  dead.add(v)
 kept=certificate['retained_original_variables'];remaining=sorted({v for p in rows.values() for mon in p for v in mon})
 require(kept==remaining,'complete retained coordinates')
 require(sorted(rows)==certificate['retained_original_rows'],'complete retained residuals')
 require(certificate['unconstrained_removed']==[],'no unconstrained deletion')
 require(set(kept)|dead==set(range(len(parent['variables']))),'every input coordinate accounted for')
 remap={v:j for j,v in enumerate(kept)}
 expected=[{'label':parent['residuals'][i]['label'],'terms':[[c,[remap[v] for v in mon]] for mon,c in sorted(rows[i].items())]} for i in sorted(rows)]
 require(expected==child['residuals'],'all child residuals replay exactly')
 require(child['variables']==[parent['variables'][v] for v in kept],'all child metadata replay exactly')
 return len(dead)

def verify_quartic(child,expanded):
 total={}
 for row in child['residuals']:
  p=poly(row['terms']);require(max(map(len,p),default=0)<=2,'quadratic source row');total=plus(total,mul(p,p))
 require(terms(total)==expanded['terms'],'all expanded quartic coefficients')
 require(expanded['variables']==len(child['variables']),'quartic variable count')
 m={'variables':len(child['variables']),'quadratic_rows':len(child['residuals']),'exact_degree':max(map(len,total)),'expanded_monomials':len(total),'max_abs_expanded_coefficient':max(map(abs,total.values())),'max_abs_row_coefficient':max(abs(c) for r in child['residuals'] for c,_ in r['terms'])}
 require(m['exact_degree']==4,'attained quartic degree')
 require(all(child['metrics'][k]==v for k,v in m.items()),'every advertised metric')
 return m

def expect_rejection(f,label):
 try:f()
 except ValueError:return label
 raise ValueError('failed corruption control: '+label)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=pathlib.Path,default=PACKET/'INDEPENDENT_CHECK.json');args=ap.parse_args()
 old=load(SOURCE/'parent.json');od=load(SOURCE/'domain.json');new=load(PACKET/'parent.json');nd=load(PACKET/'domain.json')
 require(sha(SOURCE/'parent.json')==nd['source_parent_sha256'],'whole pinned75 parent bytes')
 require(sha(SOURCE/'domain.json')==nd['source_domain_sha256'],'whole pinned75 domain bytes')
 boundary=verify_domain(old,od,new,nd)
 reports={}
 for path in sorted(PACKET.glob('support*/equation.json')):
  child=load(path);cert=load(path.with_name('projection.json'));expanded=load(path.with_name('polynomial.json'))
  count=verify_projection(new,child,cert);metrics=verify_quartic(child,expanded)
  reports[path.parent.name]={'metrics':metrics,'unique_signed_restorations':count,'equation_sha256':sha(path),'polynomial_sha256':sha(path.with_name('polynomial.json'))}
  print(path.parent.name,metrics,flush=True)
 selected=PACKET/'support8_default';child=load(selected/'equation.json');cert=load(selected/'projection.json');expanded=load(selected/'polynomial.json')
 bad_domain=copy.deepcopy(nd);bad_domain['guards'][-1]['predicate']['terms'][0][0]=2
 bad_projection=copy.deepcopy(cert);bad_projection['steps'][0]['restoration'][0][0]+=1
 bad_quartic=copy.deepcopy(expanded);bad_quartic['terms'][0][0]+=1
 controls=[expect_rejection(lambda:verify_domain(old,od,new,bad_domain),'changed product coefficient'),expect_rejection(lambda:verify_projection(new,child,bad_projection),'changed integer restoration'),expect_rejection(lambda:verify_quartic(child,bad_quartic),'changed quartic coefficient')]
 result={'status':'PASS','optimized_python':not __debug__,'domain_boundary':boundary,'profiles':reports,'rejected_corruptions':controls,'scope':'Exact domain identities, complete integral inverse maps, and coefficient expansion. Ordinary equal-sum sign lemma proves equivalence to pinned75-guard parent; inherited Con(ZFC) calibration is cited, not newly formalized.'}
 args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_bytes(bytesof(result));print(json.dumps({'status':'PASS','profiles':len(reports),'corruptions_rejected':len(controls)},indent=2))
if __name__=='__main__':main()
