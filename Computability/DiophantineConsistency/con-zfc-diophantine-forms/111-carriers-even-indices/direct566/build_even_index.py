#!/usr/bin/env python3
"""Separate even-index, square-output arithmetic prototype; proof accompanies release."""
import argparse, copy, hashlib, importlib.util, json, pathlib, sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
SOURCE=HERE/'source/signsharing'
CERT=HERE/'source/call_certificate.json'
RAW=HERE/'source/raw_builder.json'
OUT=HERE
ENGINE=HERE/'tools/terminal_elimination.py'
CHECK_ONLY=False
DROP_SCALARS=[825,891,934,964,994,1024,1054,1084,1114,1144,1174]
def need(b,s):
 if not b:raise ValueError(s)
def load(p):return json.loads(p.read_bytes())
def enc(v):return(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()
def save(p,v):
 data=enc(v)
 if CHECK_ONLY:
  if p.read_bytes()!=data:raise ValueError('deterministic rebuild differs: '+str(p))
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def module(p):
 s=importlib.util.spec_from_file_location('pinned_even_optimizer',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def generate_parent():
 old=load(SOURCE/'parent.json');domain=load(SOURCE/'domain.json');cert=load(CERT);raw=load(RAW)
 eq={'schema':old['schema'],'domain':old['domain'],'variant':'even_index_square_output56_raw','variables':copy.deepcopy(old['variables'][:1259]),'residuals':copy.deepcopy(old['residuals'][:1177])}
 edits={}
 def replace(row,newterms,reason):
  need(row not in edits,'each changed row assigned once')
  edits[row]={'row':row,'before':copy.deepcopy(eq['residuals'][row]),'after':{'label':eq['residuals'][row]['label'],'terms':newterms},'reason':reason}
  eq['residuals'][row]['terms']=newterms
 for call in cert['power_calls']:
  m=call['output'];candidates=[item['row'] for item in call['cut']['row_combination'] if [-1,[m]] in eq['residuals'][item['row']]['terms']]
  need(len(candidates)==1,'unique raw output addition')
  row=candidates[0];terms=[[c,([m,m]if mon==[m]else mon)]for c,mon in eq['residuals'][row]['terms']]
  replace(row,terms,'square output '+str(call['index']))
 for seed in cert['seeds']:
  k=seed['aliases']['k'];row=seed['rows']['R_mod_4Y']-1
  need([-1,[k]]in eq['residuals'][row]['terms'],'index remainder precursor')
  terms=[[-2 if mon==[k]else c,mon]for c,mon in eq['residuals'][row]['terms']]
  replace(row,terms,'double seed exponent '+str(k))
 replace(856,[[1,[921]],[-2,[644,919]],[-2,[644,920]],[1,[670]]],'two-step derived Pell abscissa')
 replace(857,[[1,[922]],[-2,[919]],[-2,[650,671]],[1,[671]]],'two-step derived Pell ordinate')
 outputs={c['output']for c in cert['power_calls']}
 for row in range(1134,1176):
  before=eq['residuals'][row]['terms']
  terms=[[c,([mon[0],mon[0]]if len(mon)==1 and mon[0]in outputs else mon)]for c,mon in before]
  if terms!=before:replace(row,terms,'square output in common frame')
 replace(1176,[[1,[643]],[-2,[1258]]],'double entire common frame')
 predicates=[g['predicate']for g in domain['guards']if not(g['predicate']['kind']=='retained_scalar'and g['predicate']['raw_variables'][0]in DROP_SCALARS)and g['predicate']['kind']!='paired_index_slacks']
 need(len(predicates)==56 and len(edits)==60,'exact twelve removed guards and60 changed rows')
 guards=[]
 for j,p in enumerate(predicates):
  ids=list(range(len(eq['variables']),len(eq['variables'])+3));a,b,c=ids
  eq['variables'].extend({'kind':'nonnegative_guard','name':f'even_guard.{j}.{z}'}for z in ['a','b','c'])
  eq['residuals'].append({'label':f'even_guard.{j}','terms':copy.deepcopy(p['terms'])+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]})
  guards.append({'predicate':p,'auxiliary':ids})
 data={'parent68_sha256':sha(SOURCE/'parent.json'),'domain68_sha256':sha(SOURCE/'domain.json'),'raw_builder_sha256':sha(RAW),'old_call_certificate_sha256':sha(CERT),'drop_scalar_guards':DROP_SCALARS,'drop_product_guard':[674,861],'guards':guards,'edits':[edits[i]for i in sorted(edits)],'power_calls':cert['power_calls'],'seeds':cert['seeds'],'frame_arguments':cert['frame_arguments'],'square_output_indices':sorted(outputs),'frame_formula':[[1,[643]],[-4,[]]]+[[-2,[v,v]if v in outputs else[v]]for v in cert['frame_arguments']],'derived_pair':{'source':[670,671],'target':[921,922],'old_exponent':4,'new_semantic_exponent':5,'step':2,'rows':[852,853,854,855,856,857]},'scope':'Ordinary even-index/square-output proof required; exact finite changes and integer projections are recorded separately.'}
 return eq,data

def contract_frame(eq,engine):
 rows={i:engine.normalize(r['terms'])for i,r in enumerate(eq['residuals'])};steps=[];deleted=set()
 for row in range(1175,1133,-1):
  v=1217+(row-1134);f=engine.candidate(rows[row],v,False);need(f is not None,'explicit frame monic definition')
  for j,p in list(rows.items()):
   if j!=row and any(v in mon for mon in p):
    q=engine.substitute(p,v,f);need(engine.degree(q)<=2,'frame substitution stays quadratic')
    if q:rows[j]=q
    else:del rows[j]
  del rows[row];deleted.add(v);steps.append({'row_id':row,'variable':v,'name':eq['variables'][v]['name'],'kind':eq['variables'][v].get('kind'),'restoration':engine.as_terms(f),'restoration_degree':engine.degree(f)})
 kept=sorted(set(range(len(eq['variables'])))-deleted);mp={v:i for i,v in enumerate(kept)}
 out=copy.deepcopy(eq);out['variables']=[eq['variables'][v]for v in kept];out['residuals']=[{'label':eq['residuals'][i]['label'],'terms':[[c,[mp[v]for v in mon]]for mon,c in sorted(p.items())]}for i,p in sorted(rows.items())]
 cert={'schema':'integer_quadratic_elimination_v1','input_sha256':hashlib.sha256(enc(eq)).hexdigest(),'output_sha256':hashlib.sha256(enc(out)).hexdigest(),'steps':steps,'unconstrained_removed':[],'retained_original_variables':kept,'retained_original_rows':sorted(rows)}
 engine.verify(eq,out,cert)
 return out,cert

def main():
 global CHECK_ONLY
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args();CHECK_ONLY=args.check
 engine=module(ENGINE);parent,ledger=generate_parent();save(OUT/'parent.json',parent);save(OUT/'ledger.json',ledger)
 frame,fc=contract_frame(parent,engine);save(OUT/'frame_parent.json',frame);save(OUT/'frame_projection.json',fc)
 census={}
 for name,cap,affine in [('support8_default',8,None),('support16_affine2',16,2),('support8_affine2',8,2)]:
  child,projection,metrics=engine.optimize(frame,max_support=cap,affine_support=affine);engine.verify(frame,child,projection)
  need(projection['unconstrained_removed']==[],'every removed coordinate uniquely restored')
  save(OUT/name/'equation.json',child);save(OUT/name/'projection.json',projection);save(OUT/name/'polynomial.json',engine.expand(child))
  census[name]={'metrics':child['metrics'],'unique_signed_restorations':42+len(projection['steps']),'support':cap,'affine_support':affine};print(name,child['metrics'],flush=True)
 save(OUT/'CENSUS.json',census)
if __name__=='__main__':main()
