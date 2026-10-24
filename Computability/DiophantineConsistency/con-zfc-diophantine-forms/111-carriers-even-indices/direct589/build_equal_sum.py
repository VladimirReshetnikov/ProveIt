#!/usr/bin/env python3
"""Build exact signed quartics after sharing orientation of equal-sum pairs."""
import argparse, copy, hashlib, importlib.util, json, pathlib, sys, time
sys.dont_write_bytecode=True

HERE=pathlib.Path(__file__).resolve().parent
BASE=HERE/'source'
ENGINE=HERE/'tools/terminal_elimination.py'
OUT=HERE
CHECK_ONLY=False
GROUPS=[
 {'denominator':547,'pairs':[(549,550,526),(562,563,537)]},
 {'denominator':574,'pairs':[(576,577,547),(585,586,553),(593,594,559),(601,602,565)]},
 {'denominator':608,'pairs':[(610,611,572),(619,620,578)]},
 {'denominator':626,'pairs':[(628,629,585),(637,638,591)]},
]
def encoded(v):return (json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()
def save(path,v):
 data=encoded(v)
 if CHECK_ONLY:
  if path.read_bytes()!=data:raise ValueError('deterministic rebuild differs: '+str(path))
 else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_bytes())

def parent(anchors=(0,0,0,0)):
 old=load(BASE/'parent.json');dom=load(BASE/'domain.json')
 n=dom['baseline_body_variables'];nr=dom['baseline_body_rows']
 if not(n==1259 and nr==1177):raise ValueError('source body shape')
 changed=[]
 for g,anchor in zip(GROUPS,anchors):
  for j,(r,s,start) in enumerate(g['pairs']):
   if j!=anchor:changed.append((r,s,start,g['denominator'],g['pairs'][anchor]))
 changed.append((123,564,540,530,(91,537,518)))
 removed={v for r,s,*_ in changed for v in (r,s)}
 predicates=[g['predicate'] for g in dom['guards'] if not(g['predicate']['kind']=='retained_scalar' and g['predicate']['raw_variables'][0] in removed)]
 if len(predicates)!=61:raise ValueError('retained predicate count')
 for r,s,*_ in changed:predicates.append({'kind':'equal_sum_product','raw_variables':[r,s],'terms':[[1,[r,s]]]})
 eq={k:copy.deepcopy(old[k]) for k in ('schema','domain')}
 eq.update(variant='equal_sum68_raw',variables=copy.deepcopy(old['variables'][:n]),residuals=copy.deepcopy(old['residuals'][:nr]))
 guards=[]
 for j,p in enumerate(predicates):
  ids=list(range(len(eq['variables']),len(eq['variables'])+3))
  eq['variables'].extend({'kind':'nonnegative_guard','name':f'equal_sum_guard.{j}.{s}'} for s in ['a','b','c'])
  a,b,c=ids
  eq['residuals'].append({'label':f'equal_sum_guard.{j}','terms':copy.deepcopy(p['terms'])+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]})
  guards.append({'predicate':p,'auxiliary':ids})
 certificate={'source_parent_sha256':sha(BASE/'parent.json'),'source_domain_sha256':sha(BASE/'domain.json'),'baseline_body_variables':n,'baseline_body_rows':nr,'baseline_raw_indices':dom['baseline_raw_indices'],'anchors':list(anchors),'groups':GROUPS,'changed_pairs':changed,'extra_anchor_rows':[83,84,85],'guards':guards,'retained_parent_predicates':68}
 return eq,certificate

def main():
 global CHECK_ONLY
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args();CHECK_ONLY=args.check
 spec=importlib.util.spec_from_file_location('pinned_optimizer',ENGINE);engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
 eq,domain=parent();save(OUT/'parent.json',eq);save(OUT/'domain.json',domain)
 census={}
 for name,cap,affine in [('support8_default',8,None),('support16_affine2',16,2),('support8_affine2',8,2)]:
  then=time.monotonic();child,cert,metrics=engine.optimize(eq,max_support=cap,affine_support=affine)
  engine.verify(eq,child,cert)
  if cert['unconstrained_removed']:raise ValueError('unconstrained deletion')
  save(OUT/name/'equation.json',child);save(OUT/name/'projection.json',cert);save(OUT/name/'polynomial.json',engine.expand(child))
  census[name]={'metrics':child['metrics'],'unique_signed_restorations':len(cert['steps']),'support':cap,'affine_support':affine}
  print(name,child['metrics'],round(time.monotonic()-then,3),flush=True)
 save(OUT/'CENSUS.json',census)
 print(json.dumps({'status':'PASS','engine_sha256':sha(ENGINE),'census':census},indent=2))
if __name__=='__main__':main()
