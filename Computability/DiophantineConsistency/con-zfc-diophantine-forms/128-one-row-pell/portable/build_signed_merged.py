#!/usr/bin/env python3
"""Signed compiler for the full-root merged cap, with staged sign recovery."""
from pathlib import Path
from hashlib import sha256
import argparse,copy,json,sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'parent'))
import terminal_elimination as E
sys.path.insert(0,str(HERE/'incoming/round15/direct'))
import build_signed as S
from translate_coordinates import translate

def need(c,m):
 if not c:raise ValueError(m)
def put(p,o):p.write_bytes(E.canonical_bytes(o))
def V(i):return {(i,):1}
def closure(proof,seed):
 known=set(seed);steps=[]
 for s in proof['proof_steps']:
  if set(s['dependencies'])<=known:known.add(s['variable']);steps.append(s)
 return known,steps

def make(source,defer_quotients=False,pair_guards=False):
 need(sha256(E.canonical_bytes(source)).hexdigest()=='8f0cb6b55606cd2a54e5a579c008e9d37573297ce6e38f40ed50b68bf1df9363','the reviewed full-root natural source is required; other architectures need a separate proof and binding')
 e=copy.deepcopy(source);e.pop('metrics',None);e['domain']='unrestricted integers';e['variant']+=':signed_merged_cap'
 names={v['name']:i for i,v in enumerate(e['variables'])}
 xs=[i for n,i in names.items() if n.startswith('index') and n[5:6].isdigit() and n.endswith('.X')]
 ys=[i for n,i in names.items() if n.startswith('index') and n[5:6].isdigit() and n.endswith('.Y')]
 caprows=[r for r in e['residuals'] if r['label']=='index_cap.merged_bound_errors']
 need(len(caprows)==1,'one full-root merged cap row required')
 cap=E.normalize(caprows[0]['terms'])
 need(len(xs)==len(ys)==15,'fifteen principal seed pairs required')
 for x,y in zip(xs,ys):
  need(cap.get((x,x))==-1 and cap.get((x,))==2 and cap.get((y,y))==-1,'full (X-1)^2 and (Y-k)^2 cap terms required')
 allsign=copy.deepcopy(e)
 for v in allsign['variables']:v['kind']='witness'
 deferred=[i for n,i in names.items() if (n.startswith('pow') and n.endswith('.quotient')) or n.endswith('.modular_quotient') or (n.startswith('base') and n.endswith('.T')) or n=='modular.root_quotient'] if defer_quotients else []
 pairs=[];paircoords=[];outputslacks=[]
 if pair_guards:
  for i,r in enumerate(e['residuals']):
   if not r['label'].endswith('remainder_bound'):continue
   p=E.normalize(r['terms'])
   matches=[m[0] for m,c in p.items() if len(m)==1 and c==-1 and e['variables'][m[0]]['name'].endswith(('.modular_remainder','.modular_rslack','fact0.remainder','fact0.slack'))]
   need(len(matches)==2,'expected complete remainder pair')
   denom=E.normalize(E.as_terms(p)+[[1,[matches[0]]],[1,[matches[1]]],[1,[]]])
   pairs.append({'row':i,'label':r['label'],'pair':matches,'denominator':E.as_terms(denom)})
   paircoords+=matches
  need(len(pairs)==12 and len(set(paircoords))==24,'exact12disjointpairs')
  outputslacks=[i for n,i in names.items() if n.endswith('.modular_oslack')]
  need(len(outputslacks)==1,'one exact binomial output slack')
 axioms=xs+ys+deferred+paircoords+outputslacks
 proof=S.inference(allsign,set(),axioms)
 # A remainder pair may syntactically imply the sign of its denominator.
 # The paired predicate is interpreted only AFTER powers. Retain every
 # exact-power output sign independently to prevent that bootstrap cycle.
 added=[]
 if pair_guards:
  required_outputs={i for n,i in names.items() if n.startswith('pow') and n.endswith('.output')}
  added=sorted(required_outputs-set(proof['guard_indices']))
  proof['guard_indices']=sorted(set(proof['guard_indices'])|required_outputs)
 prefix,prefixsteps=closure(proof,set(proof['guard_indices']))
 # Cap, semantic arithmetic interface, and all output/remainder quotients
 # precede orientation. Gate domains not used by orientation are postponed.
 prereq={i for n,i in names.items() if n.startswith('index_cap.')}
 prereq|={names[n] for n in ('shared.W','shared.lower_A','shared.A_slack','shared.Zminus1')}
 prereq|={i for n,i in names.items() if (n.startswith('pow') and n.endswith(('.output','.quotient'))) or '.modular_' in n}
 prereq-=set(deferred+paircoords+outputslacks)
 need(prereq<=prefix,'prefix sign deficit: '+str([e['variables'][i]['name'] for i in sorted(prereq-prefix)]))
 finalknown,post=closure(proof,set(proof['guard_indices'])|set(axioms))
 need(set(range(len(e['variables'])))<=finalknown,'all source natural signs recovered')
 guarded=copy.deepcopy(e)
 for v in proof['guard_indices']:
  a,b,c=range(len(guarded['variables']),len(guarded['variables'])+3)
  guarded['variables'] += [{'name':'nonnegative.'+str(v)+'.'+x,'kind':'integer_guard'} for x in ('a','b','c')]
  p=E.normalize([[1,[v]],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]])
  guarded['residuals'].append({'label':'nonnegative.'+str(v),'terms':E.as_terms(p)})
 for pr in pairs:
  a,b,c=range(len(guarded['variables']),len(guarded['variables'])+3)
  guarded['variables'] += [{'name':'pair.'+pr['label']+'.'+x,'kind':'integer_guard'} for x in ('a','b','c')]
  p=E.normalize([[1,pr['pair']],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]])
  pr['guard_row']=len(guarded['residuals']);pr['auxiliary']=[a,b,c]
  guarded['residuals'].append({'label':'pair.'+pr['label'],'terms':E.as_terms(p)})
 cert={'schema':'signed_merged_cap_v1','seed_X':xs,'seed_Y':ys,'deferred_quotients_and_moduli':deferred,'paired_remainders':pairs,'deferred_output_slacks':outputslacks,'prefix_added_output_guards':added,'prefix_required':sorted(prereq),'prefix_known':sorted(prefix),'prefix_steps':prefixsteps,'signs':proof,'theorem_stages':['positive frame and natural anchor','one-row cap gives canonical seed pairs','recover six exact powers and positive moduli; quotient signs from positive residues','recover remainder pairs from positive denominator sums','recover modular quotient signs','restore every source coordinate sign']}
 return e,guarded,cert

def main():
 default_source=HERE/'integer378/natural_raw/equation.json'
 if not default_source.exists():default_source=HERE/'fullroot_modular_shell16/raw/equation.json'
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=default_source);ap.add_argument('--out',type=Path,default=HERE/'rebuilt/integer378');ap.add_argument('--cap',type=int,default=16);ap.add_argument('--defer-quotients',action='store_true');ap.add_argument('--pair-guards',action='store_true');a=ap.parse_args()
 source=json.loads(a.source.read_text());e,g,c=make(source,a.defer_quotients,a.pair_guards)
 out,pc,metrics=E.optimize(g,max_support=a.cap);receipt=E.verify(g,out,pc)
 shifts={i:-1 for i,v in enumerate(out['variables']) if v['name'].startswith('crt.encoded') or v['name'] in ('t0','M0') or v['name'].endswith('minus1')}
 final=translate(out,shifts);expanded=E.expand(final)
 fm={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(m) for _,m in expanded['terms']),'monomials':len(expanded['terms']),'height':max(abs(c) for c,_ in expanded['terms']),'scalar_guards':len(c['signs']['guard_indices']),'product_guards':len(c['paired_remainders'])}
 a.out.mkdir(parents=True,exist_ok=True)
 for n,o in [('source.json',e),('guarded.json',g),('signed_certificate.json',c),('projected.json',out),('projection_certificate.json',pc),('equation.json',final),('expanded_polynomial.json',expanded),('METRICS.json',fm),('PROJECTION_METRICS.json',metrics|receipt),('translation_certificate.json',{'shifts':sorted(shifts.items()),'convention':'old=new+shift'})]:put(a.out/n,o)
 print(json.dumps(fm|{'raw_variables':len(g['variables']),'raw_rows':len(g['residuals']),'projected':receipt},indent=2))

if __name__=='__main__':main()
