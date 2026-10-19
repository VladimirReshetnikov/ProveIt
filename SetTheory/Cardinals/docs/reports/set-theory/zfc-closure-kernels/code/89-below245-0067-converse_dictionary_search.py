#!/usr/bin/env python3
"""Search involution variants by joint old-dictionary token matching and DP."""
import argparse,collections,importlib.util,json,random,sys,time
from pathlib import Path
P=argparse.ArgumentParser();P.add_argument('--package',type=Path,required=True);P.add_argument('--source',type=Path,required=True);P.add_argument('--parts',type=Path,required=True);P.add_argument('--output',type=Path,required=True);P.add_argument('--trials',type=int,default=1000);P.add_argument('--seed',type=int,default=10367219);P.add_argument('--anchored',action='store_true');P.add_argument('--variant');P.add_argument('--shuffle-rows',action='store_true')
A=P.parse_args();A.output.mkdir(parents=True,exist_ok=True)
sys.argv=['permutation_search','--package',str(A.package),'--parts',str(A.parts),'--output',str(A.output/'control'),'--trials','0']
sp=importlib.util.spec_from_file_location('base',Path(__file__).with_name('permutation_search.py'));b=importlib.util.module_from_spec(sp);sp.loader.exec_module(b)
source=json.loads(A.source.read_text());semantic=json.loads((A.package/'research/architecture/semantic_rows.json').read_text());exp=semantic['fine_atom_expansions'];expand=lambda w:tuple(x for c in w for x in exp[c]);rng=random.Random(A.seed);began=time.monotonic()
patterns=collections.defaultdict(list)
for w in [*b.g,*b.symbols]:
 if w!=b.oldroot:
  ex=expand(w);patterns[ex[0]].append((w,ex))
specs=source['anchored_variants']if A.anchored else source['variants']
variants=sorted(specs)if A.anchored else ['converse_equality','both_converses','converse_membership'];best={v:999 for v in variants};hist=[];counts={v:collections.Counter()for v in variants}
if A.variant:variants=[A.variant];best={A.variant:999};counts={A.variant:collections.Counter()}
elite={v:tuple(range(8))for v in variants};orders=set()
for i in range(A.trials):
 v=variants[i%len(variants)];spec=specs[v];order=elite[v]
 if A.shuffle_rows and i:
  order=list(order)
  if i%10==0:rng.shuffle(order)
  else:
   j,k=rng.sample(range(8),2);order[j],order[k]=order[k],order[j]
  order=tuple(order)
 orders.add((v,order))
 raw=spec['raw_AX_prefix']+''.join(spec['raw_AX_rows'][j]for j in order)+spec['raw_AX_tail']if A.shuffle_rows else spec['raw_AX_word']
 target=expand(raw);alpha=10**rng.uniform(-2,.1)
 weight={w:1+alpha*len(b.deps(w)-b.base)+(rng.random()-.5)*.1 for w in b.g if w!=b.oldroot}
 costs=[float('inf')]*(len(target)+1);choices=[None]*len(target);costs[-1]=0
 for j in range(len(target)-1,-1,-1):
  for w,ex in patterns[target[j]]:
   k=j+len(ex)
   if target[j:k]!=ex:continue
   z=costs[k]+weight.get(w,1)
   if z<costs[j]:costs[j]=z;choices[j]=(w,k)
 toks=[];j=0
 while j<len(target):w,j=choices[j];toks.append(w)
 result=b.assemble_tokens(toks)
 if result is None:counts[v]['unparseable']+=1;continue
 gram,nt=result;score=len(gram);counts[v][score]+=1
 if score<best[v]:
  best[v]=score;newroot=''.join(toks);assert expand(newroot)==target
  dd=dict(b.d);dd.update(status='ABSTRACT_CONVERSE_GRAMMAR_ONLY',rules_count=score,rules=[[w,*gram[w]]for w in sorted(gram)],roots=[newroot if w==b.oldroot else w for w in b.d['roots']],root_word_overrides={'76':newroot},original_AX_word=b.oldroot,modified_AX_word=newroot,calculus_variant=v,source_variant=spec,axiom_push_order=[8-j for j in order],search_method='expanded_dictionary_matching_plus_rank_bounded_interval_dynamic_programming');dd.pop('properties',None)
  (A.output/f'{v}_best.json').write_text(json.dumps(dd,indent=2)+'\n');rec=dict(trial=i,variant=v,rules=score,tokens=nt,AX_calls=len(newroot),axiom_push_order=[8-j for j in order],seconds=time.monotonic()-began);hist.append(rec);elite[v]=order;print('BEST',rec,flush=True)
 if i%50==0:print('progress',i,'best',best,'seconds',time.monotonic()-began,flush=True)
report=dict(status='BOUNDED_SOURCE_SEARCH',trials=A.trials,best=best,counts={v:dict(c)for v,c in counts.items()},history=hist,seed=A.seed,distinct_variant_order_pairs=len(orders),seconds=time.monotonic()-began);(A.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
