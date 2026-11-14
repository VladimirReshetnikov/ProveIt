#!/usr/bin/env python3
"""Exhaust all 720 six-head orders in each fixed 190/191-token grammar."""
from pathlib import Path
import itertools,json,collections,time
from anneal_head_variants import s,SEARCH,TOKEN,leaves,HEAD_END,identity,reword,emitted,BASE

def main():
 started=time.monotonic();results={}
 for family in ('verified196','separate196'):
  t=s.c.read_grammar(SEARCH/(family+'.grammar.json'))
  word=''.join(TOKEN[x]for x in leaves(t));tail=word[HEAD_END:]
  histogram=collections.Counter();minimum=10**9;minimum_orders=[]
  for order in itertools.permutations(range(6)):
   meta=identity();meta['order']=list(order);nt=reword(t,emitted(meta,tail))
   rows,_,shape=s.c.build(nt);ops=s.c.opportunities_fast(rows,shape)
   bound=len(shape)-len(s.c.max_matching(ops));histogram[bound]+=1
   if bound<minimum:minimum=bound;minimum_orders=[order]
   elif bound==minimum:minimum_orders.append(order)
   if bound<=61:
    chosen=s.bestcompatible_all(rows,shape);cost=len(shape)-len(chosen)
    print('PROMISING',family,order,bound,cost,flush=True)
    if cost<=61:
     folded,_=s.apply(rows,chosen);_,_,contracts=s.c.source(nt)
     result=s.c.validate(folded,contracts)
     (BASE/(family+'_order_candidate.json')).write_text(json.dumps({'order':order,'cost':cost,'grammar':s.encode(nt),'folds':chosen,'runtime':result},indent=2)+'\n')
  results[family]={'tested':720,'minimum_matching_bound':minimum,'minimum_orders':minimum_orders,'matching_bound_histogram':dict(histogram)}
  print(family,minimum,len(minimum_orders),flush=True)
 results['elapsed_seconds']=time.monotonic()-started
 results['scope']='All direct fixed-association head-order substitutions. No marker penalty is added to the matching lower bound. No assertion about arbitrary association/rewrites/machine architectures.'
 (BASE/'head_order_direct.json').write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':main()
