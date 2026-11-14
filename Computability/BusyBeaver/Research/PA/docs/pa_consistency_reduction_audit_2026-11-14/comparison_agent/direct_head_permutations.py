#!/usr/bin/env python3
"""Direct head-parameter substitutions in the two supplied 196 AX grammars.

This preserves each binary association, prefix, gate and trailing commands.
Only occurrences of D,H,A in each of six independently parameterized axiom
heads change. Physical allocation and local folds are checked separately.
"""
from pathlib import Path
import argparse,itertools,json,sys,time,collections
BASE=Path(__file__).resolve().parent
SEARCH=BASE/'selected_sources/pa_consistency_comparison_and_new196_2026-11-13/pa_consistency_research/axioms/search'
sys.path.insert(0,str(SEARCH))
import support as s
sys.path.insert(0,str(BASE.parent/'proof_agent'))
import axiom_variants as v
pair=(s.INC,s.INC);quad=(pair,pair)
s.c.MACROS[pair]=99;s.c.MACROS[quad]=190
ATOMS={'D':'node55','H':'node58','A':'node70'}
HEAD_LENGTHS=[len(v.emit(x)) for x in v.HEADS]
PREFIX_LEN=len(v.PREFIX)
PERMS=list(itertools.permutations('DHA'))

def leaves(t):
 if s.c.isnode(t):return leaves(t[0])+leaves(t[1])
 return [t]

def transform(t,perms):
 maps=[dict(zip(ATOMS.values(),[ATOMS[a] for a in PERMS[k]])) for k in perms]
 bounds=[PREFIX_LEN]
 for n in HEAD_LENGTHS:bounds.append(bounds[-1]+n)
 def rec(t,j):
  if s.c.isnode(t):
   a,j=rec(t[0],j);b,j=rec(t[1],j);return (a,b),j
  for h in range(6):
   if bounds[h]<=j<bounds[h+1]:return maps[h].get(t,t),j+1
  return t,j+1
 return rec(t,0)[0]

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=46656)
 ap.add_argument('--families',nargs='+',default=['verified196','separate196'])
 ap.add_argument('--out',default=str(BASE/'head_permutation_results'))
 args=ap.parse_args();out=Path(args.out);out.mkdir(exist_ok=True)
 stats={};started=time.monotonic();best=62
 for family in args.families:
  t=s.c.read_grammar(SEARCH/(family+'.grammar.json'))
  token={'node49':'P','node58':'H','node55':'D','node70':'A','node65':'C','node72':'r','node75':'s','node142':'g','node150':'j',s.INC:'i',s.BREAK:'z'}
  word=''.join(token[x] for x in leaves(t));assert word.startswith(v.PREFIX+''.join(map(v.emit,v.HEADS)))
  stats[family]={'attempted':0,'matching_bound_hist':collections.Counter(),'best_effective_AX':62,'simultaneous_checks':0,'candidates':[]}
  stat=stats[family]
  for k,perms in enumerate(itertools.product(range(6),repeat=6)):
   if k>=args.limit:break
   nt=transform(t,perms);rows,index,shape=s.c.build(nt);ops=s.c.opportunities_fast(rows,shape)
   bound=len(shape)-len(s.c.max_matching(ops));stat['attempted']+=1;stat['matching_bound_hist'][bound]+=1
   if bound<=best:
    chosen=s.bestcompatible_all(rows,shape);cost=len(shape)-len(chosen);stat['simultaneous_checks']+=1
    if cost<stat['best_effective_AX']:
     stat['best_effective_AX']=cost;stat['best_permutations']=perms
    if cost<best:
     best=cost;name=family+'_'+str(k)
     item={'family':family,'permutations':perms,'effective_AX':cost,'shape_count':len(shape),'folds':chosen,'grammar':s.encode(nt)}
     (out/(name+'.json')).write_text(json.dumps(item,indent=2)+'\n')
     print('BEST',name,cost,len(shape),len(chosen),round(time.monotonic()-started,2),flush=True)
    if cost<=61:
     folded,alias=s.apply(rows,chosen);sites,ins,contracts=s.c.source(nt)
     result=s.c.validate(folded,contracts);item={'family':family,'index':k,'permutations':perms,'effective_AX':cost,'validation':result}
     stat['candidates'].append(item);print('FULL',item,flush=True)
     (out/(family+'_'+str(k)+'.validation.json')).write_text(json.dumps(item,indent=2)+'\n')
     if result['ok']:
      (out/'candidate195.native.tm').write_text('#! start 74\n'+''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n' for (q,b),(w,d,n) in sorted(folded.items())))
      (out/'candidate195.sites.json').write_text(json.dumps(sites)+'\n')
      print('FOUND PASSING RUNTIME CANDIDATE; startup and logic binding still required',flush=True)
      (out/'receipt.json').write_text(json.dumps(stats,indent=2)+'\n');return
   if (k+1)%1000==0:
    print(family,k+1,'best',best,'seconds',round(time.monotonic()-started,2),flush=True)
  print('FAMILY',family,stat['attempted'],dict(stat['matching_bound_hist']),flush=True)
  (out/'receipt.json').write_text(json.dumps({'stats':stats,'seconds':time.monotonic()-started,'scope':'Direct substitutions only; each head independently permutes its three numeric parameters. Fixed association and gate. Matching bounds are used only to discard impossible simultaneous pairwise folds under the imported template.'},indent=2)+'\n')

if __name__=='__main__':main()
