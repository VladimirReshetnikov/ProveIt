#!/usr/bin/env python3
"""Validate closed-subblock AX grammar candidates against pinned primary PA194.
All source instruction ordinals and resolved successors must match, not merely
physical leaf labels. Then reconstruct a literal reader graph using verified
existing pairs and find/check a compatible simultaneous local-fold witness.
This checker rejects contextual physical-label collisions in source identity.
"""
from pathlib import Path
import argparse,hashlib,itertools,json,sys,time
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'reference/pa194'
sys.path.insert(0,str(BASE/'construction'))
import compiler as c
from build194 import read_table,table_text,apply_folds,check_local_folds,dense_table,startup


def main():
 ap=argparse.ArgumentParser();ap.add_argument('grammar',type=Path);ap.add_argument('--dictionary',type=Path,default=HERE.parent/'grammar/closure_dictionary.json');ap.add_argument('--output',type=Path);ap.add_argument('--target',type=int,default=193);ap.add_argument('--quick',action='store_true');args=ap.parse_args()
 if not __debug__:raise RuntimeError('Assertions are certificate checks; disable -O.')
 t=c.read_grammar(args.grammar);baseline=c.read_grammar(BASE/'construction/source/pa194.grammar.json')
 sites,instructions,contracts=c.source(t);oldsites,oldins,oldcontracts=c.source(baseline)
 newword=[s[1:] for s in sites];oldword=[s[1:] for s in oldsites]
 assert newword==oldword,('Primitive source word changed',len(sites),len(oldsites),next((i for i,(x,y) in enumerate(zip(newword,oldword)) if x!=y),None))
 assert instructions==oldins,'Ordinal successor graph changed'
 assert len(sites)==3673 and len(contracts)==4780
 sys.path.insert(0,str(BASE/'verification/independent/reference'))
 import source_language as sl
 opcode={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
 mapped=[[''.join(map(str,p)),opcode[o],a] for p,o,a in sites]
 graph,_=sl.graph_arithmetic(mapped);assert graph==sl.graph_intervals(mapped)
 names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
 assert [[names[e[0]]]+e[1:]+targets for e,targets in graph]==json.loads(json.dumps(instructions))
 print('SOURCE IDENTITY PASS',len(sites),'sites',len(contracts),'contracts',flush=True)
 dictionary=json.loads(args.dictionary.read_text());labels=dictionary['labels'];oldrows,_=c.machine()
 pairs={tuple(v[:2]):v[2] for v in dictionary['pairs']}
 for (qa,qb),q in pairs.items():assert oldrows[q,0]==(0,True,qa) and oldrows[q,1]==(1,True,qb)
 raw={k:v for k,v in oldrows.items() if k[0]<1300};shape={};index={};intern={}
 inc=('leaf','inc',1)
 def build(t):
  if t==inc:return 61
  if t==c.BREAK:return -1
  if isinstance(t,str):return labels[t]
  assert c.isnode(t)
  a,b=build(t[0]),build(t[1])
  if (a,b) in pairs:return pairs[a,b]
  if (a,b) in intern:return intern[a,b]
  q=2000+len(shape);shape[q]=t;index[t]=q;intern[a,b]=q
  for bit,u in enumerate((a,b)):raw[q,bit]=(0,False,302) if u==-1 else (bit,True,u)
  return q
 root=build(t);raw[101,1]=(1,True,root)
 nraw=len(raw)//2;needed=max(0,nraw-args.target)
 print('RAW',nraw,'READERS',len(shape),'FOLDS NEEDED',needed,flush=True)
 ops=c.opportunities_fast(raw,shape)
 degree={a:sum(x==a for x,y,o in ops) for a,b,o in ops};ops.sort(key=lambda x:(degree[x[0]],x[0],x[1]))
 tried=0;winner=None;certificate=None
 def recurse(i,used,chosen):
  nonlocal tried,winner,certificate
  if len(chosen)>=needed:
   tried+=1
   folded,aliases=apply_folds(raw,chosen)
   try:cert=check_local_folds(raw,folded,aliases,chosen)
   except (AssertionError,KeyError):return False
   winner=(folded,aliases,chosen);certificate=cert;return True
  if len(chosen)+len(ops)-i<needed:return False
  rem=[(a,b,o) for a,b,o in ops[i:] if a not in used and b not in used]
  if len(chosen)+len(c.max_matching(rem))<needed:return False
  for j in range(i,len(ops)):
   a,b,opts=ops[j]
   if a in used or b in used:continue
   for acts in itertools.product(*opts):
    if recurse(j+1,used|{a,b},chosen+[[a,b,acts]]):return True
  return False
 assert recurse(0,set(),[]),('No compatible fold witness to target',args.target,'raw',nraw,'ordinary matching',len(c.max_matching(ops)),'tried',tried)
 folded,aliases,folds=winner;n=len(folded)//2
 dense,order=dense_table(folded,n)
 assert all(folded[q,b]==oldrows[q,b] for q in c.BOXSTATES for b in (0,1))
 boot=startup(folded,sites[25][0])
 print('STRUCTURE PASS',n,'states','BOOT',boot['steps'],'LOCAL',len(certificate['cases']),flush=True)
 result=c.validate(folded,contracts) if not args.quick else None
 if not args.quick:assert result['ok'],result
 receipt={'working_states':n,'raw_states':nraw,'reader_states':len(shape),'fold_count':len(folds),'primitive_word_identical':True,'source_graph_identical':True,'independent_cfg_resolvers_agree':True,'source_sites':len(sites),'contracts':len(contracts),'startup':boot,'local_cases':len(certificate['cases']),'symbolic_runtime':result,'complete_physical_table_checked':not args.quick,'native_sha256':hashlib.sha256(table_text(folded).encode()).hexdigest(),'dense_sha256':hashlib.sha256(table_text(dense).encode()).hexdigest(),'grammar_sha256':hashlib.sha256(args.grammar.read_bytes()).hexdigest(),'new_kernel_proof':False}
 if args.output:
  args.output.mkdir(parents=True,exist_ok=True)
  for name,table in [('native.tm',folded),('machine.tm',dense),('raw.native.tm',raw)]: (args.output/name).write_text(table_text(table))
  for name,obj in [('labels.json',order),('folds.json',folds),('sites.json',mapped),('instructions.json',instructions),('local_certificate.json',certificate),('verification.json',receipt)]: (args.output/name).write_text(json.dumps(obj,indent=2)+'\n')
  (args.output/'grammar.json').write_bytes(args.grammar.read_bytes())
 print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
