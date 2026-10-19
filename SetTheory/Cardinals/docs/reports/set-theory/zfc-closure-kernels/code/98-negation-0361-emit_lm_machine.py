#!/usr/bin/env python3
"""Emit a complete binary table and literal source sites for the LM backend.

This emitter checks exact changed-source reassociation. It does not certify
that the retained binary framework implements the new LM atom; run the
separate full frame/affine validators and exact blank check before claiming it.
"""
from pathlib import Path
from functools import cache
import argparse,json,sys,hashlib
from audit_lm_grammar import audit

def main():
 p=argparse.ArgumentParser();p.add_argument('--candidate',type=Path,required=True);p.add_argument('--backend',type=Path,required=True);p.add_argument('--fine',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 meta=json.loads(a.backend.read_text());fine=Path(a.fine or meta['fine_path']);local=audit(a.candidate,a.backend,fine);source=meta['source'];names={int(q):w for q,w in meta['names'].items()};terms=meta['terminals'];data=json.loads(a.candidate.read_text());rules={w:(l,r) for w,l,r in data['rules']};routes={(r['source'],r['read']):r['word'] for r in data['routes']}
 runtime=fine/'runtime';sys.path.insert(0,str(runtime/'code'));sys.path.insert(0,str(runtime/'reference/context246/code'));sys.path.insert(0,str(runtime/'reference/jeff/ZF/m254/tools/prog'))
 import rebuild_machines as rebuild,rmpath
 from build_source_machine import sparse_boot,check_bisimulation
 original,start=rebuild.read_table(runtime/'reference/context246/machine/zfc_prefix246_old.tm');assert start==95
 seq=set(source['sequence_states']);erased={177,74};alloc={w:q for q,w in names.items() if w in rules};available=sorted((seq|erased)-set(alloc.values()));fresh=256
 while len(available)<len(rules)-len(alloc):
  if fresh not in available and fresh not in alloc.values():available.append(fresh)
  fresh+=1
 for w in sorted(set(rules)-set(alloc)):alloc[w]=available.pop(0)
 assert alloc[names[96]]==96
 def dest(w):return source['atoms'][terms[w]]['state'] if w in terms else alloc[w]
 table={k:v for k,v in original.items() if k[0] not in seq|erased}
 for k,(w,d,t) in list(table.items()):
  if k==(58,0):table[k]=(0,'L',84)
  elif k in routes:table[k]=(w,d,alloc[routes[k]])
  elif t in seq:table[k]=(w,d,alloc[names[t]])
  else:assert t not in erased
 for word,(l,r) in rules.items():table[alloc[word],0]=(0,'R',dest(l));table[alloc[word],1]=(1,'R',dest(r))
 states={q for q,b in table};assert len(states)==len(rules)+117 and len(table)==2*len(states);assert {t for w,d,t in table.values()}-states=={254}
 (a.output/'machine_old.tm').write_text(rebuild.encode(table,95));order=[95]+sorted(states-{95});mapping={q:i for i,q in enumerate(order)}|{254:len(states)};canonical={(mapping[q],b):(w,d,mapping[t]) for(q,b),(w,d,t) in table.items()};(a.output/'machine.tm').write_text(rebuild.encode(canonical,0))
 def write(n,x):(a.output/n).write_text(json.dumps(x,indent=2)+'\n')
 (a.output/'grammar.json').write_bytes(a.candidate.read_bytes())
 write('allocation.json',alloc);write('renumbering.json',dict(old_to_canonical=mapping,canonical_to_old=order));write('local-routing-audit.json',local)
 ast=source['ast_dag'];byast={int(i):names[int(q)] for q,i in source['sequence_ast_roots'].items()}
 @cache
 def raw_base(i):
  r=ast[i];return ('L',tuple(r[1])) if r[0]=='L' else ('N',raw_base(r[1]),raw_base(r[2]))
 def balanced(items):
  assert items
  if len(items)==1:return items[0]
  k=len(items)//2;return ('N',balanced(items[:k]),balanced(items[k:]))
 @cache
 def raw(i):
  if meta.get('source_override') and i==int(source['sequence_ast_roots']['76']):
   return balanced([raw_base(meta['token_to_ast'][c]) for c in meta['source_override']['new_word']])
  r=ast[i];return ('L',tuple(r[1])) if r[0]=='L' else ('N',raw(r[1]),raw(r[2]))
 @cache
 def changed(i):
  if i in byast and byast[i] in rules:return expand(byast[i])
  r=ast[i];return ('L',tuple(r[1])) if r[0]=='L' else ('N',changed(r[1]),changed(r[2]))
 @cache
 def expand(w):
  if w in terms:return changed(source['atoms'][terms[w]]['ast'])
  l,r=rules[w];return ('N',expand(l),expand(r))
 before,after=raw(source['original_ast']),changed(source['original_ast'])
 def leaves(t,p=''):
  return [(p,t[1])] if t[0]=='L' else leaves(t[1],p+'0')+leaves(t[2],p+'1')
 bl,al=leaves(before),leaves(after);assert [x for p,x in bl]==[x for p,x in al]
 codes=dict(inc='CI',dec='CD',brk='CB',cont='CC',halt='CH')
 def sites(physical):
  return [[p,codes[e[0]],None if len(e)==1 else rebuild.PHYSICAL[e[1]] if physical and e[0] in ('inc','dec') else e[1]] for p,e in al]
 write('sites_logical.json',sites(False));write('sites_physical.json',sites(True));write('modified_source.json',dict(source_backend='LM_DIRECT_NEGATION',source_edits=meta['source_edits'],source_override=meta.get('source_override'),before=before,after=after))
 entries=rmpath.certificate(before,after);comparison=check_bisimulation(before,after,entries);bits=lambda p:''.join('1' if b else '0' for b in p);write('register_bisimulation.json',dict(start_pair=0,entries=[[bits(x),bits(y),nz,z] for x,y,nz,z in entries],result=comparison))
 boot=sparse_boot(table,2000000);write('blank_boot.json',boot)
 report=dict(status='EMITTED_LM_CANDIDATE_REQUIRES_FULL_BINARY_FRAME_CHECK',working_states=len(states),source_leaves=len(al),maximum_depth=max(len(p) for p,e in al),maximum_zero_run=max(max(map(len,p.split('1'))) for p,e in al),table_sha256=hashlib.sha256((a.output/'machine_old.tm').read_bytes()).hexdigest(),canonical_sha256=hashlib.sha256((a.output/'machine.tm').read_bytes()).hexdigest(),register_program_reassociation=comparison,blank_status=boot['status'],blank_steps=boot.get('blank_steps'),scope='Changed-source reassociation and concrete blank check only. The 218/0 primitive/routing contraction needs independent full runtime validation.')
 write('machine-audit.json',report);print(json.dumps(report,indent=2))
if __name__=='__main__':main()
