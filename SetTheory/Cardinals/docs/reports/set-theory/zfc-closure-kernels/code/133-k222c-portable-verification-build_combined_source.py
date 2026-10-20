#!/usr/bin/env python3
"""Reconstruct the G + witness-request source and bind its exact arithmetic emitter.

This source certificate is an ordinary mathematical verification program. It
uses the pinned witness-request K223 package's source language and all-register
macro bisimulations. Binary runtime and native logical equivalence are separate
necessary certificates.
"""
from pathlib import Path
from functools import cache
import argparse, hashlib, json, sys

SEED_SOURCE_SHA='df55079f114a6aa9ada970d7d857726e47e3a3dba2a721245ebbacfd4577c13c'
SEED_TABLE_SHA='7e036b1bd05fe8a7e5877a8c5386cae603f4d689adeeb13754ee98dca998bfef'
BASE_SOURCE_SHA='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878'
BASE_TABLE_SHA='f886dd8d11e9705c5315140f68d5ae2f26c80afb015e08074c7e3da1414fa37f'
FINAL_SOURCE_SHA='cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e'
ROTATION='1110100100111000'
TARGET='11101001001110'
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--seed-root',type=Path,required=True)
 ap.add_argument('--baseline224',type=Path,required=True)
 ap.add_argument('--output',type=Path,required=True)
 a=ap.parse_args()
 sys.path.insert(0,str(a.seed_root/'portable/verification'))
 import source_language as s
 import build223 as b
 @cache
 def size(n):return 1 if s.leaf(n) else size(n[0])+size(n[1])
 def flat(n):return tuple((o,k) for p,o,k in s.sites(n))
 def read_pinned(path,pin):
  raw=path.read_bytes();assert sha(raw)==pin,(path,sha(raw));return raw
 source_raw=read_pinned(a.seed_root/'portable/machine/sites.json',SEED_SOURCE_SHA)
 table_raw=read_pinned(a.seed_root/'portable/machine/candidate.k.tm',SEED_TABLE_SHA)
 seed=s.tree(json.loads(source_raw));table=b.read_table(table_raw)
 groups,paths=b.decoder_map(table,seed);q=lambda k:b.sole(groups,k)
 baseraw=read_pinned(a.baseline224/'portable/machine/results/sites.json',BASE_SOURCE_SHA)
 basetable=b.read_table(read_pinned(a.baseline224/'portable/machine/results/candidate224.k.tm',BASE_TABLE_SHA))
 base=s.tree(json.loads(baseraw));basegroups,_=b.decoder_map(basetable,base)
 tokens,contracts=b.macros_and_contracts(a.baseline224,basegroups)
 macros={k:b.sequence(parts) for k,parts in tokens.items()}
 word_flat=lambda word:sum((flat(macros[k]) for k in word),())
 I,Q,R,E,N=b.I,b.Q,b.R,b.E,b.N
 old_row_word=[168,166,182,168,121,182,166,121,182,119,119]
 new_row_word=[168,166,182,168,121,182,166,121,181,166,121,182,180,119,119]
 row_before=I(E('c','a'),I(E('c','b'),E('a','b')))
 row_after=I(E('c','a'),I(E('c','b'),Q(R('a','b'),E('a','b'))))
 assert b.execute_word(old_row_word)==row_before
 assert b.execute_word(new_row_word)==row_after
 spec_raw=(a.seed_root/'portable/machine/grammar223.json').read_bytes()
 assert sha(spec_raw)==b.GRAMMAR_SHA
 word=json.loads(spec_raw)['macro_word']
 assert b.execute_word(word)==b.expected_expression()
 new_word=word[:9]+word[20:75]+word[76:]
 old_bundle=b.expected_expression()
 # The repeated seed request W and hereditary closure H are unchanged.
 rv=I(R('a','b'),Q('c',R('a','b')))
 helper=I(E('a','b'),Q(R('a','b'),E('a','b')))
 core_tail=old_bundle[1][2][2]
 assert old_bundle==N(I(rv,I(helper,core_tail)))
 new_bundle=N(I(rv,core_tail))
 assert len(new_word)==65 and b.execute_word(new_word)==new_bundle
 old_flat=flat(seed)
 assert old_flat[486:786]==word_flat(old_row_word)
 assert old_flat[2541:4781]==word_flat(word)
 expected=(old_flat[:486]+word_flat(new_row_word)+old_flat[786:2541]
           +word_flat(new_word)+old_flat[4781:])

 # Prune two closed helper pieces and insert the G row's new constructors,
 # retaining all useful existing source factors and all source instruction order.
 # Intervals refer to the unmodified seed source and are processed right-to-left.
 pair_inc,rel,eq,all_=q(99),q(155),q(182),q(86)
 inserted=((pair_inc,(rel,eq)),all_)
 assert old_flat[648:732]==flat((pair_inc,eq))
 assert flat(rel)==word_flat([166,121,181])
 assert flat(eq)==word_flat([166,121,182])
 assert all(s.boundary(t)==(0,0,False) for t in (pair_inc,rel,eq,all_))
 offsets=[2541]
 for k in word:offsets.append(offsets[-1]+size(macros[k]))
 assert (offsets[9],offsets[20],offsets[75],offsets[76],offsets[-1])==(2783,3083,4707,4734,4781)
 changes=[(648,732,inserted),(2783,3083,None),(4707,4734,None)]
 def edit(n,pos,start,end,replacement):
  stop=pos+size(n)
  if end<=pos or stop<=start:return n
  if start<=pos and stop<=end:return replacement if pos==start else None
  assert not s.leaf(n)
  left=edit(n[0],pos,start,end,replacement)
  right=edit(n[1],pos+size(n[0]),start,end,replacement)
  return right if left is None else left if right is None else (left,right)
 composed=seed
 for start,end,replacement in reversed(changes):
  composed=edit(composed,0,start,end,replacement)
 assert flat(composed)==expected
 assert s.metrics(composed)==dict(dag_nodes=208,leaf_occurrences=4744,maximum_depth=36,maximum_zero_run=7)

 # One global closed rotation repairs the only seven-zero source address.
 selected=s.subtree(composed,ROTATION)
 assert not s.leaf(selected[0])
 u,v=selected[0];w=selected[1]
 assert all(s.boundary(t)==(0,0,False) for t in (u,v,w))
 replacement=u,(v,w)
 @cache
 def rotate(t):
  return replacement if t==selected else t if s.leaf(t) else (rotate(t[0]),rotate(t[1]))
 final=rotate(composed)
 assert flat(final)==expected
 assert s.metrics(final)==dict(dag_nodes=208,leaf_occurrences=4744,maximum_depth=36,maximum_zero_run=6)
 g0,c0=s.graph_arithmetic(s.sites(composed));g1,c1=s.graph_arithmetic(s.sites(final))
 assert g0==g1==s.graph_intervals(s.sites(composed))==s.graph_intervals(s.sites(final))

 # Independently assemble an ordinary closed-macro reference source at the
 # smallest closed ancestor containing the changes. No optimized grammar used.
 oldax=s.subtree(seed,TARGET)
 chunks=[inserted]
 for first,last in [(732,2783),(3083,4707),(4734,4815)]:
  chunks+=b.closed_chunks(oldax,first-648,last-648)
 assert len(chunks)==15 and all(s.boundary(t)==(0,0,False) for t in chunks)
 reference=s.replace(seed,TARGET,b.sequence(chunks))
 assert flat(reference)==expected
 gr,cr=s.graph_arithmetic(s.sites(reference))
 assert gr==g1==s.graph_intervals(s.sites(reference))
 assert c0==c1==cr==6167

 source_bytes=s.compact(s.sites(final))
 assert sha(source_bytes)==FINAL_SOURCE_SHA
 result=dict(status='EXACT_COMBINED_SOURCE_AND_ALL_NATURAL_EMITTER_PASS',
  seed_source_sha256=SEED_SOURCE_SHA,seed_table_sha256=SEED_TABLE_SHA,
  source_sha256=sha(source_bytes),source_metrics=s.metrics(final),
  old_source_metrics=s.metrics(seed),
  row=dict(old_expression=row_before,new_expression=row_after,old_word=old_row_word,new_word=new_row_word,
           seed_primitive_interval=[486,786],old_primitive_count=len(word_flat(old_row_word)),new_primitive_count=len(word_flat(new_row_word))),
  bundle=dict(old_expression=old_bundle,new_expression=new_bundle,old_word=word,new_word=new_word,
              seed_primitive_interval=[2541,4781],old_primitive_count=len(word_flat(word)),new_primitive_count=len(word_flat(new_word))),
  all_other_primitive_instructions_unchanged=True,
  unchanged_interfaces=dict(logical_row_positions=8,enumerator=True,gate='c=a or c=b gives0; otherwise emit transformed bundle',proof_cutoff=True,contradiction_code=1),
  rotation=dict(path=ROTATION,direction='right',all_three_factors_closed=True,complete_guarded_cfg_equal=True),
  reference=dict(ancestor=TARGET,closed_chunks=len(chunks),primitive_word_equal=True,guarded_cases=cr,two_independent_cfg_resolvers_agree=True),
  macro_contracts=contracts,
  scope='Symbolic arithmetic expressions hold for all natural a,b,c; arbitrary previous top and stack; initially clean scratch. Separate logical equivalence and complete binary runtime are required.')
 a.output.mkdir(parents=True,exist_ok=True)
 (a.output/'sites.json').write_bytes(source_bytes)
 (a.output/'reference_sites.json').write_bytes(s.compact(s.sites(reference)))
 (a.output/'source_emitter_receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:result[k] for k in ('status','source_sha256','source_metrics','reference')},indent=2))

if __name__=='__main__':main()
