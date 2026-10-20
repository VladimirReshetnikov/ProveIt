#!/usr/bin/env python3
"""Rotate a sequence of closed source phases and check exact CFG conjugacy.

This builds exploratory tables by changing only the phase-selector decoder
rows when the two top-level blocks are swapped. Startup/runtime are separate.
"""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
def main():
 out=ROOT/'source218/cyclic_phase';out.mkdir(exist_ok=True)
 p=ROOT/'baseline219/K219_Construction_2026-10-20/machine'
 oldrows=json.loads((p/'sites219.json').read_text());old=r.s.tree(oldrows)
 A,B=old;cut=len(r.s.sites(A));N=len(oldrows);new=(B,A);rows=r.s.sites(new)
 assert r.s.boundary(A)[:2]==r.s.boundary(B)[:2]==(0,0)
 assert [x[1:]for x in rows]==[x[1:]for x in oldrows[cut:]+oldrows[:cut]]
 og=r.s.graph_arithmetic(oldrows)[0];ng=r.s.graph_arithmetic(rows)[0]
 assert og==r.s.graph_intervals(oldrows)and ng==r.s.graph_intervals(rows)
 expected=[]
 for i in list(range(cut,N))+list(range(cut)):
  effect,targets=og[i];expected.append([effect,[(j-cut)%N for j in targets]])
 assert ng==expected
 (out/'sites.json').write_bytes(r.s.compact(rows))
 T=r.b.read_table((p/'k219.native.tm').read_bytes());a0,a1=T[84,0],T[84,1]
 assert a0[:2]==(0,1)and a1[:2]==(1,1)
 U=dict(T);U[84,0]=(0,1,a1[2]);U[84,1]=(1,1,a0[2])
 (out/'phase219.tm').write_bytes(r.b.table_bytes(U))
 V={(q,b):(w,d,88 if z==301 else z)for(q,b),(w,d,z)in U.items()if q!=301}
 V[88,0]=(0,-1,51);V[88,1]=(1,1,103);V[51,0]=(0,1,122);V[51,1]=(1,1,51)
 (out/'phase218.tm').write_bytes(r.b.table_bytes(V))
 receipt={'status':'EXACT_CYCLIC_SOURCE_CFG_CONJUGACY','cut':cut,'leaves':N,
          'old_root_blocks_closed':True,'primitive_word_cyclically_equal':True,
          'two_independent_cfg_resolvers_conjugate':True,'metrics':r.s.metrics(new),
          'old_ord_to_new':'(ordinal - 9) mod 4744','new_initial_old_ordinal':cut,
          'source_sha256':hashlib.sha256((out/'sites.json').read_bytes()).hexdigest(),
          'phase219_sha256':hashlib.sha256((out/'phase219.tm').read_bytes()).hexdigest(),
          'phase218_sha256':hashlib.sha256((out/'phase218.tm').read_bytes()).hexdigest(),
          'changed_phase_rows':[[84,0,*U[84,0]],[84,1,*U[84,1]]],
          'scope':'Source phase conjugacy is exact; table bindings, unbounded runtime, and blank startup remain unproved.'}
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
