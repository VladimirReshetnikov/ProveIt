#!/usr/bin/env python3
"""Independent four-source reconstruction and separate bridge audit; no Lean."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
root='research/ordinary13-residue-folds-model-draft/'
s=pin(root+'ResidueFoldsModel.lean.src','62f5b50c78596f6086ac6ae31f4a00679a3901c9826cf7e6debe6ff39da7db35')
pin(root+'receipt.json','3f777dabcd14daa3d0f2be128ab1d8579b64e22e549d5e8e123948c34f4535a1')
pin('reviews/ordinary13-natural-residue-eta-fold88-independent/result.json','6d2b6da5daadc54609a541e6e4800591248998a488144b307218ebbfedfe2261')
pin('reviews/ordinary13-natural-residue-eta-fold87-independent/result.json','9a77fca0e1200d2a755dca369d91cf77baace798613440e464e108fe6a00cd9b')
entries=[('P89','1cf3ece1241b09402110f78d7be1712b508e431c763772af5a0f6e91d3bb2a73','02849926cb905aa822f0c077329ddef012c8058184ffd719a62c5350a24717c4','ordinary13-natural-residue-forced89-degree56','c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a'),('Fold88','915f92db06125342a2a99757450a25c86b1b7c5049ad00bfa3afe3fc477d63c8','ceca527ce4c67abc58fe8b9c3e82144807ee047c6c22d1701242df05a8a40be2','ordinary13-natural-residue-eta-fold88-degree56','f71cb18bdc28088a7a7c7c7ae84afc15e49470ee3d4fa4076d8c25d6d2b89b58'),('P88','96739da4451ffec0774ffe580d3a754561e194da647708ab3872d7cc143c0fea','8db3637cc65a9bb7cdbacfdc127eb7e1cade5f1f7692009235c1dae3bb25fd62','ordinary13-natural-residue-forced88-degree60','cb488cb849c08c11d159f8805fdd7664c6472cbd41cefadc530e21060a5a1dd2'),('Fold87','ff42c9123d06a684e30b5af953962d82b72ed33a814dcc72faa602f0f05f0161','c52f3b3e7fec3186e6d9efa93ab6d5424c625359b105283d5bf5dc5c8d02c3b0','ordinary13-natural-residue-eta-fold87-degree60','81a09c0504bc786afb017483225e1fb6b1a52e9ddd98f53b0643dfb23c3a602f')]
for name,lh,rh,path,gh in entries:
 graph=json.loads(pin('research/'+path+'/candidate.json',gh))
 for suffix,digest in [('',lh),('Residuals',rh)]:
  src=pin(root+'ResidueFold'+name+suffix+'.lean.src',digest)
  for i,x in enumerate(graph['witnesses']):assert f'let {x} : Expr (Fin 13) := .var {i}' in src
  for i,x in enumerate(graph['fixed_numerals']):assert f'let {x} : Expr (Fin 13) := .constant (p {i})' in src
  rows=re.findall(r'^  let (\w+) := (\w+|\d+) ([+*\-]) (\w+|\d+)$',src,re.M)
  assert rows==[(n,str(a),o,str(b)) for n,o,a,b in graph['source']],name+suffix
  if suffix:assert ': Fin 4 → Expr (Fin 13)' in src and '![A0,A1,Fam,g72]' in src
for pair in ['88_89','87_88']:
 for i in range(4):assert f'theorem relation_{pair}_{i}' in s
 for name in ['evaluation','zero_iff','sameNoZero','polynomialBridge','native_equivalence']:assert f'theorem {name}_{pair}' in s
assert '(hparent : PolynomialBridge (ResidueFoldP89Draft.literal p))' in s
assert '(hparent : PolynomialBridge (ResidueFoldP88Draft.literal p))' in s
assert 'section Ring\nvariable {R : Type*} [CommRing R]' in s
print(json.dumps({'scope':'four exact source reconstructions and conditional bridge signatures; no Lean','parent_89_for_fold_88':True,'parent_88_for_fold_87':True,'four_residuals_each':True,'all_ring_proof_tactics_unchecked':True,'parent_bridges_explicit_and_separate':True,'lean_elaborated':False},sort_keys=True,indent=2))
