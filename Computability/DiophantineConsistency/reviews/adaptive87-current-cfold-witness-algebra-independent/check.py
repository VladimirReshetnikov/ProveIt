#!/usr/bin/env python3
"""Independent source-interface and exact integer controls; no Lean."""
import hashlib,json,random,subprocess,sys,itertools
from pathlib import Path
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
for n,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256((R/n).read_bytes()).hexdigest()==h,n
A=(R/'research/adaptive87-current-cfold-witness-algebra-draft/CfoldWitnessAlgebra.lean.src').read_text();S=(R/'research/adaptive87-current-cfold-witness-algebra-draft/CfoldWitnessRepresentatives.lean.src').read_text();P=(R/'research/current2011-shear-positive-gap-representation-draft/PositiveGapRepresentation.lean.src').read_text();M=(R/'Lean/DiophantineConsistency/ModelDifferenceRing.lean').read_text()
for x in ['M*(ell+k+r-k*Bt)+Y*b-q3*Bt','M*(ell+k+rho-k*C)+Y*b-q3*Bt','(hM : M=q3*b) (hY : Y=q3*s) (hBt : Bt=b*t)','(hq : 2 ≤ q) (hC : 1 ≤ C) (hX : q^2 ≤ X)','(hK : 0 ≤ K) (hF : F ≤ q-2)','(hrho : 0<rho) (hk : 0≤k) (hBt : C≤Bt)','(hC : 1≤C) (hk : 0≤k) (hgap : s<tau-ell) (ht : 0≤t)']:assert x in A,x
for x in ['import DiophantineConsistency.ModelDifferenceRing','import CfoldWitnessAlgebra','import PositiveGapRepresentation','(ι (n+1) : DiffRing V) = ι (rho+1)+(ι k)*(Bt-C)','(ι (n+1) : DiffRing V)=(C-1)*k+(tau-ell)-s+t']:assert x in S,x
assert 'theorem positive_as_successor (D : DiffRing V) (hD : 0 < D)' in P and '∃ n : V, ι (n+1) = D' in P
for x in ['instance : CommRing (DiffRing V)','instance : LinearOrder (DiffRing V)','instance : IsStrictOrderedRing (DiffRing V)','theorem nonneg_iff {x : DiffRing V}','theorem ι_nonneg (a : V)','theorem ι_lt_ι {a b : V}']:assert x in M,x
old=json.loads((R/'research/adaptive87-four-square-current88-30/graph.json').read_bytes());new=json.loads((R/'research/adaptive87-current-cfold88-degree28/graph.json').read_bytes())
assert old['witnesses']==new['witnesses'] and old['witnesses'][8]=='r' and old['fixed_numerals']==new['fixed_numerals']
assert [(i,x,y) for i,(x,y) in enumerate(zip(old['source'],new['source'])) if x!=y]==[(28,['root_skew','*','k','Bt'],['root_skew','*','k','C'])]
def parent(M,e,k,r,B,Y,b,q3):return M*(e+k+r-k*B)+Y*b-q3*B
def child(M,e,k,r,C,B,Y,b,q3):return M*(e+k+r-k*C)+Y*b-q3*B
rng=random.Random(54701)
for _ in range(2500):
 M,e,k,r,C,B,Y,b,q3=[rng.randrange(-9,10) for _ in range(9)]
 assert parent(M,e,k,r+k*(B-C),B,Y,b,q3)==child(M,e,k,r,C,B,Y,b,q3)
 assert child(M,e,k,r-k*(B-C),C,B,Y,b,q3)==parent(M,e,k,r,B,Y,b,q3)
 s,t,tau=[rng.randrange(-9,10) for _ in range(3)];M=q3*b;Y=q3*s;B=b*t
 rho=(C-1)*k+(tau-e)-s+t
 assert child(M,e,k,rho,C,B,Y,b,q3)==M*tau
# Equality case shows the stated ordered bound can be sharp.
q,C,X,K,F=2,1,4,0,0
assert C*(X+K*q)-F*q-C==2*q-1
out=subprocess.check_output([sys.executable,'-I','-S','-B',str(R/'research/adaptive87-current-cfold-witness-algebra-draft/check.py')],cwd=R)
assert out==(R/'research/adaptive87-current-cfold-witness-algebra-draft/result.json').read_bytes()
print(json.dumps({'exact_literal_delta':True,'source_interface_markers':True,'signed_ring_wiring_controls':2500,'order_bound_equality_control':True,'author_receipt_reproduced':True,'limitations':'unelaborated source and prospective imports; no model or graph endpoint proof'},indent=2,sort_keys=True))
