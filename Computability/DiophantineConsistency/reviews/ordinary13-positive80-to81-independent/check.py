#!/usr/bin/env python3
"""Pinned literal/direction review and exact finite factor controls; no Lean."""
from pathlib import Path
import hashlib,itertools,json,random
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
r=ROOT/'research';p80=json.loads((r/'ordinary13-unit-product80/candidate.json').read_text());p81=json.loads((r/'ordinary13-residue-first81/candidate.json').read_text())
assert p80['witnesses']==p81['witnesses'] and p80['fixed_numerals']==p81['fixed_numerals']
assert len(p80['source'])==80 and len(p81['source'])==81
assert p80['source'][:-7]==p81['source'][:-8]
assert p80['source'][-7:]==[['F0','+',1,'A0'],['F1','+',1,'A1'],['Fs','+',1,'g72'],['P01','*','F0','F1'],['P012','*','P01','Fa'],['P0123','*','P012','Fs'],['out','-','P0123',1]]
assert p81['source'][-8:]==[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam','-','Fa',1],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['sum01','+','A0sq','A1sq'],['sum23','+','Fam2','Fsm2'],['out','+','sum01','sum23']]
src=(r/'ordinary13-positive80-to81-model-draft/PositiveSquare81Graph.lean.src').read_text()
body=src.split('def graph (p : Fin 4 → ℤ) : Graph :=\n',1)[1].split('\nend PositiveSquare81GraphDraft',1)[0].splitlines()
expected=['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(p81['witnesses'])]
expected+=['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(p81['fixed_numerals'])]
expected+=['  let '+n+' := '+str(a)+' '+op+' '+str(b) for n,op,a,b in p81['source']]
expected+=['  ⟨A0,A1,Fa,g72,out⟩']
assert body==expected
src80=(r/'ordinary13-natural89-to-positive80-model-draft/PositiveUnit80Graph.lean.src').read_text()
body80=src80.split('def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n',1)[1].split('\nend PositiveUnit80GraphDraft',1)[0].splitlines()
expected80=['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(p80['witnesses'])]
expected80+=['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(p80['fixed_numerals'])]
expected80+=['  let '+n+' := '+str(a)+' '+op+' '+str(b) for n,op,a,b in p80['source']]
expected80+=['  out']
assert body80==expected80
assert all(x!=y for x in (3,11) for y in (0,12,6,9))
# Bounded square-sum/product controls are consistency tests, not all-model proof.
controls=0
for a,b,c,d in itertools.product(range(-2,3),repeat=4):
 square=a*a+b*b+(c-1)**2+d*d;product=(1+a)*(1+b)*c*(1+d)-1
 if square==0:assert product==0
 controls+=1
source=(r/'ordinary13-positive80-to81-model-draft/Positive80To81Transport.lean.src').read_text()
for x in ['import Eta85ToPositive80','EtaNaturalUnitBridgeDraft.residuals_zero',
 'Natural89Positive80TransportDraft.lift_lower','Natural89RReplacementDraft.zero89_iff85',
 'theorem zero80_to81','theorem zero81_to80','theorem sameNoZero',
 'Eta85ToPositive80Draft.native85','(h81 : PolynomialBridge']:
 assert x in source,x
assert '←show (PositiveSquare81GraphDraft.graph p).first' not in source
print(json.dumps({'source_pins':pins,'shared_graph_rows':len(p80['source'])-7,
 'generated_81_rows':len(p81['source']),'square_to_product_finite_controls':controls,
 'lean_executed':False,'scope':'source review only; no model/provider/endpoint proof'},sort_keys=True,indent=2))
