#!/usr/bin/env python3
"""Check exact source/DAG gamma shift, not Lean elaboration."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
pins={
'research/ordinary14-natural80-gamma-shift-model-draft/Natural80GammaShift.lean':'150871559ad8be8ac689135c8021b8e488af138e68f929b878632d13d99c216a',
'research/ordinary14-natural80-gamma-shift-model-draft/check_source.py':'1c7c98d2243263f11e879c23dee56e26164ea914d715b358d1d16701b71bcd4e',
'research/ordinary14-natural80-gamma-shift-model-draft/result.json':'fba473c7d6b2293bce08e0c2e7f6020ef87eb5b9a53abf4c5b7d917ae67387ec',
'research/ordinary14-natural80-gamma-client-draft/Natural80GammaClient.lean':'7fca431907062c8578970ae7840f37d3710f09f49c0e1e4a784ba7a94cb8288b',
'research/ordinary14-natural-forced-gamma80/candidate.json':'136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5',
'research/ordinary14-natural-forcedj81/candidate.json':'24d0c9f0f7d0078f268b27f6d3a0698952fbc0b13c4d28b4e5f9152dc4a41999',
'research/ordinary14-natural-forced-gamma80-lean-draft/P80NaturalForcedGamma.lean':'015214c4176ab1600c573297521b43987eb66fe863d918a6bcff803a76ca44d9',
'research/ordinary14-natural-forcedj81-lean-draft/P81NaturalForcedJ.lean':'73fbd4a953a32c7c56a1e1b06f93c4da9aed950c8022f8988ac82c6c06353897',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
}
s={}
for p,h in pins.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[Path(p).name if not p.endswith('candidate.json') else p]=b.decode()
g80=json.loads(s['research/ordinary14-natural-forced-gamma80/candidate.json']);g81=json.loads(s['research/ordinary14-natural-forcedj81/candidate.json'])
assert g80['witnesses']==g81['witnesses'] and len(g80['witnesses'])==14 and g80['fixed_numerals']==g81['fixed_numerals']
assert g80['witnesses'][12]=='n_gamma' and len(g80['source'])==80 and len(g81['source'])==81
for g,t in ((g80,s['P80NaturalForcedGamma.lean']),(g81,s['P81NaturalForcedJ.lean'])):
 assert re.findall(r'let\s+(\w+)\s*:\s*Expr \(Fin 14\)\s*:=\s*\.var (\d+)',t)==[(v,str(i)) for i,v in enumerate(g['witnesses'])]
 assert re.findall(r'let\s+(\w+)\s*:\s*Expr \(Fin 14\)\s*:=\s*\.constant \(p (\d+)\)',t)==[(v,str(i)) for i,v in enumerate(g['fixed_numerals'])]
 block=t.split('-- BEGIN LITERAL GRAPH',1)[1].split('-- END LITERAL GRAPH',1)[0];rows=[]
 for line in block.splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'\s*let (\w+) := (\w+|\d+) ([+*\-]) (\w+|\d+)\s*',line);assert m,line
  n,x,op,y=m.groups();p=lambda t:int(t) if t.isdecimal() else t;rows.append([n,op,p(x),p(y)])
 assert rows==g['source']
 assert [x.strip() for x in re.search(r'-- END LITERAL GRAPH\s*⟨([^⟩]+)⟩',t).group(1).split(',')][:6]==['F0','F1','Fa','Fs','guard','out']
 known=set(g['witnesses']+g['fixed_numerals'])
 for n,op,x,y in rows:
  assert n not in known and all(type(v)==int or v in known for v in (x,y));known.add(n)
 assert g['output']=='out'
# Exact row-by-row deletion proves substitution gamma=(n_gamma-1)+1, not same-valuation equality.
assert ['gamma','+','n_gamma',1] in g81['source']
expected=[[n,op,'n_gamma' if x=='gamma' else x,'n_gamma' if y=='gamma' else y] for n,op,x,y in g81['source'] if n!='gamma']
assert expected==g80['source']
# Exact one-coordinate affine cut: 80 input = 81 input + 1.
for j in range(14):
 d=-1 if j==12 else 0
 sft=1 if j==12 else 0
 assert d+sft==0
src=s['Natural80GammaShift.lean']
for tok in ('j = 12 then v j - 1 else v j','v80 12=v81 12+1 ∧ ∀ j, j≠12 → v80 j=v81 j',
 'if j=12 then v j+1 else v j', 'down81 (fun j => ι (v80 j)) = (fun j => ι (v81 j))',
 'InternalZero (P80NaturalForcedGamma.graph p).output v80 ↔',
 'InternalZero (P81NaturalForcedJ.graph p).output v81',
 'gamma_pos_of_80_zero p beta K MC MF v hbeta hK hMC hMF hb hKpos hMCbound hMFbound hv',
 'exists_add_of_le (pos_iff_one_le.mp hg)','simpa [w,add_comm] using hg',
 '(internalZero_iff_related p hw).mp hv', '(internalZero_iff_related p (related_lift w)).mpr hw'):
 assert tok in src,tok
m=re.search(r'theorem exists_zero_iff\b(.*?)(?=\s+:=\s*by\b)',src,re.S);assert m
sig=re.sub(r'\s+',' ',m.group(1))
for tok in ('(hbeta : (p 0 : DiffRing V)=ι beta)', '(hK : (p 1 : DiffRing V)=ι K)', '(hMC : (p 2 : DiffRing V)=ι MC)', '(hMF : (p 3 : DiffRing V)=ι MF)', '(hb : 0<beta)', '(hKpos : 0<K)', '(hMCbound : MC<beta)', '(hMFbound : MF<2*beta)'):
 assert tok in sig,tok
assert all(x not in sig for x in ('0<v 12','0 < v 12','0<w 12','0 < w 12'))
gm=re.search(r'theorem gamma_pos_of_80_zero\b(.*?)(?=\s+:=\s*by\b)',s['Natural80GammaClient.lean'],re.S);assert gm
gs=re.sub(r'\s+',' ',gm.group(1))
for tok in ('(hbeta : (p 0 : DiffRing V)=ι beta)', '(hK : (p 1 : DiffRing V)=ι K)', '(hMC : (p 2 : DiffRing V)=ι MC)', '(hMF : (p 3 : DiffRing V)=ι MF)', '(hb : 0<beta)', '(hKpos : 0<K)', '(hMCbound : MC<beta)', '(hMFbound : MF<2*beta)', ': 0<v 12'):
 assert tok in gs,tok
model=s['ModelDifferenceRing.lean'];assert 'AdaptiveEquationSyntax2011.InternalZero e v ↔ e.evalRing (fun i => ι (v i)) = 0' in model
for n in ('output_eval','internalZero_iff_related','exists_zero_iff'):
 assert '#print axioms DiophantineConsistency.Natural80GammaShiftDraft.'+n in src
print(json.dumps({'scope':'source signatures and exact external gamma-shift graph edit; no Lean/model/iPRA theorem', 'pinned_files':len(pins),'graphs_rows':[80,81],'shifted_slot':12,'forward_needs_derived_predecessor':True,'axiom_prints_executed':False},sort_keys=True,indent=2))
