#!/usr/bin/env python3
"""External binding check only; no Lean proof replay."""
import contextlib,hashlib,io,json,re,runpy,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];f=D/'research/nine-sharing-norm38-forward-bridge-draft/Norm38Forward.lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(f)=='70dad9e40dd83aaca364972a1b84ba62f40594aeb5ad3b62b992e66078821837';s=f.read_text()
with contextlib.redirect_stdout(io.StringIO()): prior=runpy.run_path(str(D/'reviews/nine-sharing-norm38-model-bridge-draft-independent/check.py'))
with contextlib.redirect_stdout(io.StringIO()): forward=runpy.run_path(str(D/'reviews/nine-sharing-forward38-draft-independent/check.py'))
assert forward['results']['38']['ordered_assignments']==24
slots=json.loads((D/'research/nine-sharing-norm38-slot-extraction-draft/slots.json').read_text())['slots'];assert len(slots)==29
normnames={'N0':'hn0','N1':'hn1','Na':'hna','Nt':'hnt','scaled_Ns':'hns'};gates=set()
for i,slot in enumerate(slots):
 body=re.search(r'  have hz'+f'{i:02d}'+r' : .*?(?=\n  have |\n  apply )',s,re.S).group();assert f'residualAt p {i}' in body and f'slot{i:02d} p ports w hp' in body
 if slot['kind']=='norm':assert 'sub_eq_zero.mpr '+normnames[slot['gate']] in body
 else:
  k=slot['rhs'];m=re.fullmatch(r'(positive|negative)Residual ι GateOp\.(add|sub|mul) \(v (\d+)\) \(v (\d+)\) \(v (\d+)\)',k);assert m
  kind,op,l,r,t=m.groups();gates.add((t,l,r,op));assert f'gate_{t}.'+('1' if kind=='positive' else '2') in body
for t,l,r,op in gates:assert f'have gate_{t} := hg ⟨{t}, {l}, {r}, GateOp.{op}⟩' in s
assert len(gates)==19 and len(re.findall(r'  have hz\d\d :',s))==29
for frag in ['(hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))','(hb : (0 : DiffRing V) < ((p 0 : ℤ) : DiffRing V))','ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self)','FreshCarrierSpheres.value65_zero_iff_norms','FreshCarrierSpheres.modelFacts','Carrier65.strong_scale','Norm38Reference.static_terminals_agree','SharingNormSquares.seed_zero_iff_residuals']:assert frag in s
carrier=(D/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert '(core p v).Z = (core p v).delta * strong (core p v)' in carrier
print(json.dumps({'status':'PASS_EXTERNAL_FORWARD_BINDING_ONLY','source_sha256':sha(f),'cuts':len(gates),'slots':len(slots),'scope':'Source and prior symbolic comparisons only; no Lean proof or model bridge'},indent=2,sort_keys=True))
