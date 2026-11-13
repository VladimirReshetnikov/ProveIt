#!/usr/bin/env python3
"""External source-binding check for the proposed forward bridge, not Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
slotsfile=D/'research/nine-sharing-norm38-slot-extraction-draft/slots.json';assert sha(slotsfile)=='f3b2a0ea47962596d8753533c363a6b3e0b4121cd3150722181581d9085326a4';slots=json.loads(slotsfile.read_text())['slots'];src=(P/'Norm38Forward.lean').read_text();assert 'UNCOMPILED DRAFT' in src and 'sorry' not in src and 'admit' not in src
gates={}
for s in slots:
 if s['kind']=='norm':continue
 m=re.fullmatch(r'(positive|negative)Residual ι GateOp\.(add|sub|mul) \(v (\d+)\) \(v (\d+)\) \(v (\d+)\)',s['rhs']);assert m
 kind,op,a,b,t=m.groups();gates[t]=(a,b,op)
for t,(a,b,op) in gates.items():assert f'have gate_{t} := hg ⟨{t}, {a}, {b}, GateOp.{op}⟩' in src
norm={'N0':'hn0','N1':'hn1','Na':'hna','Nt':'hnt','scaled_Ns':'hns'}
for s in slots:
 i=s['slot'];body=re.search(r'  have hz'+f'{i:02d}'+r' : .*?(?=\n  have |\n  apply )',src,re.S).group()
 assert f'InternalZero (residualAt p {i})' in body and f'slot{i:02d} p ports w hp' in body
 if s['kind']=='norm':assert 'sub_eq_zero.mpr '+norm[s['gate']] in body
 else:
  target=re.search(r'\(v (\d+)\)$',s['rhs']).group(1);projection='1' if s['kind']=='positive' else '2';assert f'gate_{target}.{projection}' in body
for d in ['reviews/nine-sharing-forward38-draft-independent','reviews/nine-sharing-norm38-model-bridge-draft-independent','research/nine-sharing-norm38-reference-draft']:
 p=D/d;run=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True);assert run.returncode==0 and not run.stderr and run.stdout==(p/'result.json').read_bytes(),d
assert len(gates)==19 and len(slots)==29 and len(re.findall(r'  have hz\d\d :',src))==29
for name in ('forward_prefix','forward_gatesHold','forward_fiveNorms','static_implies_seed_zero','source_zero_implies_seed_zero'):assert 'theorem '+name in src
print(json.dumps({'status':'PASS_FORWARD_SOURCE_BINDING_ONLY','source_sha256':sha(P/'Norm38Forward.lean'),'slots_sha256':sha(slotsfile),'gate_hypotheses':len(gates),'slot_residuals':len(slots),'scope':'Generated gate/slot bindings plus existing independent external checks; no Lean compilation or model bridge.'},indent=2,sort_keys=True))
