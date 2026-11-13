#!/usr/bin/env python3
"""Check generated slot declarations against pinned graph/seed; no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
graph=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';seed=D/'research/nine-sharing-quartic65-norm38-candidate/seed.json'
assert sha(graph)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
assert sha(seed)=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23'
g=json.loads(graph.read_text());s=json.loads(seed.read_text());slots=json.loads((P/'slots.json').read_text());src=(P/'Norm38SlotExtraction.lean').read_text()
assert 'UNCOMPILED DRAFT' in src and 'sorry' not in src and 'admit' not in src
indices={n:i for i,n in enumerate(g['witnesses'])};indices.update({n:14+i for i,n in enumerate(g['fixed_numerals'])});indices.update({1:18,3:19,4:20});gates={}
for k,(name,op,a,b) in enumerate(g['source'][:60]):
 gates[name]=(k+21,indices[a],indices[b],{'+':'add','-':'sub','*':'mul'}[op]);indices[name]=k+21
for i,(entry,r) in enumerate(zip(slots['slots'],s['residuals'])):
 assert (entry['slot'],entry['gate'],entry['kind'])==(i,r['gate'],r['kind'])
 target,left,right,op=gates[r['gate']]
 expected=(f"{r['kind']}Residual ι GateOp.{op} (v {left}) (v {right}) (v {target})" if r['kind']!='norm' else f"pairValue ι (v {target}) - "+('pairValue ι (v 36)' if r['gate']=='scaled_Ns' else '1'))
 assert entry['rhs']==expected
 body=re.search(r'^theorem slot'+f'{i:02d}'+r'\b.*?(?=^/--|^theorem |^end )',src,re.M|re.S).group()
 assert f'(residualAt p {i}).evalRing' in body and '(let v := NormAssignment38.assignment ports w; '+expected+')' in body
 assert f'have h{i:02d} := each_slot_zero p w hz {i}' in src and f'rw [slot{i:02d} p ports w hp] at h{i:02d}' in src
assert len(slots['slots'])==len(s['residuals'])==29 and len(re.findall(r'^theorem slot\d\d\b',src,re.M))==29
norm={r['gate']:i for i,r in enumerate(s['residuals']) if r['kind']=='norm'}
assert '    exact ⟨'+', '.join(f'sub_eq_zero.mp h{norm[n]:02d}' for n in ('N0','N1','Na','Nt','scaled_Ns'))+'⟩' in src
review=D/'reviews/nine-sharing-norm38-model-bridge-draft-independent';run=subprocess.run([sys.executable,'-I','-S','-B',str(review/'check.py')],capture_output=True)
assert run.returncode==0 and not run.stderr and run.stdout==(review/'result.json').read_bytes()
print(json.dumps({'status':'PASS_GENERATED_SLOT_BINDING_ONLY','source_sha256':sha(P/'Norm38SlotExtraction.lean'),'slots_sha256':sha(P/'slots.json'),'slot_count':len(slots['slots']),'norm_slots':norm,'scope':'Source/graph index binding and previously reviewed symbolic residual comparison only; no Lean compilation, model bridge or endpoint.'},indent=2,sort_keys=True))
