#!/usr/bin/env python3
"""Source/graph audit, not a Lean proof or proof-script replay."""
import contextlib,hashlib,io,json,re,runpy,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];src=D/'research/nine-sharing-norm38-slot-extraction-draft/Norm38SlotExtraction.lean';seed=D/'research/nine-sharing-quartic65-norm38-candidate/seed.json';packet=D/'research/nine-sharing-norm38-slot-extraction-draft/slots.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src)=='7afacc8c1f2b9b0e1b443f346653c21dde511fe200e8296daf2ec2afd4ea38fc' and sha(seed)=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23'
with contextlib.redirect_stdout(io.StringIO()): prior=runpy.run_path(str(D/'reviews/nine-sharing-norm38-model-bridge-draft-independent/check.py'))
s=src.read_text();res=json.loads(seed.read_text())['residuals'];entries=json.loads(packet.read_text())['slots'];assert len(res)==len(entries)==29
names={row[0]:g for row,g in zip(prior['graph']['source'][:60],prior['gates'])};terminal={'N0':61,'N1':44,'Na':78,'Nt':66,'scaled_Ns':80}
for idx,(entry,r) in enumerate(zip(entries,res)):
 assert (entry['slot'],entry['gate'],entry['kind'])==(idx,r['gate'],r['kind'])
 target,lft,rgt,op=names[r['gate']];expected=(f"{r['kind']}Residual ι GateOp.{op} (v {lft}) (v {rgt}) (v {target})" if r['kind']!='norm' else f"pairValue ι (v {target}) - "+('pairValue ι (v 36)' if r['gate']=='scaled_Ns' else '1'))
 assert target==terminal.get(r['gate'],target) and entry['rhs']==expected
 block=re.search(r'^theorem slot'+f'{idx:02d}'+r'\b(.*?)(?=^/--|^theorem |^end )',s,re.M|re.S).group(1)
 assert '(hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))' in block
 assert f'(residualAt p {idx}).evalRing' in block and 'Fin.cons (1 : V) w' in block and expected in block
 assert f'have h{idx:02d} := each_slot_zero p w hz {idx}' in s and f'rw [slot{idx:02d} p ports w hp] at h{idx:02d}' in s
assert 'exact ⟨sub_eq_zero.mp h16, sub_eq_zero.mp h11, sub_eq_zero.mp h27, sub_eq_zero.mp h17, sub_eq_zero.mp h28⟩' in s
assert 'NormAssignment38.gatesHold ι ports w ∧ NormAssignment38.fiveNorms ι ports w' in s
print(json.dumps({'status':'PASS_EXTERNAL_SLOT_BINDING_ONLY','source_sha256':sha(src),'slots_sha256':sha(packet),'slot_count':len(entries),'norm_order':[16,11,27,17,28],'scope':'Uses earlier independent full symbolic source/graph comparison; no Lean replay, proof elaboration or zero bridge'},indent=2,sort_keys=True))
