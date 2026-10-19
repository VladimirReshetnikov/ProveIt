"""Parametric wrong-return witness for the invalid 244 reassociation.
Registers are fixed zero; gap and all spare values/length are arbitrary.
Self-authored symbolic rules only. This is a runtime-contract rejection,
not a blank-run reachability or consistency-theoretic separation claim.
"""
import json
import symbolic_runtime as s
import independent_runtime as r
T=r.table(r.OUT/'candidates/candidate_reassociation244_old.tm')
lemmas,blocks=s.prove_blocks(T)
pc='111010010010000000'
values=[s.ZERO]*9
start=s.State(96,[s.bit(1),s.BLANK],[s.bit(int(b)) for b in pc]+[s.run(0,s.add(s.var(1),s.num(64-len(pc)))),s.bit(1)]+s.file_bits(values))
# Tape at clean return in the independently checked literal witness.
badpc=''.join('1' if i in [0,1,2,4,7,10,13] else '0' for i in range(14))
expectedpc=r.inc(r.strip(pc,'0',1))[0]
def target(p):return s.State(96,[s.bit(1),s.BLANK],[s.bit(int(b)) for b in p]+[s.run(0,s.add(s.var(1),s.num(64-len(p)))),s.bit(1)]+s.file_bits(values))
bad=target(badpc).key();good=target(expectedpc).key()
clock=s.ZERO;motion=s.ZERO;trace=[]
for count in range(4000):
 key=start.key()
 assert not count or key!=good,'Correct target unexpectedly reached before bad return'
 if count and key==bad:break
 clock,motion,event=start.step(T,lemmas,clock,motion);trace.append(event)
else:raise AssertionError('Wrong target not established')
assert motion==s.ZERO
report={'status':'PARAMETRIC_WRONG_RETURN_PROVED','start_pc':pc,'wrong_return_pc_minimal':badpc,'required_pc':expectedpc,'logical_registers':[0]*9,'quantifiers':'For every additional gap n>=0, every first spare v>=0, and every finite list of remaining spare values','whole_tape_difference':'Wrong return has one at cell13 and zero at16; required target has zero at13 and one at16; all other cells identical','duration_affine_coefficients':clock,'symbolic_rule_count':len(trace),'literal_steps_at_gap0_spare1_emptytail':clock[0]+clock[11],'scope':'First clean-frame instruction-contract failure; not blank-run reachability or consistency equivalence','trace':trace}
(r.OUT/'obvious244_parametric_wrong_return.json').write_text(json.dumps(report,indent=2)+'\n')
print({k:v for k,v in report.items() if k!='trace'})
