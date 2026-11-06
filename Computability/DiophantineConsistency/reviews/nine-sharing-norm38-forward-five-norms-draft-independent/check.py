import hashlib,json,re
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-forward-five-norms-draft';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();a=q/'Norm38ForwardFiveNorms.lean';b=q/'Norm38SourceToSeed.lean'
assert sha(a)=='d3e4b62d337dab008f2b4b4788178de6a9af8058b756b025ff505e05230dfd4c' and sha(b)=='9b1a089b2d84bdea914aa629230fec9dc06d704baac1e2a2d13cf7948b593363';x=a.read_text();y=b.read_text()
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',x,re.M)==['DiophantineConsistency.Norm38ReferenceTerminals','DiophantineConsistency.Norm38ReferenceFieldsAll','DiophantineConsistency.Norm38ForwardGatesAssembly','DiophantineConsistency.Norm38ForwardPrefix']
assert 'd.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1' in x and 'NormAssignment38.fiveNorms ι ports' in x and 'SharingForward38.witnessCoordinates ports u' in x
assert all(t in x for t in ['Norm38ForwardGates.forward_gatesHold','Norm38Reference.static_terminals_agree','Norm38Forward.forward_prefix','Norm38Reference.reference_terminal_fields_combined','Carrier65.strong_scale','hZ.trans (hcd.symm.trans htd.symm)'])
assert '∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)' in y and '(0 : DiffRing V) < ((p 0 : ℤ) : DiffRing V)' in y and 'InternalZero (ObjectCurrentEquation2011.expressionAt p) (fun j => u j+1)' in y and '(Fin.cons (1 : V) (SharingForward38.witnessCoordinates ports u))' in y
assert all(t in y for t in ['FreshModel106.evalRing_expressionAt65','FreshCarrierSpheres.modelFacts','FreshCarrierSpheres.value65_zero_iff_norms','Norm38Forward.static_implies_seed_zero','Norm38ForwardGates.forward_gatesHold','Norm38ForwardFiveNorms.forward_fiveNorms'])
carrier=(D/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert '(core p v).Z = (core p v).delta * strong (core p v)' in carrier
spheres=(R/'current2011-spheres-fresh-base/FreshCarrierSpheres.lean').read_text();assert '(core p v).P = 1 ∧ (core p v).Q = 1 ∧ (core p v).U = 1 ∧\n        strong (core p v) = 1 ∧ (core p v).W = 1' in spheres
p=(R/'normalized106-fresh-base-model-build/FreshModel106.lean').read_text();assert '(ObjectCurrentEquation2011.expressionAt p).evalRing v =' in p and 'Carrier65.value (fun j => (p j : R)) v' in p
print(json.dumps({'status':'PASS_SOURCE_REVIEW_ONLY','five_norms_sha256':sha(a),'source_to_seed_sha256':sha(b),'scope':'Proposed proofs uncompiled; provider routing and elaboration unchecked; no endpoint claim.'},indent=2,sort_keys=True))
