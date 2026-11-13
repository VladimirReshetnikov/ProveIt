#!/usr/bin/env python3
"""Pin and inspect text of the prospective conditional composition only."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1]
paths={
 'composition':('research/nine-sharing-norm38-compose-draft/SharingNormCompose.lean','d1758d81480e229305c6da73ccde257440242cb1cff92748814851ea6e08eb8f'),
 'forward':('research/nine-sharing-forward38-draft/ForwardWitness38.lean','559de61d5eeeb17ef2f6c449f4d594e242ab1c784ce4b34ba58753898209ad14'),
 'seed':('research/nine-sharing-seed38-lean-draft/SharingSeed38.lean','7c459d84ce729a11a837c3c85199f0a01311dcdead6c8b6d4625ded386b72cf1'),
 'spheres_source':('research/current2011-spheres-fresh-base/FreshCarrierSpheres.lean','a9e4d44f3ef37f81f192d9d7fa03678eaa53ca5ec216b3257a3a6fa7ab48f6a5'),
 'model_source':('research/normalized106-fresh-base-model-build/FreshModel106.lean','61e64a2ef559c3da369021df2705cd76f957bc0ea971467b80d627eaa9422769'),
 'port_prelude_source':('research/thirteen-current2011-carrier-model-prelude-diagnostic/ModelThirteenCarrierPrelude.lean','c3a5c6047f9f72d7d5663fa2ad047f00754b5ea92208b6a04ae997714124acc8'),
}
for path,h in paths.values():assert hashlib.sha256((D/path).read_bytes()).hexdigest()==h
s=(D/paths['composition'][0]).read_text();compact=' '.join(s.split())
assert 'UNCOMPILED DRAFT' in s and 'sorry' not in s and 'admit' not in s
for frag in [
 'CurrentMasks2011.beta : V), (CurrentKernel2011.K : V), (CurrentMasks2011.lowPort : V), (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V))',
 'w (Fin.castLE (by decide : 14 ≤ 38) j)',
 'd.P = 1 ∧ d.Q = 1 ∧ d.U = 1 ∧ Carrier65.strong d = 1 ∧ d.W = 1',
 'SharingSeed38.seed CurrentWindowCarry2011.ports) (Fin.cons 1 w)',
 'seedZero w → unitNorms (inputPrefix w)',
 'unitNorms u → seedZero (SharingForward38.witnessCoordinates (naturalPorts (V := V)) u)',
 'existential_seed_iff_current (hextract : Extraction) (hconstruct : Construction)',
 '(∃ w : Fin 38 → V, seedZero w) ↔ ∃ u : Fin 14 → V, InternalZero ObjectCurrentEquation2011.naturalExpression u',
]: assert frag in compact,frag
prelude=(D/paths['port_prelude_source'][0]).read_text()
assert all(('theorem port'+str(i)) in prelude for i in range(4))
assert '(CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ)' in prelude
print(json.dumps({'status':'PASS_CONDITIONAL_SOURCE_INSPECTION_ONLY','pinned_sources':{k:v[1] for k,v in paths.items()},'scope':'Source pins and key statement fragments only; no Lean parsing, kernel check, provider routing or model bridge.'},indent=2,sort_keys=True))
