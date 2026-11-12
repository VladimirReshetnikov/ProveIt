#!/usr/bin/env python3
"""Independent symbolic tuple and bridge-direction source audit; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-positive-bridge-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'README.md':'00ed4f7cf27e06b3ebebb777695503c6e61d0cc0e4099112de99cd7b5ae5a3c5','Root74PositiveBridge.lean':'f54228acca9fd8db59d25bdd65b3cf4910fb4bd8c7395524c2c4803fdc047e90','check_source.py':'35bca13cbd9c7a37c630caef67f8fc6d43149fe43a5f079193e4d5bcf0b55df0','observation.json':'9c59b5f9d04749efcaadd284476a558f11644a2883346f55e880cd496b6546eb'}
tail=b"\nIndependent source review: [root74 positive bridge](../../reviews/ordinary14-root74-positive-bridge-independent/README.md).\n"
final=(A/'README.md').read_bytes()
assert hashlib.sha256(final).hexdigest()=='60e2b116753b262870420f43586be5ca155c5c6cf11a4eb2f11f237f5bde0dcc'
assert final.endswith(tail) and hashlib.sha256(final[:-len(tail)]).hexdigest()==pins['README.md']
for n,h in pins.items():
 if n!='README.md':assert sha(A/n)==h,n
s=(A/'Root74PositiveBridge.lean').read_text();mapfile=D/'research/ordinary14-78-74-model-composition-draft/Model78To74.lean';prior=D/'research/ordinary14-root78-positive-bridge-draft/Root78PositiveBridge.lean';slim=D/'research/ordinary14-compact-port-bounds-slim-draft/CompactPortBoundsSlim.lean';tuplefile=D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean';ports=D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean';endpoint=D/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean'
for p,h in [(mapfile,'dd18b7795ed5c9e9bfa4bd9f1d78aa134b4a896c80ed1f4e24478a0add220b76'),(prior,'d9cd05f4e1aa64ddf4d4f800ba51c3a9774558e95b2709950d115acb3b9b166a'),(slim,'fb35a320b1521b3005feb597ace302ea9779304839a952b9590f6e0b9a6b4fa4'),(tuplefile,'379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46'),(ports,'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414'),(endpoint,'1476d90741c9cae95b164c4de25dcbdf43399347eee97b9031684f9b1a916ce1')]:assert sha(p)==h
for t in ['(P74PositiveGuard.graph CompactSymbolicModelIff.p).output','let p : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat','CompactPortBoundsSlimDraft.port_bounds (V:=V) CompactFixedBeta.betaNat','(paramKernel rho) lowNat highNat CompactFixedBeta.beta_identity rfl rfl','Model78To74Draft.positive_zero_iff_natural_ports (V:=V) p hb.1','hpair.symm.trans (Root78PositiveBridgeDraft.positiveBridge V)']:
 assert t in s,t
assert not re.search(r'\b(?:sorry|admit|axiom)\b',s)
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in tuplefile.read_text()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports.read_text()
assert '(P78AuxRoot.graph CompactSymbolicModelIff.p).output' in prior.read_text()
assert '0 < (ports B K L H 0 : V) ∧' in slim.read_text()
mt=mapfile.read_text().split('theorem positive_zero_iff_natural_ports',1)[1].split(':= by',1)[0];assert mt.index('P78AuxRoot')<mt.index('P74PositiveGuard')
e=endpoint.read_text().split('def PositiveModelBridge',1)[1].split('theorem bridge_of_positive',1)[0];assert e.index('InternalZero e v')<e.index('ArithmeticMachineRun215.run time')
reviews=[('ordinary14-78-74-model-composition-independent','a9f0c41711366888695748e4dc5b1f89e0ba77d42654a34b18d5b20b8ad06341','observation.json','3dd4c353aeeec78fd3a7d503626638f4b5e7819a79a47997c4c353a56a02823a'),('ordinary14-root78-positive-bridge-draft-independent','9626cc12b784de46138760fe285b1d1503252d2f2d6a9fb15b3881b5feb6e99d','result.json','1f4eb32d21c19dfe5ecd50d135d52da0fe5057df5f00fca43e1a2e58fc00495e'),('ordinary14-compact-port-bounds-slim-independent','4050d26f346755fe03e8dde90e206eecd276726d712008d79aff6bf1fde6b780','observation.json','c1fdedc40513b14c6e0544caa5b04f352f77528822726054cb19784d47647b35')]
for n,h1,receipt,h2 in reviews:
 q=D/'reviews'/n;assert sha(q/'check.py')==h1 and sha(q/receipt)==h2
 assert subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],cwd=D,check=True,capture_output=True).stdout==(q/receipt).read_bytes()
assert subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,check=True,capture_output=True).stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source interface, symbolic tuple and prior review replay only; no Lean, provider or endpoint proof','author_pins':pins,'symbolic_port_source_sha256':sha(tuplefile),'port_constructor_sha256':sha(ports),'bridge_interface_sha256':sha(endpoint),'prior_source_reviews_replayed':[x[0] for x in reviews],'author_receipt_reproduced':True},sort_keys=True,indent=2))
