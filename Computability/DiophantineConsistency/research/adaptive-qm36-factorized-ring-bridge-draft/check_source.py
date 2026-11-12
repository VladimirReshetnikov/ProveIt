#!/usr/bin/env python3
"""Read-only source indices and external all-port identity observation."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1];B=D/'research/adaptive-qm36-conditional-model-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
pin(P/'generate.py','36a2e19a52ac82540f42366c089cfbf575faf6a9195ca7a6ad2cbed1eefb2f78')
obs=json.loads(pin(P/'result.json','3d4e4fd95c97362044b35b4e8cebba6f482e34214c88f2f4e8c4e54fd1f99a88'))
s=pin(P/'AdaptiveQM36FactorizedRingBridge.lean.src','9a7d38b4dc75a13b2bc400214823ceb6d0607ce1c3ab4008d62626de55e912f7')
a=pin(B/'AdaptiveQM36Residuals155.lean.src','03c99c18fc52e185bf8c334ce3ab62afb40c9f0d91d7bdc2cd5e695263dfae95');b=pin(B/'AdaptiveQM36Residuals153.lean.src','05bdc1497069a2b0417b340f696cd4c69c3f84df0c97d4c5d05d5f1db01a782d')
cert=json.loads(pin(D/'research/adaptive-square-sums36-factored-roots/result.json','b5688a298d31bcb1815bcfceb33ed2283ddfd397f71b6fc84984218e7182151a'))
def vec(x):
 y=re.findall(r'^  !\[([^\n]+)\]$',x,re.M);assert len(y)==1;return y[0].split(',')
r=vec(a);assert r==vec(b) and len(r)==27 and r[14]=='zDifference' and r[15]=='dDifference'
assert re.findall(r'/-- Residual (\d+): ([A-Za-z0-9_]+)\. -/',s)==[(str(i),n) for i,n in enumerate(r)]
for i in range(27):
 assert f'theorem residual{i:02d}' in s and f'(AdaptiveQM36Residuals153Draft.residuals p {i}).evalRing v' in s and f'(AdaptiveQM36Residuals155Draft.residuals p {i}).evalRing v' in s
 assert f'h{i:02d} := residual{i:02d} p v' in s
assert cert['all_27_residuals_identical'] and cert['complete_output_polynomial_identical']
for x in ('theorem evaluation_identity {R : Type*} [CommRing R]','theorem internalZero_iff','theorem sameNoZero','theorem native_equivalence'):
 assert x in s
for x in ('(h38 : AdaptiveQM38ConditionalTransferDraft.ZeroPreservationObligations)','(h37 : AdaptiveQM37ConditionalTransferDraft.GraphZeroObligations)','(h36 : AdaptiveQM36ConditionalTransferDraft.GraphZeroObligations)'):
 assert x in s
assert obs['residuals']==27
print(json.dumps({'scope':'bounded source indices and prior exact external polynomial receipt; no Lean/model theorem','residual_identities':27,'factored_indices':[14,15],'all_port_commutative_ring_statement':True,'lean_proof_unelaborated':True,'inherited_obligations_explicit':True},indent=2,sort_keys=True))
