#!/usr/bin/env python3
"""Bounded static source and external graph checker; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-qcube93-model-draft/Ordinary13QCube93Arithmetic.lean.src': 'e9f61ed8c5e3262d9a316ef13cd15fa03dfc70a653c6ba7b85059aa9293be36d', 'research/ordinary13-qcube93-model-draft/Ordinary13QCube93Child.lean.src': 'c05027c2a17f2ddb9256294ba1598c64e26b73ce239e8561a8860da63027c10e', 'research/ordinary13-qcube93-model-draft/Ordinary13QCube93ChildResiduals.lean.src': 'df55aaf919b8cc1a9176efaa60fe1b47942d8f9ce33f1b7b45ef769561b8b74f', 'research/ordinary13-qcube93-model-draft/Ordinary13QCube93ConditionalTransfer.lean.src': 'c1ebe2c158143de433c1922f9b9e30c72c2cf7648a87e928416275f980f52d4e', 'research/ordinary13-qcube93-model-draft/Ordinary13QCube93Parent.lean.src': 'bb55431d8f7e065b4b2744dc6ab636b79d62b4efba8c4a55ac67a2bca2581418', 'research/ordinary13-qcube93-model-draft/Ordinary13QCube93ParentResiduals.lean.src': '3c736a519e5d72fede02e6a16470c4b70503fc4ff9320ecd3e53547d4c3b2510', 'research/ordinary13-qcube93-model-draft/generate.py': '9036a03e1b3676b0e460555fbbba312181b36bbc30dee86636bf083fa930d085', 'research/ordinary13-qcube93-model-draft/generated.json': 'fd1eb29f402ce0c077488340f0cf7e27c90506999caf9856303721057d65130d', 'research/ordinary13-natural-qcube-quotient93-degree56/candidate.json': '346a4895448a2212ce2617ef805fd3ea164d7d8896d5bad2c210cf19cd3ef21a', 'research/ordinary13-natural-qcube-quotient93-degree56/check.py': '5b8492a8f96f34ff76e06305c31917afea49942638c7f6bc434533e70479e9b9', 'research/ordinary13-natural-qcube-quotient93-degree56/receipt.json': '07440a24e5f36af72dfc90b8f8eaaa78f6f5f6280636b5026e1a1189b44ab249', 'research/ordinary13-natural-cfold-forced-x95-degree28/candidate.json': '5fd11fa456867a2ed4f3b5bc58db59caab0f58736019ee864403d62124aced4e', 'Lean/DiophantineConsistency/ModelRelationCombining.lean': '559df80321efb3854759ca9dcb20277533bba2568863ddf8e5059d81ac0cc5d6', 'Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean': 'f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660', 'Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean': '4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('ordinary13-qcube93-model-draft','generate.py','generated.json'),('ordinary13-natural-qcube-quotient93-degree56','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
src={x.name:x.read_text() for x in P.glob('*.lean.src')};assert len(src)==6
for n,s in src.items():assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),n
for tag in ['Parent','Child']:
 s=src['Ordinary13QCube93'+tag+'Residuals.lean.src'];m=re.findall(r'^  !\[([^\n]+)\]$',s,re.M)
 assert ': Fin 4 → Expr (Fin 13)' in s and len(m)==1 and m[0].split(',')==['A0','A1','Fam','g72']
a=src['Ordinary13QCube93Arithmetic.lean.src'];t=src['Ordinary13QCube93ConditionalTransfer.lean.src']
for x in ['cube_bezout','cube_dvd_of_dvd_mul','ModelRelationCombining.sq_dvd_sq','Trace75IntegralTransport.natural_dvd_of_signed','positive_quotient_of_signed_norm']:
 assert x in a,x
for x in ['BetaRepresented','GraphObligations','hparent : PolynomialBridge','parentVal_y','childVal_y','positive_quotient_of_signed_norm']:
 assert x in t,x
print(json.dumps({'scope':'bounded source and external graph checks; no Lean','pinned_files':len(pins),'source_files':len(src),'residuals_each':4,'represented_beta_explicit':True,'parent_bridge_and_graph_obligations_explicit':True,'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(src.items())}},sort_keys=True,indent=2))
