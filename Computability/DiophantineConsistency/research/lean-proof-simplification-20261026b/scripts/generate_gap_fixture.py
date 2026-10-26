#!/usr/bin/env python3
"""Build an exact-data fixture, avoiding unrelated full-module certificates."""
from pathlib import Path
import argparse, hashlib, json
p=argparse.ArgumentParser();p.add_argument('module_dir',type=Path);p.add_argument('prototype_dir',type=Path);a=p.parse_args()
src=(a.module_dir/'GapCircuit66.lean').read_bytes()
start=src.index(b'def naturalNodes :');end=src.index(b'def naturalOutput',start)
definition=src[start:end]
header='''import DiophantineConsistency.ArithmeticDAGPowers

/-! Exact naturalNodes fixture extracted byte-for-byte from pinned GapCircuit66.
Only the length and topology facts needed here are replayed. This does not
constitute a successful build of the full original GapCircuit66 module. -/
namespace DiophantineConsistency.ProofSimplification.GapData
open ArithmeticDAG
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
'''
footer='''theorem natural_length : naturalNodes.length = 484 := by decide +kernel

theorem natural_topological : Topological naturalNodes := by decide +kernel

end DiophantineConsistency.ProofSimplification.GapData

'''
power=(a.prototype_dir/'GapPowerCertificate.lean').read_text()
power='\n'.join(x for x in power.splitlines() if not x.startswith('import '))+'\n'
power=power.replace('GapCircuit66.','GapData.')
dispatch=(a.prototype_dir/'CircuitDispatch.lean').read_text()
dispatch=dispatch[dispatch.index('namespace DiophantineConsistency'):]
dispatch=dispatch.replace('CircuitDispatch','GapFixtureDispatch').replace('GapCircuit66.','GapData.')
fixture=header.encode()+definition+footer.encode()+power.encode()+b'\n'+dispatch.encode()
output=a.prototype_dir/'GapExactDataFixture.lean';output.write_bytes(fixture)
assert fixture[len(header.encode()):len(header.encode())+len(definition)]==definition
manifest={'snapshot':'60e9c5d620c6c387d932876cfa2d9376f64ea56c',
'source':'Computability/DiophantineConsistency/Lean/DiophantineConsistency/GapCircuit66.lean',
'source_file_sha256':hashlib.sha256(src).hexdigest(),
'definition_byte_offset':start,'definition_bytes':len(definition),
'definition_sha256':hashlib.sha256(definition).hexdigest(),
'fixture_file':output.name,'fixture_definition_offset':len(header.encode()),
'fixture_definition_matches_source_bytes':True,
'scope':'Exact naturalNodes data; length, topology, power-label certificate, power theorem, local dispatch. Full original module build failed separately.'}
(a.prototype_dir/'gap_fixture_source.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))
