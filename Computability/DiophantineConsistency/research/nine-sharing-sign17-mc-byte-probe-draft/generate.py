#!/usr/bin/env python3
"""Generate a source-only Lean literal from pinned MC raw big-endian bytes."""
import gzip, hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent
seed=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json'
sha=lambda b: hashlib.sha256(b).hexdigest()
raw_seed=seed.read_bytes()
assert sha(raw_seed)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac'
binding=json.loads(raw_seed)['coefficient_binding']; record=binding['ports']['MC']
packed=(seed.parent/binding['path']/record['file']).read_bytes(); raw=gzip.decompress(packed)
assert sha(packed)==record['gzip_sha256'] and sha(raw)==record['raw_sha256']
assert len(raw)==record['raw_bytes']==11815 and raw[0]!=0
literal='0x'+raw.hex()
source='''import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: equality to a literal made from MC bytes; external provenance separate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MCByteLiteral

def mcLiteral : ℕ := '''+literal+'''

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem low_port_literal : CurrentMasks2011.lowPort = mcLiteral := by
  unfold CurrentMasks2011.lowPort LowMaskCoding.mask LowMaskCoding.supportValue mcLiteral
  rw [CurrentMasks2011.lowSupport_def]
  decide +kernel

theorem current_port2_literal : CurrentWindowCarry2011.ports 2 = (mcLiteral : ℤ) := by
  change (CurrentMasks2011.lowPort : ℤ) = (mcLiteral : ℤ)
  exact_mod_cast low_port_literal

end DiophantineConsistency.Sign17MCByteLiteral
#print axioms DiophantineConsistency.Sign17MCByteLiteral.low_port_literal
#print axioms DiophantineConsistency.Sign17MCByteLiteral.current_port2_literal
'''
out=here/'Sign17MCByteLiteral.lean'
if out.exists():raise SystemExit('refusing overwrite')
out.write_text(source)
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','raw_sha256':sha(raw),'raw_bytes':len(raw),
                  'source_sha256':sha(source.encode()),'literal_hex_digits':len(raw.hex()),
                  'scope':'External gzip-to-literal generation; no Lean theorem yet.'},sort_keys=True,indent=2))
