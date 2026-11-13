#!/usr/bin/env python3
"""Exact finite floor identity for the R=31 arbitrary-port seed."""
from hashlib import sha256
from pathlib import Path
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;seed=H.parent/'trace74-boundary-31-seed/observation.json'
sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
assert sha(seed)=='bcaf04a0f6651682c5e016748a90dbcdcd3b15bf5b9a14dea62530155238dd93'
r=json.loads(seed.read_text());assert r['status']=='PASS_PARTIAL_SEED' and r['R']==31 and r['X']==2**31
s=int(r['s_hex'],16);X=2**31;numerator=(X+1)**30;denominator=16*X**15;q,rem=divmod(numerator,denominator)
assert q==s and 0<=rem<denominator and numerator==s*denominator+rem
print(json.dumps({'status':'PASS','seed_receipt_sha256':sha(seed),'X':X,'s_hex':hex(s),'s_bits':s.bit_length(),'numerator_bits':numerator.bit_length(),'denominator_bits':denominator.bit_length(),'remainder_bits':rem.bit_length(),'identity':'s = floor((X+1)^30 / (16*X^15))','scope':'finite integer identity only; no Lean certificate, zero, fixed-port or iPRA claim'},sort_keys=True))
