#!/usr/bin/env python3
"""Exact bit-2 obstruction for the fixed-payload scalar boundary assignment."""
from hashlib import sha256
from pathlib import Path
import gzip,json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
C=D/'candidates/ten-positive-qcube-product-square/coefficients'
def unpack(name,gzip_hash,raw_hash):
 gz=(C/(name+'.bin.gz')).read_bytes();assert sha256(gz).hexdigest()==gzip_hash
 raw=gzip.decompress(gz);assert sha256(raw).hexdigest()==raw_hash
 return int.from_bytes(raw,'little')
beta=unpack('beta','07d42a69e7593ac08bcb2957c965c02f179588b0c3b232c3c640258d0aaeab04','0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d')
mc=unpack('MC','71ecc4fe568471f83978d00ee7a4e03614203d6af36611c0660dbd4fd3eb2276','6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4')
q=beta+1;J=1;F=3;C0=q-3
assert q==1<<(67*8807) and mc%(1<<67)==(1<<67)-2
assert F+C0==q and ((C0-1)>>2)&1==1 and ((mc*J+1)>>2)&1==1
print(json.dumps({'status':'PASS_BIT_OBSTRUCTION_ONLY','q_exponent':67*8807,'J':J,'F':F,'C':'q-3','bit':2,'bit_C_minus_1':1,'bit_MC_J_plus_1':1,'no_carry_fails_for_assignment':True,'scope':'exact fixed payload scalar assignment; no proof that no-carry follows from a 74 zero, no evaluated graph zero, fixed-BFS guard decision or Lean/file binding'},sort_keys=True))
