#!/usr/bin/env python3
import pathlib,json,hashlib,os
D=pathlib.Path(__file__).resolve().parents[2];T=D/'research/current2011-four-port-byte-tuple';A=T/'attempt03'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'result.json').read_text());o=json.loads((A/'outer-observation.json').read_text());s=(A/'source.lean').read_text();log=(A/'compile.log').read_text()
assert sha(A/'source.lean')=='80b6c77ee62fc49dba6e047f90caf350801e72fc4fd3176073b54276f57a5f52'
assert sha(A/'result.json')=='7d1303ce65bae45724a7c27bc96e5500ad74028b4ae4ef418561dfff368b70f2'
assert sha(T/'check03.py')==d['runner_sha256']=='c60a561147c012aff525a42e7d8712f8706eb7b02f6d41b2f101c43d193c03ea'
assert (d['status'],d['exit'],o['session_id'],o['observed_outer_exit'],d['stop_reason'],d['object_sha256'])==('FAILED',1,2118,1,None,None)
assert sha(A/'compile.log')==d['log_sha256'] and '(kernel) excessive memory consumption' in log and 'decoded_eq_ports]' in log
for x in ['import FourByteGeneric','import BetaKernelPair','import MaskPair','FourByteGeneric.assemble','BetaKernelPair.decode_pair.1','BetaKernelPair.decode_pair.2','MaskPair.decode_pair.1','MaskPair.decode_pair.2']:assert x in s
assert d['guards_stable'] and d['guards_before']==d['guards_after'] and len(d['guards_after'])==874
for key,v in d['guards_after'].items():
 p=pathlib.Path(v.get('path',key.rsplit(':',1)[-1]) if v else key.rsplit(':',1)[-1])
 if p==T/'CurrentFourPortBytes.lean':assert sha(A/'source.lean')==v['sha256'];continue
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
print(json.dumps({'status':'PASS','outer_session':2118,'outer_exit':1,'lean_exit':1,'recorded_guard_slots':874,'scope':'Failed kernel check, no tuple theorem, no Lean replay.'},indent=2))
