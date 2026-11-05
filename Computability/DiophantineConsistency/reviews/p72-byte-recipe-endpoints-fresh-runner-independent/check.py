#!/usr/bin/env python3
"""Read-only byte-endpoint client pin check; no Lean invocation."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/p72-byte-recipe-endpoints-fresh';fresh=Path('/tmp/p72-current-base-extension-attempt02-20261105')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(q/'run.py')=='e14af51406e092ebbd40d57f4568afdebd5eb823f3553f98ebc893e528b14bce'
assert sha(q/'P72ByteEndpoints.lean')=='d2920d8dc8bdc492d5390ec39eeb68b9cc164274ac42465dca4d9cbceb0f348f'
assert sha(q/'monitor.py')=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad'
s=q.joinpath('P72ByteEndpoints.lean').read_text();assert 'CompactBytePortsModelIff.byteP_eq' in s and 'rw [byteP_eq_ports]' in s and 'standard_translated_p13' in s and 'standard_translated_p14' in s
row=json.loads((fresh/'rows/0609.json').read_text());assert row['module']=='DiophantineConsistency.Compact44.CompactBytePortsModelIff' and row['status']=='PASS'
obj=fresh/'lib/DiophantineConsistency/Compact44/CompactBytePortsModelIff.olean';assert sha(obj)==row['object_sha256']
assert "'CompactBytePortsModelIff.byteP_eq' depends on axioms:" in (fresh/'logs/0609-compile.txt').read_text()
print(json.dumps({'status':'PASS_PRELAUNCH_SOURCE_INSPECTION_ONLY','runner_sha256':sha(q/'run.py'),'client_sha256':sha(q/'P72ByteEndpoints.lean'),'byte_provider_sha256':sha(obj),'scope':'Source and existing provider point observations; no Lean launch, file-byte or degree theorem.'},indent=2,sort_keys=True))
