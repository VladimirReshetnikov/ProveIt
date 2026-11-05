#!/usr/bin/env python3
"""Read-only pinned-source/receipt inspection plus isolated non-Lean controls."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B without -O')
root=Path(__file__).resolve().parents[2];p=root/'research/current14-mf-base-only-endpoint';d=root/'research/current14-printed-port-extension-driver-v3';owned=root/'research/current14-structured-endpoint-coherent-runner-v3/owned.py'
pins={p/'runner.py':'1013bbda00819d45a8f5e652ad81b025867d7697e0e395c373e10f3b2427f7f8',p/'controls.py':'f9e60b5087fe06beada2a474672cf6ad29a884efe2a08272e4a86ba3a0d8fa15',p/'Current14LiteralPortsMF.lean':'8f7e7bc42f16d91ce118202467546160fb2364df4452a5b256ac8e1af7d00183',p/'StructuredEndpointMF.lean':'906861b83a51dd58b043da16a0d6628925128bfc1197568eb7ba09f472622a08',d/'driver.py':'6e12ae1fae6e721238ac6a052428357049f060596fd51338811eee054aad0880',d/'guards.py':'e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3',d/'owned.py':'60859f538a7069d90f3f44871613fd2ef96c0ea738c9313cd1971d851b4b33ca',d/'deps.py':'d3f898f522e7d30756df4fb011b12beff44e338158d6d692e567caff748b8284',owned:'51f3ec69c2f4a11cfe118072f724a110c976a3557d1c68553ebb6a9c8108f498'}
for f,h in pins.items():
 if hashlib.sha256(f.read_bytes()).hexdigest()!=h:raise RuntimeError('pin mismatch '+str(f))
run=subprocess.run([sys.executable,'-I','-S','-B',str(p/'controls.py')],capture_output=True,text=True,timeout=20,check=True)
r=json.loads(run.stdout)
if run.stderr or r['status']!='PASS' or 'axiom-report' not in r['scope']:raise RuntimeError('controls mismatch')
base=Path('/tmp/current14-standard-fresh-build-20261104');state=json.loads((base/'state.json').read_text());want={k for guard in state['outputs'].values() for k,v in guard.items() if v is not None};actual={str(x) for x in (base/'lib').rglob('*') if x.is_file() or x.is_symlink()}
if want!=actual or len(want)!=1000:raise RuntimeError('current base inventory differs')
print(json.dumps({'status':'PASS_STATIC_REVIEW_CONTROLS','source_pins':{str(k):v for k,v in pins.items()},'controls':r,'current_base_files':len(actual),'scope':'Independent pinned-source audit and synthetic controls only; no Lean, runner or endpoint check launched.'},sort_keys=True))
