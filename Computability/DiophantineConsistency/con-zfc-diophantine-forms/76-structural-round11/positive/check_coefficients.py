from pathlib import Path
import json,gzip,hashlib
p=Path(__file__).resolve().parent/'native';x=json.loads((p/'ACTIVE_BINDING.json').read_text())
for name,d in x['ports'].items():
 z=(p/d['file']).read_bytes();raw=gzip.decompress(z)
 if hashlib.sha256(z).hexdigest()!=d['sha256_gzip'] or hashlib.sha256(raw).hexdigest()!=d['sha256_raw']:raise RuntimeError(name+' hash')
 v=int.from_bytes(raw,'little')
 if v.bit_length()!=d['bits'] or len(raw)!=d['raw_bytes']:raise RuntimeError(name+' size')
 if name=='beta' and v!=(1<<590069)-1:raise RuntimeError('radix')
print('PASS: complete compact44 tuple, four compressed and raw hashes and lengths')
