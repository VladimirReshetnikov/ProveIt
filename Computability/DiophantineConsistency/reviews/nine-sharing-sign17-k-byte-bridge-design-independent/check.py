#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-byte-bridge-design';sha=lambda b:hashlib.sha256(b).hexdigest();assert sha((p/'check_layout.py').read_bytes())=='8b86dcde6572072ca3ac42b57149a6d57eaca6b84298bd067a202adb1046f228'
coeff=root/'research/padding-staircase-independent/coefficients.json';seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(coeff.read_bytes())=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93' and sha(seed.read_bytes())=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';c=json.loads(coeff.read_text());assert len(c)==3297 and all(type(x)==int and x>=0 for x in c) and all(x==0 for x in c[986:]);binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256']=='64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7' and len(raw)==11868
# Independently extract actual little-endian radix digits from the raw integer.
r=1<<47;value=int.from_bytes(raw,'big');digits=[]
while value:value,x=divmod(value,r);digits.append(x)
assert len(digits)==2021 and digits[18]==1 and digits[2020]==1
for j in range(2021):
 expected=(c[1005-j] if 20<=j<=1005 else 0)+(1 if j in (18,1004,2020) else 0)
 assert 0<=expected<r and digits[j]==expected,(j,expected,digits[j])
assert digits[1004]==c[1]+1 and digits[1005]==c[0] and digits[20]==c[985] and all(x==0 for x in digits[:18]+digits[19:20]+digits[1006:2020]);assert 2016==252*8 and 2021-2016==5 and len(raw)==252*47+24
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-coefficient-bytes-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_LAYOUT','digits':len(digits),'collision_index':1004,'coefficient_at_collision':c[1],'max_digit':max(digits),'radix':r,'full_47_byte_blocks':252,'tail_bytes':24,'scope':'independently decoded external snapshot, no Lean digit, JSON or file theorem'},indent=2))
