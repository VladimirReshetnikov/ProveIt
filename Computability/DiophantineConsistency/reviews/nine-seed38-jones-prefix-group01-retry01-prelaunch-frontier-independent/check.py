import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-prefix-group01-retry01';old=D/'research/nine-seed38-jones-prefix-group01-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'450c9e47f879febe22ea1fa61960c9cb746699434940ac03941c6c66a76558e0','provider_preflight.py':'ccee59247c75cc6924675f62bd2de9593d88eb10b57dff02c9f0b9a1556d97ae','source-manifest.json':'3dc19eac847c2e516695d7bdf12b087d3768b45def573a70939120bba3c5a974','src/DiophantineConsistency/Norm38MacroPrefixGroup01.lean':'07df9f3ac1f7fa7d6c02241385d81added00c92994060dcfb9070a99ce871cd9'}
for k,h in pins.items():assert sha(p/k)==h,k
before=(old/'src/DiophantineConsistency/Norm38MacroPrefixGroup01.lean').read_text();after=(p/'src/DiophantineConsistency/Norm38MacroPrefixGroup01.lean').read_text()
for a,b in [('change (d2.values a ⟨1, by decide⟩) ^','change (d2.values a (Fin.last 1)) ^'),('change (d3.values a ⟨2, by decide⟩) ^','change (d3.values a (Fin.last 2)) ^')]:assert before.count(a)==1;before=before.replace(a,b)
assert before==after and sha(old/'provider_preflight.py')==sha(p/'provider_preflight.py') and sha(old/'attempt01/state.json')=='b5be6f0badd09341fe0ea3c5f8bf0b2022ff52862741f966f14288074e97cfcf' and sha(old/'attempt01/Norm38MacroPrefixGroup01-compile.txt')=='a320a8be9c5f41ef3a524005e2840bf5cce1da95fc301919f6d87d8043629310'
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Norm38MacroPrefixFirst'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and s['selected'][imports[0]]['sha256']=='a69ba5536b935e388c616cc6c624ecb8da8aaef052b3350bc09d327dd8272c9a'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producer':s['selected'][imports[0]],'scope':'Two Fin.last proof-expression fixes; no Lean theorem or full graph semantics.'},indent=2,sort_keys=True))
