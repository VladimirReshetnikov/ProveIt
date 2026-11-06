import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-prefix-group01-check';draft=D/'research/nine-seed38-jones-prefix-group01-draft/Norm38MacroPrefixGroup01.lean'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'e4cfe5151b28c3cebabdee86ff7b4fafe81153b47e0f6920acb50ebedbeb3fdd','provider_preflight.py':'ccee59247c75cc6924675f62bd2de9593d88eb10b57dff02c9f0b9a1556d97ae','source-manifest.json':'c05c06fff3f68ff4540cadda9c06dfb7e4b0d84d6f9863db20e9ce41d42fc1be','src/DiophantineConsistency/Norm38MacroPrefixGroup01.lean':'f0aebaa5f8a5f9cf601efc12d36bc0e14cf54373941f61071abb7898134e6926'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(draft)==pins['src/DiophantineConsistency/Norm38MacroPrefixGroup01.lean'];t=draft.read_text()
for x in ['def base','indexY Norm38MacroLanguage.seed 0','theorem prefix_B','d2.values a (Fin.last 1) = base a ^ (5 : Nat)','theorem prefix_q','d3.values a (Fin.last 2) = (base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)','theorem prefix_N','d4.values a (Fin.last 3) = ((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)','#print axioms prefix_B','#print axioms prefix_q','#print axioms prefix_N']:assert x in t,x
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Norm38MacroPrefixFirst'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],timeout=300));assert s['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and s['selected'][imports[0]]['sha256']=='a69ba5536b935e388c616cc6c624ecb8da8aaef052b3350bc09d327dd8272c9a'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=300));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producer':s['selected'][imports[0]],'scope':'Three short-prefix values only; no full recipe entry transport or semantic graph equality.'},indent=2,sort_keys=True))
