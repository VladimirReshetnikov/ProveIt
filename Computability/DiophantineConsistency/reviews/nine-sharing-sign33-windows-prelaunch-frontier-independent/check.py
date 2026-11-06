import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-windows-check';draft=D/'research/nine-sharing-sign33-signs-draft/Sign33Draft.lean';old=D/'research/nine-sharing-sign33-strong-f-retry01'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'7a55455c88d09c68b4449df1a7886e9a5c4ba64c45eb89ef9653cbd98c3ec396','provider_survey.py':'b20bdfa2c26708c6bff944dd5d5917d1b6371cad55a4f528fa01e7551fa41b48','source-manifest.json':'62c46428842b3c8ea5d92cb60de428d82a6caa586c19ac0cb729600c1e1f1ace','src/DiophantineConsistency/Sign33Windows.lean':'01c97dbea6ac97215cc0b50eea54052b1e6d7ab29977902db2568168223a255f'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(draft)=='c6cf5a3c39c00188050a71f5a7e95d93884344db9b275bc095b224527a49fb4d';ds=draft.read_text();block=ds[ds.index('theorem windows_from_maintained_norms'):ds.index('\nend ModelWindows',ds.index('theorem windows_from_maintained_norms'))];src=(p/'src/DiophantineConsistency/Sign33Windows.lean').read_text();assert block in src
for x in ['(hbeta : 0<beta)','(hMC : MC<beta)','(hMF : MF<2*beta)','htransport hfirst hmain hstrict haux','maintained_first_indices beta K MC MF J F alpha z f i T s w N eta zeta y gamma','0<q-F-alpha ∧ R+2<E ∧ 2*R<c']:assert x in block,x
olds=(old/'provider_survey.py').read_text();news=(p/'provider_survey.py').read_text();assert olds.replace("'Sign33StrongF'","'Sign33Windows'")==news
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;imports=['DiophantineConsistency.ArithmeticPellFirstIndex','DiophantineConsistency.ModelDifferenceRing'];assert rows[0]['imports']==imports
s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33Windows.olean' not in s['links']
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'Exact copied hypotheses and proof plus point producer survey; no Lean theorem, derived concrete hypotheses or sign bridge.'},indent=2,sort_keys=True))
