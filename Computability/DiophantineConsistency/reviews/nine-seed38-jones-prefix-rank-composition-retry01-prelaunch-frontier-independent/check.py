#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-composition-retry01';old=d/'research/nine-seed38-jones-prefix-rank-composition-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'b71746d625e658b655b75eb2c8ddae4d6639f42377b594db7cab5fe581ae14b6','provider_preflight.py':'09e6495defe334d6993f37a56a27494f8933f153e76e2fcdde974c02c6b42610','source-manifest.json':'bd9779aa624b712c3fb390bd069b7dddc8bfca3267e3b5e184dd37c823bebde8','src/DiophantineConsistency/Norm38MacroRankComposition.lean':'e5c1a4595a648a39adf5601c318528e470e19c5ebaa89367520318f101754449'}.items():assert h(p/n)==v
a=(old/'src/DiophantineConsistency/Norm38MacroRankComposition.lean').read_text();b=(p/'src/DiophantineConsistency/Norm38MacroRankComposition.lean').read_text();needle='  rw [d10_B_eq_b_pow, rankRaw_eq_rankCode]\n';repl=needle+'  have h : ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc : Fin 10) = ⟨0, by decide⟩ := by decide\n  rw [h]\n';assert a.count(needle)==1 and a.replace(needle,repl)==b
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'proof-only Fin-zero normalization retry; no Lean replay'},sort_keys=True,indent=2))
