#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-retry01';old=d/'research/nine-seed38-jones-prefix-rank-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'67a840d54e7ba5930f257e7f4527fd4df4fb4dff28efcd21df244bcbb40f202a','provider_preflight.py':'d6e7d0c6f806cb82cf5cef1b3f3b0b230402e9569d9194d7912bf456a68e2f4d','source-manifest.json':'881ccf0b03b654605aedabf3115903d7ebed3b71daf9dfc63a675967b7f941d5','src/DiophantineConsistency/Norm38MacroRankRaw.lean':'0cbe9cd4c27401da6726e5db2fab5dbb35eba64b8f4fbc396a79d725de8129bc','src/DiophantineConsistency/Norm38MacroRankCarry.lean':'258d07601bdeaffaf681fdaf1b5f549e055fcf3d991ddc231cb95115d8b04cf2'}.items():assert h(p/n)==v
a=(old/'src/DiophantineConsistency/Norm38MacroRankRaw.lean').read_text();b=(p/'src/DiophantineConsistency/Norm38MacroRankRaw.lean').read_text();needle='  rw [d11, Norm38MacroCuts.snoc_last]\n  rfl\n';repl='  rw [d11, Norm38MacroCuts.snoc_last]\n  simp only [Term.eval, NExpr.eval, rankRaw, Int.cast_one, Int.cast_ofNat]\n';assert a.count(needle)==1 and a.replace(needle,repl)==b
assert (old/'src/DiophantineConsistency/Norm38MacroRankCarry.lean').read_bytes()==(p/'src/DiophantineConsistency/Norm38MacroRankCarry.lean').read_bytes()
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'single raw evaluator proof repair, carry unchanged; no Lean replay'},sort_keys=True,indent=2))
