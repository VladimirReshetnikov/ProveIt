#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'9db0c8a23c101af18f39eb585882cfd1197fcec6cb9eed398382c6690a083148','provider_preflight.py':'96a2567b6c3f5e250792cfd198a630aa2968c6f843431739f357fb8cb7f0bda7','source-manifest.json':'32036f20b4430c211e06a7e384c2bc03f220e3a2f19ac347e3bde536b6162ffb'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroRankRaw','a22def05d850d3bddb2685a45f016493ae3a10b9b931d2b137039ba9209ecfe6',['DiophantineConsistency.Norm38MacroPrefixCarrySums','DiophantineConsistency.Norm38MacroPrefixCarryOthers'],'d11_rank_raw'),('Norm38MacroRankCarry','258d07601bdeaffaf681fdaf1b5f549e055fcf3d991ddc231cb95115d8b04cf2',['DiophantineConsistency.Norm38MacroRankRaw'],'d11_rank_carried')];assert len(rows)==2
for row,(n,sha,imports,t) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==imports;assert re.findall(r'^theorem (\w+)',s,re.M)==[t] and re.findall(r'^#print axioms (\w+)',s,re.M)==[t]
 for prefix,idx,casts in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(prefix)==int(idx)+1+casts.count('.castSucc')
raw=(p/'src/DiophantineConsistency/Norm38MacroRankRaw.lean').read_text();assert [int(x) for x in re.findall(r'd10\.values a ⟨(\d+), by decide⟩',raw)]==list(range(9))
carry=(p/'src/DiophantineConsistency/Norm38MacroRankCarry.lean').read_text();assert all(t in carry for t in ['d10_b_carry','d10_B_carry','d10_q','d10_N','d10_e_carry','d10_ell_carry','d10_lambda_carry','d10_g_carry','d10_theta_carry'])
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'two uncompiled symbolic rank-node statements; no Lean replay'},sort_keys=True,indent=2))
