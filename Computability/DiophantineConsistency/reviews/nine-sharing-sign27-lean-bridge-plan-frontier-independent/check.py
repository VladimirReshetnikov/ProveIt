#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-sextic-lean-draft';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'generate.py':'90d55b7635eccf93acb19cf7644bdd84d47090fc07f639e2b54754ef6adb86ae','check.py':'ce082329d66bbcbe465f2e78318c08b89f4a5430c5e485e5441132adeb1dd28a','check_bridge.py':'7c4ceb83dd93bdb2060ed9f409982e98e61b725fa64d66020241ef88face8f85','SharingSeed27Sextic.lean':'ef5a3f69db7045c34ae66205066fbfaf3edb544384648dc1f961a4f0bf1e5dca','SharingSeed27BridgeDraft.lean':'d7c481a27d8a753a7bcafc29c0523db584097ec71ec6bdaa0ca9b7cabff5719c'}.items():assert H(P/n)==h
plan=D/'research/nine-sharing-sign27-lean-bridge-plan/README.md';assert H(plan)=='b5698aeb200a37fe72066d38f6a2e3e99c20a141fe52e118a6edc72fc7e905d5';txt=plan.read_text()
for x in ['v21 = u + 1','v22 = u * (u + 2)','ι_nonneg','zero_or_succ','ι_injective','No Lean syntax, predecessor theorem, zero bridge']:assert x in txt
seed=D/'research/nine-sharing-sign27-sextic-normalized-root-candidate/seed.json';assert H(seed)=='5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d';j=json.loads(seed.read_text());assert j['witness_count']==27 and len(j['residuals'])==18 and (j['old_root_coordinate'],j['old_product_coordinate'],j['new_predecessor_coordinate'],j['removed_norm'])==(21,22,21,'N1')
s=(P/'SharingSeed27BridgeDraft.lean').read_text();blocks=re.findall(r'!\[([^\]]+)\]',s);assert len(blocks)==2
lift=[x.strip() for x in blocks[0].split(',')];drop=[x.strip() for x in blocks[1].split(',')];assert lift==[f'v {i}' for i in range(21)]+['v 21 + 1','v 21 * (v 21 + 2)']+[f'v {i}' for i in range(22,28)];assert drop==[f'v {i}' for i in range(21)]+['u']+[f'v {i}' for i in range(23,29)]
assert not re.search(r'(?m)^\s*(?:theorem|lemma)\b|\b(?:sorry|admit)\b',s) and 'def ForwardTarget' in s and 'def BackwardTarget' in s and '∃ u : V, v 21 = u + 1 ∧ v 22 = u * (u + 2)' in s
for script,result in [('check.py','result.json'),('check_bridge.py','bridge-result.json')]:
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/script)],capture_output=True,text=True,check=True,timeout=120);assert json.loads(r.stdout)==json.loads((P/result).read_text())
print(json.dumps({'status':'PASS_SOURCE_REVIEW','residuals':18,'lift_coordinates':29,'drop_coordinates':28,'scope':'source mapping and AST transcription only; predecessor/zero bridge/endpoint remain open'},sort_keys=True,indent=2))
