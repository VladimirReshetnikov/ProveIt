#!/usr/bin/env python3
"""Inspect retained generic rank reduction rebuild; no Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/pell-rank-generic-rebuild';s=P/'PellRankReduction.lean';o=P/'observations/attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None
assert sha(P/'run.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name)=='fa624649df7e97d02e08f069cde8c99c36fd0a6e1d0191629fa6498c8268bdc5'
assert sha(root/'PellRankReduction.olean')==t['object_sha256']=='1cb551f5865a5c7a2ba6cdf762415181cef24a01dc5666a1ca9d5bd529f27325'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256']
assert (o/'stdout').read_text()=="'TenPositivePellRankReduction.rank_to_main_index' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
old=pathlib.Path('/tmp/pell-rank-reduction-2v7bmiw4/PellRankReduction.lean');reference=D/'research/pell-rank-reduction-prototype/PellRankReduction.lean';assert sha(old)==sha(reference)=='8ebe1aa951f7a6c21709c6086b59fba29a9c4511e7fb008070baade612047e8d';assert old.read_text().replace('import SignedRankIndex\n','import DiophantineConsistency.ArithmeticPellResidueAux\n',1)==s.read_text()
assert not re.search(r'\b(?:sorry|admit)\b',s.read_text());imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['DiophantineConsistency.ArithmeticPellResidueAux']
rel=imports[0].replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
assert p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items())
print(json.dumps({'status':'PASS','source_sha256':sha(s),'old_source_sha256':sha(old),'direct_module':imports[0],'direct_path':str(p),'direct_sha256':sha(p),'object_sha256':t['object_sha256'],'lean_replayed':False},indent=2,sort_keys=True))
