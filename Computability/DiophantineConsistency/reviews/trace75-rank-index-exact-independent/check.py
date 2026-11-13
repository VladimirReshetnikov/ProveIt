#!/usr/bin/env python3
"""Inspect rank-index and rank-exact author receipts without Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
cases=[('Trace75RankIndex','rankindex-attempt02','run-rankindex-v2.py','1532fc93288929e13209bc97d4bc4d3946e5cbdfea91d649d2716d4c91011f28','9eeb3bbba40a1cb450220a8b64592c5ece3838d3f6093f6955d8c3e3f79cf248','graph_rank_auxiliary',['Trace75JoinedSquare','Trace75Rank','Trace75SignedRank']),('Trace75RankExact','rankexact-attempt01','run-rankexact.py','0e5c5e4e05a934a86d83d619066e943bda3c83fab3156683874d2de0ad0e2c5f','26c9d2ab4e3a06a3f72906eb1a2b2604081324f1488fc1308f594ec3985436ee','graph_rank_exact',['Trace75RankIndex','Trace75MainIndex','PellRankReduction'])]
for mod,attempt,runner,source,obj,thm,imports in cases:
 s=P/(mod+'.lean');o=P/'observations'/attempt;t=json.loads((o/'terminal.json').read_text());root=Path(t['output_root']);assert t['exit']==0 and t['reason'] is None
 assert sha(P/runner)==t['runner_sha256'] and sha(s)==sha(o/'source.txt')==sha(root/s.name)==t['inputs'][str(s)]==source and sha(root/(mod+'.olean'))==t['object_sha256']==obj
 for path,h in t['inputs'].items():assert sha(path)==h,path
 assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'] and not (o/'stderr').read_text()
 assert ' '.join((o/'stdout').read_text().split())==f"'{mod}.{thm}' depends on axioms: [propext, Classical.choice, Quot.sound]"
 assert not re.search(r'\b(?:sorry|admit)\b',s.read_text()) and re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M)==imports
 for name in imports+['Trace75JoinedSquare','Trace75SignedRank','Trace75Rank','DiophantineConsistency.TenPositiveTrace75']:
  rel=name.replace('.','/')+'.olean';path=next((Path(x)/rel for x in t['lean_path'].split(':') if (Path(x)/rel).is_file()),None);assert path and any(Path(q).resolve()==path.resolve() and h==sha(path) for q,h in t['inputs'].items()),name
  print(mod,name,path,path.resolve(),sha(path))
failed=P/'observations/rankindex-attempt01';assert json.loads((failed/'terminal.json').read_text())['exit']!=0 and 'Application type mismatch' in (failed/'stdout').read_text();assert sha(failed/'source.txt')!=cases[0][3]
print('PASS source, object, diagnostics, direct and nearby post-hoc selection; initial RankIndex failed')
print('No Lean replay, complete producer/package/dynamic ancestry, or external file identity claim')
