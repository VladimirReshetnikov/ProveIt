from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,time
w=Path('/tmp/adaptive86-machine-compat-rebase-v14-qo2jqgv5'); root=Path('/home/codex/.codex/worktrees/46be/Proofs'); base=root/'Computability/DiophantineConsistency'; src=base/'Lean'; research=base/'research/wang-chunk-full'; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
while True:
 s=json.loads((w/'state.json').read_text())
 if s['status']!='RUNNING':break
 time.sleep(2)
if s['status']!='PASS':print('TERMINAL',s['status'],flush=True);raise SystemExit(1)
rows=[]
for n,h in s['source_sha256'].items():
 p=(research/'machine-rebase-rank-bound-helper-v14.lean') if n.endswith('.AdaptiveDirectOrdinate86RankBoundCompat') else (research/'machine-rebase-current-fixed-forward-v14.lean') if n.endswith('.AdaptiveDirectOrdinate86FixedForward') else (research/'machine-rebase-compat-helpers-v8.lean') if n.endswith('.AdaptiveDirectOrdinate86CompatHelpers') else (research/'machine-rebase-current-orientation.lean') if n.endswith('.AdaptiveDirectOrdinate86MainOrientation') else src/('/'.join(n.split('.'))+'.lean')
 rows.append({'path':str(p.relative_to(root)),'expected':h,'actual':sha(p)})
for n,k in [('ArithmeticAdaptiveFirstDivisibility2011','first_divisibility_source_sha256'),('ArithmeticAdaptiveMainOrientation2011','main_orientation_source_sha256'),('ArithmeticAdaptiveMainCongruence2011','main_congruence_source_sha256'),('ArithmeticAdaptiveRankCongruence2011','rank_congruence_source_sha256'),('ArithmeticAdaptiveIndexComparison2011','index_comparison_source_sha256'),('ArithmeticAdaptiveStrongNorm2011','strong_norm_source_sha256'),('AdaptiveDirectOrdinate86MainOrientation','current_orientation_source_sha256'),('ArithmeticAdaptiveRankWindow2011','rank_window_source_sha256'),('AdaptiveDirectOrdinate86FixedForward','fixed_forward_source_sha256')]:
 p=src/'DiophantineConsistency'/f'{n}.lean';rows.append({'path':str(p.relative_to(root)),'expected':s[k],'actual':sha(p)})
result={'status':'PASS' if all(x['expected']==x['actual'] for x in rows) else 'FAILED','time_utc':datetime.now(timezone.utc).isoformat(),'state_sha256':sha(w/'state.json'),'sources':rows};(w/'post-terminal-sources.json').write_text(json.dumps(result,indent=2)+'\n'); print('TERMINAL SOURCE CHECK',result['status'],'rows',len(rows),flush=True)
