from pathlib import Path
import importlib.util,json,time
B=Path(__file__).resolve().parent.parent;S=B/'work/state_reduction';O=B/'review-logs/partial-journals.json'
spec=importlib.util.spec_from_file_location('recovered_partition',S/'audit_degree2_partition.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
results=sorted(p for p in S.glob('two_action_*_gap.json')if p.with_suffix('.jsonl.gz').is_file())
assert len(results)==32
out=dict(status='RUNNING_PARTIAL_DELIVERY',scope='Only the 32 recovered complete journals; exact assignment partitions, not rerun symbolic diagnostic outcomes. The promised 36-domain family remains incomplete.',checks=[],missing_result_domains=[89,92,98],missing_journal_domains=[82,89,92,98])
start=time.monotonic()
def save():
 out['seconds']=time.monotonic()-start;O.write_text(json.dumps(out,indent=2)+'\n')
save()
for p in results:
 r=m.audit(p);out['checks'].append(r);save();print('PASS recovered domain',r['deleted_state'],'pruned',r['pruned'],'remaining',r['remaining'],flush=True)
out.update(status='PASS_32_RECOVERED_PARTITIONS_ONLY',domain_count=len(out['checks']),total_pruned=sum(r['pruned']for r in out['checks']),total_remaining=sum(r['remaining']for r in out['checks']),survivors=sum(r['survivors']for r in out['checks']),total_nodes=sum(r['nodes']for r in out['checks']),checked_domains=sorted(r['deleted_state']for r in out['checks']))
assert out['total_pruned']==32*1008**2 and out['total_remaining']==0 and out['survivors']==0
save();print({k:v for k,v in out.items()if k not in ('checks','scope')})
