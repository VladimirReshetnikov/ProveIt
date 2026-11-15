#!/usr/bin/env python3
"""Portable replay of the PA194H5X physical-reduction experiments.

Default: hashes, positive controls, complete-window quotient and elimination,
and the exact two-cell shared-selector screen. --extended replays longer
finite searches; --regenerate-contexts reruns the universal symbolic collectors.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys,tempfile
if not __debug__ or sys.flags.optimize:
 raise SystemExit('Run with assertions enabled; disable -O and PYTHONOPTIMIZE.')
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--work',type=Path)
p.add_argument('--extended',action='store_true')
p.add_argument('--regenerate-contexts',action='store_true')
a=p.parse_args();work=(a.work or Path(tempfile.mkdtemp(prefix='pa194-runtime-'))).resolve();work.mkdir(parents=True,exist_ok=True);bins=work/'bin';bins.mkdir(exist_ok=True)
for n,h in json.loads((HERE/'INPUT_SHA256.json').read_text()).items():
 assert hashlib.sha256((HERE/n).read_bytes()).hexdigest()==h,('Input changed',n)
programs=['joint_return_merge','eliminate_control','merge_compensated','shared_selector_general','allocation_tagged','neutral_rows','append_search','append_pair_micro']
for name in programs:
 subprocess.run(['g++','-O3','-std=c++17',str(HERE/'code'/(name+'.cpp')),'-o',str(bins/name)],check=True)

def run(name,cmd,empty=True):
 r=subprocess.run([str(x)for x in cmd],capture_output=True,text=True,check=True)
 (work/(name+'.stdout')).write_text(r.stdout);(work/(name+'.stderr')).write_text(r.stderr)
 if empty:assert not r.stdout,('Unexpected nomination; inspect it before accepting or rejecting',name)
 print(name, r.stderr.splitlines()[-1]if r.stderr.splitlines()else'PASS',flush=True)
 return r
machine=HERE/'inputs/PA194H5X';table=machine/'machine.native.tm';windows=HERE/'results/PA194H5X_complete6.tsv'
positive=HERE/'positive_control'
r=run('positive_elimination',[bins/'eliminate_control',positive/'duplicate.tm',6,100,positive/'contexts.tsv'],False)
assert any(json.loads(x)['remove']==1 for x in r.stdout.splitlines())
r=run('positive_compensation',[bins/'merge_compensated',positive/'duplicate.tm',6,160,positive/'contexts.tsv',1,3,2,0],False)
assert r.stdout
r=run('quotient',[bins/'joint_return_merge',table,6,160,windows]);assert re.search(r'DONE pairs 18721 trials 26200136 combos 176844 hits 0\b',r.stderr)
r=run('incoming_elimination',[bins/'eliminate_control',table,6,160,windows]);assert re.search(r'DONE controls 193 edges 197 trials 132784 hits 0\b',r.stderr)
r=run('shared_selector',[bins/'shared_selector_general',table]);assert re.search(r'DONE pairs 14 configurations 672 row_trials 259392 joint_pairs 0 hits 0\b',r.stderr)
secondary=HERE/'inputs/PA194JH5X/machine.native.tm'
r=run('secondary_quotient',[bins/'joint_return_merge',secondary,6,160,HERE/'results/PA194JH5X_source6.tsv']);assert re.search(r'DONE pairs 18721 trials 25551656 combos 183698 hits 0\b',r.stderr)
run('secondary_incoming_elimination',[bins/'eliminate_control',secondary,6,160,HERE/'results/PA194JH5X_source6.tsv'])
r=run('secondary_shared_selector',[bins/'shared_selector_general',secondary]);assert 'DONE pairs 15 configurations 752 row_trials 290272 joint_pairs 0 hits 0' in r.stderr
if a.regenerate_contexts:
 source=work/'source6.tsv';boxes=work/'box6.tsv';complete=work/'complete6.tsv'
 for name,cmd in [
 ('source_contexts',[sys.executable,'-B',HERE/'code/collect_source_contexts.py',table,machine/'sites.json',machine/'instructions.json',source,6]),
 ('box_contexts',[sys.executable,'-B',HERE/'code/collect_box_contexts.py',machine,'--checker',HERE/'literal_checker','--radius',6,'--output',boxes,'--startup-steps',57922]),
 ('complete_contexts',[sys.executable,'-B',HERE/'code/merge_complete_contexts.py',machine,source,boxes,complete])]:run(name,cmd,False)
 for actual,expected in[(source,'PA194H5X_source6.tsv'),(boxes,'PA194H5X_box6.tsv'),(complete,'PA194H5X_complete6.tsv')]:
  assert actual.read_bytes()==(HERE/'results'/expected).read_bytes(),('Context bytes differ',expected)
 print('Regenerated all universal context files byte-for-byte.',flush=True)
if a.extended:
 r=run('secondary_allocations',[bins/'allocation_tagged',HERE/'inputs/PA194JH5X/raw.native.tm',10,0,1]);assert 'DONE layouts 40320 best_folds 9 hits 0' in r.stderr
 r=run('all_allocations',[bins/'allocation_tagged',machine/'raw.native.tm',10,0,0]);assert 'DONE layouts 362880 best_folds 9 hits 0' in r.stderr
 run('coupled_compensators',[sys.executable,'-B',HERE/'code/run_compensators.py',table,windows,work/'compensators',bins/'merge_compensated'],False)
 c=json.loads((work/'compensators/summary.json').read_text());assert c['rows']==384 and c['hits']==0
 r=run('neutral_rows',[bins/'neutral_rows',table,6,160,windows],False)
 neutral=work/'neutral.jsonl';neutral.write_text(r.stdout);assert r.stdout==(HERE/'results/PA194H5X_complete_neutral.jsonl').read_text()
 run('selected_neutral_quotients',[sys.executable,'-B',HERE/'code/run_selected_neutral_quotients.py',table,windows,neutral,work/'selected','--merger',bins/'joint_return_merge'],False)
 c=json.loads((work/'selected/receipt.json').read_text());assert(c['all_neutral_rows'],c['selected_candidates'],c['hits'])==(343,59,0)
 gh=HERE/'inputs/PA194AX11GH/machine.native.tm'
 r=run('single_row_append',[bins/'append_search',gh,HERE/'inputs/append_cases.txt']);assert 'DONE trials 35696 screened 7 hits 0 steps 728755426' in r.stderr
 r=run('two_row_append',[bins/'append_pair_micro',gh]);assert 'DONE trials 602176 first_pass 0 hits 0 steps 10495179' in r.stderr
print(json.dumps({'status':'PASS','work':str(work),'extended':a.extended,'regenerated_contexts':a.regenerate_contexts,'scope':'Reproduced finite experiments and optional universal symbolic context coverage; no sub-194 result or general lower bound is asserted.'}),flush=True)
