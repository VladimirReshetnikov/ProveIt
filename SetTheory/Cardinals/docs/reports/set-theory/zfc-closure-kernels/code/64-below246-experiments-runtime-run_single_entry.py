"""Reproduce the finite single-external-entry deletion screening experiment.

Requires Python3 and a C++17 compiler. Set ZFC246_BASE to the pristine
context246 archive directory. No third-party Python packages are needed.
The generated rejection records are bounded screening outcomes, not
unbounded non-equivalence certificates.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,subprocess,sys,tempfile

HERE=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--compiler',default='c++')
    p.add_argument('--skip-prepare',action='store_true',help='Reuse the existing deterministic fixtures.')
    args=p.parse_args()
    if not args.skip_prepare:
        subprocess.run([sys.executable,str(HERE/'single_entry_prepare.py')],check=True)
    with tempfile.TemporaryDirectory(prefix='zfc-runtime-search-') as tmp:
        exe=Path(tmp)/'single_entry_search'
        subprocess.run([args.compiler,'-O3','-std=c++17',str(HERE/'single_entry_search.cpp'),'-o',str(exe)],check=True)
        with (HERE/'single-entry-survivors.jsonl').open('w') as out,(HERE/'single-entry-search.log').open('w') as err:
            subprocess.run([str(exe),*(str(HERE/f'single-entry-{part}.txt') for part in ('table','cases','members')),
                str(HERE/'single-entry-rejections.jsonl')],stdout=out,stderr=err,check=True)
    result=json.loads((HERE/'single-entry-search.log').read_text().splitlines()[-1])
    fixtures=json.loads((HERE/'single-entry-fixtures.json').read_text())
    reasons=Counter();examples={}
    for line in (HERE/'single-entry-rejections.jsonl').read_text().splitlines():
        row=json.loads(line)
        reasons[row[-1]]+=1
        if row[-1] not in examples:
            fixture=fixtures['rows'][row[6]]
            examples[row[-1]]=dict(deleted_state=row[0],changed_entry=row[1:3],new_action=row[3:6],
                fixture_id=row[6],fixture={k:fixture[k] for k in ('pc','kind','r','positive')})
    assert result['recipes']==980*fixtures['single_external_entry_states']
    assert sum(reasons.values())+result['survivors']==result['recipes']
    result.update(status='completed_finite_screen',baseline_sha256=fixtures['baseline_sha256'],
        eligible_states=fixtures['eligible_states'],eligible_state_count=fixtures['single_external_entry_states'],
        actions_per_state=980,fixture_count=fixtures['cases'],all_baseline_fixtures_pass=fixtures['all_baseline_cases_pass'],
        all_eligible_states_have_both_read_bits=fixtures['all_have_both_read_bits'],
        fixed_interface_states=[95,96],fuel_per_case=10000,intermediate_dispatch_budget=15,
        rejection_reasons=dict(reasons),example_rejected_fixture_by_reason=examples,
        rejection_columns=['deleted_state','source_state','source_read_bit','new_write','new_move','new_target','fixture_id','reason'],
        generated_input_sha256={name:sha(HERE/name) for name in ('single-entry-table.txt','single-entry-cases.txt','single-entry-members.txt')},
        limitation='Finite screening only. In particular step_budget and dispatcher_budget are protocol rejections, not proofs of non-halting or unbounded non-equivalence. No state lower bound follows.')
    (HERE/'single-entry-summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('recipes','survivors','case_runs','seconds','eligible_state_count','rejection_reasons')}))

if __name__=='__main__':main()
