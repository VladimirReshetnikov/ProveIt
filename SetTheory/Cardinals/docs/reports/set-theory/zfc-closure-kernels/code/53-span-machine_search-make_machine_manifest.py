#!/usr/bin/env python3
"""Collect stable search summaries and audited boundaries for the report."""
import csv,hashlib,json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def digest(path):
    h=hashlib.sha256()
    with path.open('rb')as source:
        for block in iter(lambda:source.read(1024*1024),b''):h.update(block)
    return h.hexdigest()

def main():
    definitions=[
        ('all_actions','action_search.cpp','all_actions.audit.json',1008,2,2,
         './action_search action_data all_actions 600 0 46 0'),
        ('target_control','action_search.cpp','target_control.audit.json',251,2,2,
         './action_search action_data target_control 600 0 46 1'),
        ('multi_target_degree3','action_search_multi.cpp','multi_target_degree3.audit.json',251,3,3,
         './action_search_multi multi_data multi_target_degree3 300 3 3 1'),
        ('multi_degree3','action_search_multi_restart.cpp','multi_degree3.audit.json',1008,3,3,
         './action_search_multi_restart multi_data multi_degree3 600 3 3 0'),
        ('multi_target_degree4plus','action_search_multi.cpp','multi_target_degree4plus.audit.json',251,4,9,
         './action_search_multi multi_data multi_target_degree4plus 600 4 9 1'),
    ]
    runs=[]
    for prefix,source,audit_name,actions,mind,maxd,command in definitions:
        summary=list(csv.DictReader((ROOT/(prefix+'.summary.tsv')).open(),delimiter='\t'))
        audit_path=ROOT/audit_name
        audit=json.loads(audit_path.read_text())if audit_path.exists()else None
        record={'prefix':prefix,'source':source,'source_sha256':digest(ROOT/source),
            'actions_per_incoming':actions,'minimum_degree':mind,'maximum_degree':maxd,
            'reproduce_command':command,'audit_path':audit_name,'audit_status':None if audit is None else audit['status'],
            'attempts_including_interrupted':sum(int(row['checks'])for row in summary),
            'elapsed_seconds':float(summary[-1]['seconds']),
            'ledger_path':prefix+'.ledger.tsv','ledger_bytes':(ROOT/(prefix+'.ledger.tsv')).stat().st_size,
            'ledger_sha256':None if audit is None else audit['ledger_sha256'],
            'frontier_path':prefix+'.frontier.tsv','frontier_rows':len((ROOT/(prefix+'.frontier.tsv')).read_text().splitlines()),
            'complete_deletions':[int(row['deleted'])for row in summary if int(row['remaining'])==0],
            'partial_deletions':[int(row['deleted'])for row in summary if int(row['remaining'])>0],
            'survivors':sum(int(row['survivors'])for row in summary),
            'nodes':sum(int(row['nodes'])for row in summary),
            'pruned_assignments':sum(int(row['pruned'])for row in summary),
            'case_prefix_reuse':source=='action_search_multi.cpp'}
        if audit is not None:
            record['planned_assignments']=audit['planned']
            record['remaining_assignments']=audit.get('remaining',0)
            record['branches']=audit['branches']
            assert record['planned_assignments']==record['pruned_assignments']+record['survivors']+record['remaining_assignments']
        runs.append(record)
    variant=json.loads((ROOT/'variant_folds.summary.json').read_text())
    variant.update({'source':'variant_fold_search.cpp','source_sha256':digest(ROOT/'variant_fold_search.cpp'),
        'ledger_path':'variant_folds.ledger.tsv','ledger_sha256':digest(ROOT/'variant_folds.ledger.tsv'),
        'input_preparation':'variant_data/preparation.json'})
    manifest={'scope':'Finite conditional state-reduction searches. No accepted smaller machine and no state lower bound.',
        'source_commit':'43026ff42f0939f09b9e95495248cfadcad38e38',
        'original_table_sha256':'939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713',
        'ordinary_case_fuel':1000,'original_guard_cases':8391,'original_blank_prefix_steps':82552,
        'runs':runs,'variant_control':variant,
        'all_audits_complete':all(x['audit_status']=='PASS'for x in runs),
        'notes':['Raw ledgers remain unchanged; lossless packing must reconstruct their exact SHA256.',
          'Wall-clock-bounded reproduction can end at a different frontier on a different host.',
          'Partition audits validate coverage, not semantic failure for every rejected machine.',
          'The 185033-entry Python/C++ target-control comparison is exact; the 1472-event full-action semantic replay is sampled.',
          'Counts for overlapping families are not additive.']}
    (ROOT/'machine_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'all_audits_complete':manifest['all_audits_complete'],'runs':[(x['prefix'],x['audit_status'])for x in runs]}))

if __name__=='__main__':main()
