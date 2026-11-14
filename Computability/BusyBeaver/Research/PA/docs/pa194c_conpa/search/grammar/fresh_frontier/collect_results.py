#!/usr/bin/env python3
"""Collect completed logs without certifying searched machine semantics."""
from pathlib import Path
import hashlib,json,re,sys

P=Path(__file__).resolve().parent
runs=[]
for name,family,seed in [('D','S',2026111408),('E','C',2026111409)]:
    lines=(P/f'run{name}.log').read_text().splitlines()
    assert lines[0]==f'INITIAL 1 best 60 seed {seed}'
    m=re.fullmatch(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([\d.]+)',lines[-1])
    if m:
        iterations,accepted,hits,best=map(int,m.groups()[:4]);elapsed=float(m[5])
        completed=True
    else:
        assert '--allow-partial' in sys.argv, 'Use --allow-partial for interrupted logs'
        progress=[re.fullmatch(r'CYCLE (\d+) best (\d+) now (\d+) pool (\d+) iterations (\d+) nodes (\d+) seconds ([\d.]+)',line) for line in lines]
        progress=[x for x in progress if x]
        assert progress,'No completed progress record'
        p=progress[-1];iterations=int(p[5]);best=int(p[2]);elapsed=float(p[7])
        accepted=None;hits=sum(line.startswith('HIT ') for line in lines);completed=False
    assert (P/f'check{family}.audit').read_text().strip()=='0 0 68 8 60'
    runs.append({'run':name,'controller':family,'seed':seed,
                 'source':'search193_occ.cpp','input':f'start194alt{family}.txt',
                 'budget_seconds':600,'iterations':iterations,
                 'accepted_moves':accepted,'hits':hits,
                 'best_penalized_score':best,'elapsed_seconds':elapsed,
                 'completed':completed,
                 'count_scope':('Final DONE record' if completed else 'Last complete CYCLE progress record; no DONE; no extrapolation'),
                 'initial_raw_readers':68,'initial_compatible_folds':8,
                 'initial_effective_readers':60,'initial_penalized_score':60})
local=[]
for family in ['S','C']:
    for radius,steps in [(4,120),(8,200)]:
        for kind,code,expected in [('local','action_merge_all.cpp',194),
                                   ('eliminate','incoming_eliminate.cpp',172)]:
            prefix=f'{kind}_alt{family}_r{radius}'
            lines=(P/(prefix+'.log')).read_text().splitlines()
            candidates=(P/(prefix+'.jsonl')).read_text().splitlines()
            assert len(lines)==expected
            local.append({'controller':family,'source':code,
                          'input':f'pa194alt{family}.native.tm',
                          'radius':radius,'maximum_local_steps':steps,
                          'context':'Arbitrary-tape local closure from native start control 74',
                          'processed_controls':len(lines),'returned_candidates':len(candidates),
                          'log':prefix+'.log','results':prefix+'.jsonl'})
included=['README.md','PROVENANCE.json','build_inputs.py','check_inputs.py',
          'collect_results.py','input_receipt.json','input_validation.json',
          'input_validation.log','new194.grammar.json','new194.folds.json',
          'new194.unfolded202.native.tm','pa194altS.native.tm','pa194altC.native.tm',
          'start194altS.txt','start194altC.txt','leaf_attrs.txt','screen.cpp',
          'search193_occ.cpp','action_merge_all.cpp','incoming_eliminate.cpp',
          'checkS.audit','checkC.audit','runD.log','runD.csv','runE.log','runE.csv']
included += [x[k] for x in local for k in ['log','results']]
result={'status':('INTERRUPTED_PARTIAL_NO_RECORDED_TARGET_HITS' if not all(x['completed'] for x in runs) and all(x['hits']==0 for x in runs)
                  else 'COMPLETED_NO_TARGET_HITS' if all(x['hits']==0 for x in runs)
                  else 'TARGET_HIT_REQUIRES_FULL_VALIDATION'),
        'target_effective_readers_max':59,'fixed_controls':134,
        'started_utc_approx':'2026-11-14 03:52:50 UTC',
        'runs_launched_concurrently':True,'runs':runs,
        'total_proposals':sum(x['iterations'] for x in runs),
        'total_count_scope':'Sum of last fully recorded counts; interrupted runs may have performed additional unreported proposals.',
        'interruption_note':'The parent reported a user-aborted wait and instructed packaging of the interrupted snapshots without resuming the searches. No DONE record is present in either supplied log.',
        'distinct_machines_counted':False,'source_word_or_parameter_roles_changed':False,
        'additional_local_checks':local,'kernel_checked':False,
        'scope':'Heuristic grammar reassociation with bounded compatible-fold screening and supplementary bounded local reductions. No lower bound and no claim that every searched candidate is semantically invalid.',
        'sha256':{f:hashlib.sha256((P/f).read_bytes()).hexdigest() for f in included}}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','total_proposals','runs']},indent=2))
