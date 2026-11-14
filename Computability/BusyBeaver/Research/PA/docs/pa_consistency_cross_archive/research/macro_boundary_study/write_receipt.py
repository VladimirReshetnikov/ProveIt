"""Summarize completed log lines only; interrupted iterations are excluded."""
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).parent
def readlog(name):
    rows=[]
    for line in (HERE/'logs'/name).read_text().splitlines():
        m=re.fullmatch(r'drop (\d+) total (\d+) runs (\d+) survivors (\d+) seconds ([\d.]+)',line)
        assert m,line
        a,c,r,n,seconds=m.groups();rows.append({'deleted_state':int(a),'cumulative_assignments':int(c),'cumulative_run_calls':int(r),'survivors':int(n),'seconds':float(seconds)})
    return rows
def study(names,fixture,endpoint):
    rows=[(n,readlog(n)) for n in names]
    states=[r['deleted_state'] for _,rs in rows for r in rs]
    assert len(set(states))==len(states)
    return {'log_files':names,'completed_deleted_states':sorted(states),'deleted_state_count':len(states),
      'assignments':sum(rs[-1]['cumulative_assignments'] for _,rs in rows if rs),
      'survivors':sum(r['survivors'] for _,rs in rows for r in rs),'fixture':fixture,'endpoint':endpoint}
exact_names=['macro_folds_log.txt','macro_decoder_log.txt','macro_decoder0_log.txt','macro_decoder1_log.txt']
exact_names=[n for n in exact_names if (HERE/'logs'/n).exists()]
receipt={'status':'FINITE_SCREEN_ONLY_NO_SMALLER_MACHINE',
 'source_commit':'906367250a7f96c923147b10df392294bced7be5',
 'canonical_input_tm_sha256':hashlib.sha256((HERE/'upstream/data/pa196.tm').read_bytes()).hexdigest(),
 'source_program_sha256':hashlib.sha256((HERE/'upstream/PA196/Program.lean').read_bytes()).hexdigest(),
 'executed_tm_text_sha256':'1ffb73d174b7040a9b50d1fe871ebcfe3bc9d3054a6b11ac6d5732bac6c446a2',
 'executed_tm_text_note':'Run input contained one additional final newline; parsed transitions equal canonical input exactly.',
 'source_sites':3812,'unguarded_cases':4959,'guarded_cases':4956,'transition_row_cover_prefix':59,
 'zero_positive_site_mask_pairs':274880,'fixture_files':{},
 'budget':'max(800, 2 * parent_steps + 64)','tape_cells':256,'initial_head_index':32,
 'exact_keeper_row':study(exact_names,'unguarded','full tape, head, root control'),
 'guarded_keeper_row':study(['macro_guarded_log.txt'],'mask representative','full tape, head, root control'),
 'relaxed_keeper_row':study(['macro_loose_log.txt'],'mask representative','same primary values and address; gap>=48; any nonempty valid spares'),
 'arbitrary_helper_prefix':study(['macro_helpers_log.txt'],'unguarded','full tape, head, root control'),
 'controls':json.loads((HERE/'macro_controls.json').read_text()),
 'limitations':['Finite representative register values only.','Failure may be unexpected halt, window exit, or budget exhaustion.','No global state-count lower bound.','No new PA consistency biconditional.']}
for name in ['macro_tests.txt','macro_guarded_tests.txt']:
    receipt['fixture_files'][name]=hashlib.sha256((HERE/name).read_bytes()).hexdigest()
receipt['exact_keeper_row']['all_196_deletions_completed']=receipt['exact_keeper_row']['completed_deleted_states']==list(range(196))
(HERE/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:{p:v[p] for p in ('deleted_state_count','assignments','survivors')} for k,v in receipt.items() if isinstance(v,dict) and 'assignments' in v},indent=2))
