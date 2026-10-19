"""Independent table-data audit, written for the 2026-10-18 review.

No downloaded Python module is imported or executed. Transition files and
JSON certificate files are read as inert data only. The sparse and dense
interpreters below implement the mathematical five-field transition format.
"""
if not __debug__:
    raise RuntimeError('Assertions are required; do not use python -O or PYTHONOPTIMIZE')

from pathlib import Path
import json, hashlib, os
PACKAGE = Path(__file__).resolve().parent.parent
ROOT = Path(os.environ.get('B245_OUTPUT', PACKAGE / 'results'))
ROOT.mkdir(parents=True, exist_ok=True)
SOURCES = Path(os.environ.get('B245_INPUTS', PACKAGE / 'inputs'))

def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q,b,w,d,t=line.split()
        key=(int(q),int(b))
        assert key not in rows
        assert int(b) in (0,1) and int(w) in (0,1) and d in ('L','R')
        rows[key]=(int(w),d,int(t))
    return rows

def sparse(table, count):
    state=position=0; ones=set(); seen=set(); used=set()
    for tick in range(count):
        bit=int(position in ones); seen.add(state); used.add((state,bit))
        write,direction,state=table[state,bit]
        if write: ones.add(position)
        else: ones.discard(position)
        position += 1 if direction=='R' else -1
    return state,position,sorted(ones),seen,used

def dense(table,count):
    # Every head position lies within [-count,count].
    tape=bytearray(2*count+1); origin=count; index=origin; state=0
    for tick in range(count):
        write,move,target=table[state,tape[index]]
        tape[index]=write
        index += {'L':-1,'R':1}[move]
        state=target
    return state,index-origin,[i-origin for i,b in enumerate(tape) if b]

results={}
tables={}
boots={}
for label,n,steps in [('routing245',245,407915),('prefix246',246,410735)]:
    folder=SOURCES / ('candidate-'+label)
    path=folder/('zfc_'+label+'.tm')
    oldpath=folder/('zfc_'+label+'_old.tm')
    table=read_table(path); old=read_table(oldpath); tables[label]=old
    states={s for s,b in table}
    assert states==set(range(n)) and len(table)==2*n
    assert set(table)=={(s,b) for s in states for b in (0,1)}
    assert {t for w,d,t in table.values()}-states=={n}
    halted_by=[list(key)+list(row) for key,row in table.items() if row[2]==n]
    assert len(halted_by)==1
    mapping={int(k):v for k,v in json.loads((folder/'renumbering.json').read_text())['old_to_canonical'].items()}
    assert len(set(mapping.values()))==n+1
    assert {(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in old.items()}==table
    s,h,ones,seen,used=sparse(table,steps)
    assert (s,h,ones)==dense(table,steps)
    assert (s,h)==(88,-5)
    boots[label]=ones
    cert=json.loads((SOURCES/'certificate__blank_boot.json').read_text())
    assert ones==cert['all_one_positions']
    results[label]={
      'working_states':n,'transition_rows':len(table),'start':0,'halt':n,
      'two_way_binary_tape':True,'every_move_left_or_right':True,
      'initialization_states_included':True,'renumbering_matches':True,
      'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
      'old_labels_sha256':hashlib.sha256(oldpath.read_bytes()).hexdigest(),
      'unique_halt_action':halted_by[0],
      'blank_steps':steps,'final_state':s,'head':h,'one_cells':len(ones),
      'whole_tape_matches_delivered_245_frame':True,
      'sparse_dense_agreement':True,'bootstrap_visited_states':len(seen),
      'bootstrap_used_transition_rows':len(used),
      'boot_one_positions':ones,
    }

a,b=tables['prefix246'],tables['routing245']
changed=[{'state_read':list(k),'prefix246':list(a[k]),'routing245':list(b[k])} for k in sorted(a.keys()&b.keys()) if a[k]!=b[k]]
removed=sorted(a.keys()-b.keys()); added=sorted(b.keys()-a.keys())
assert len(changed)==104 and removed==[(247,0),(247,1)] and added==[]
results['comparison']={'changed_surviving_rows':len(changed),'removed_rows':removed,'added_rows':added,'changed_rows':changed,'identical_bootstrap_whole_tape':boots['routing245']==boots['prefix246'],'bootstrap_steps_saved':410735-407915}
(ROOT/'independent-table-boot-results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps({k:{a:b for a,b in v.items() if a not in ('boot_one_positions','changed_rows')} for k,v in results.items()},indent=2))
