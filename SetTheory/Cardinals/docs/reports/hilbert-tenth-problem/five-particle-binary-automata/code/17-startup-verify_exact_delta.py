#!/usr/bin/env python3
"""Exact serialized and semantic delta, including propagated private renaming."""
from collections import Counter
import hashlib
import json
from pathlib import Path
from baseline_support import regenerated_baseline
from verify_pins import verify_inputs
ROOT = Path(__file__).resolve().parent
verify_inputs()
def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)
def read(root, name):
    return json.loads((root / name).read_text())
def checksum(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
layers = {}
with regenerated_baseline() as baseline:
    for name in ('primitive3.json','normalized3.json','reversible5.json','reversible2-primitives.json','source.json'):
        old, new = read(baseline, name), read(ROOT, name)
        field = 'branches' if 'branches' in old else 'rows'
        a, b = {row['name']:row for row in old[field]}, {row['name']:row for row in new[field]}
        common = set(a) & set(b)
        row_fields = sorted(set().union(*(set(row) for row in a.values())))
        changed = sorted(n for n in common if a[n] != b[n])
        rec = dict(old_sha256=checksum(baseline/name), new_sha256=checksum(ROOT/name),
                   old_controls=len(old['controls']), new_controls=len(new['controls']),
                   old_rows=len(a), new_rows=len(b),
                   ordered_controls_identical=old['controls']==new['controls'],
                   control_names_removed=len(set(old['controls'])-set(new['controls'])),
                   control_names_added=len(set(new['controls'])-set(old['controls'])),
                   row_names_removed=len(set(a)-set(b)), row_names_added=len(set(b)-set(a)),
                   shared_row_names_changed=len(changed), shared_row_names_unchanged=len(common)-len(changed),
                   changed_row_fields={key:sum(a[n].get(key)!=b[n].get(key) for n in common) for key in row_fields},
                   positional_row_entries_changed=sum(x!=y for x,y in zip(old[field],new[field])))
        require(rec['old_controls']==rec['new_controls'] and rec['old_rows']==rec['new_rows'], 'Dimensions changed')
        if name in ('primitive3.json','normalized3.json'):
            require((baseline/name).read_bytes()==(ROOT/name).read_bytes(), 'Data layer changed')
        if name=='reversible5.json':
            require(rec['ordered_controls_identical'] and not rec['row_names_removed'] and not rec['row_names_added'] and len(changed)==8, 'Unexpected five-counter delta')
            rec['changed_rows']=[dict(name=n,old=a[n],new=b[n]) for n in changed]
        layers[name] = rec
    oldc,newc = read(baseline,'certificates.json'),read(ROOT,'certificates.json')
    oldh,newh = {h['target']:h for h in oldc['history']},{h['target']:h for h in newc['history']}
    require(oldh.keys()==newh.keys() and len(newh)==233, 'Collision universe changed')
    changes=[]
    for target in oldh:
        a,b=oldh[target],newh[target]
        require({k:v for k,v in a.items() if k!='incoming'}=={k:v for k,v in b.items() if k!='incoming'},'History private graph allocation changed')
        if a['incoming']!=b['incoming']:
            require(a['incoming']==list(reversed(b['incoming'])), 'Non-swap history change')
            changes.append(dict(target=target,old_bit0=a['incoming'][0],old_bit1=a['incoming'][1],new_bit0=b['incoming'][0],new_bit1=b['incoming'][1]))
    require({x['target'] for x in changes}=={'n0001_1','n0001_2','n0001_3','tm_A0_pop0'},'Wrong four targets')
    require(oldc['normalization']==newc['normalization'],'Normalization changed')
    # Derive the old and new empty prologue costs from actual five-counter rows.
    def prologue(root):
        table=read(root,'reversible5.json');graph={}
        for row in table['rows']:graph.setdefault(row['source'],[]).append(row)
        q='START';v=[0]*5;clock=0;steps=0;primes=(2,3,5,7,11)
        while q!='tm_A0_pop0':
            choices=[e for e in graph[q] if e['symbol'] not in 'ZP-' or (v[e['counter']]==0 if e['symbol']=='Z' else v[e['counter']]>0)]
            require(len(choices)==1,'Prologue nondeterminism')
            e=choices[0];A=1
            for p,c in zip(primes,v):A*=p**c
            p=primes[e['counter']];symbol=e['symbol']
            clock+=1 if symbol=='0' else (p+7)*A+3 if symbol=='+' else 4*A+(p+3)*(A//p)+3 if symbol=='-' else 4*A+4*(A//p)+3
            v[e['counter']]+={'+':1,'-':-1}.get(symbol,0);q=e['target'];steps+=1
            require(steps<=142,'Prologue budget')
        return dict(five_counter_steps=steps,final_five_counters=v,predicted_literal_steps=clock)
    clocks={'old':prologue(baseline),'new':prologue(ROOT)}
    require(clocks['old']['predicted_literal_steps']==79936151060302 and clocks['new']['predicted_literal_steps']==138,'Wrong empty prologue comparison')
receipt=dict(status='PASS',scope='Exact pinned old/new generated-table delta; old tables regenerated, never read from another release. Expanded private naming may differ; equal dimensions do not imply identical machine or CA rule.',collision_pairs=233,changed_pairs=changes,unchanged_collision_pairs=229,policy_selected_targets=6,other_unselected_collision_pairs=227,layers=layers,empty_prologues=clocks,clock_scope='Old 79,936,151,060,302 clock derived from the fully executed 142-row five-counter prologue and exact prime cost formulas; its enormous two-counter expansion was not traversed. New 138-row literal execution is separately verified.')
(ROOT/'exact-delta-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
