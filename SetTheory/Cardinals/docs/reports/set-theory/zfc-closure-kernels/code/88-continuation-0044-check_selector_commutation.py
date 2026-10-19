#!/usr/bin/env python3
"""Check finite premises of selector-permutation equivariance of a fixed-color emitter.

The theorem is in selector_commutation.tex. This checks its exact frozen
premises; it does not infer runtime correctness or a state lower bound.
"""
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from state_paths import output_directory
from collections import defaultdict
from hashlib import sha256
import json

ROOT=Path(__file__).resolve().parents[2]
OUT=output_directory()
INPUTS=ROOT/'experiments/state/inputs'
K={60,44,31,56,38,40,28,64,69}

def read_table(path):
    t={}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,s=line.split();t[int(q),int(b)]=int(w),d,int(s)
    assert len(t)==2*len({q for q,b in t})
    return t

def check(name,graph_path,roles_path,table_path,borrowed):
    graph=json.loads(graph_path.read_text())
    entries={int(s):tuple(e) for s,e in graph['entries'].items()}
    colors={int(s):int(q) for s,q in json.loads(roles_path.read_text())['roles'].items()}
    assert set(colors)=={s for s,e in entries.items() if e[0]=='N'}
    t=read_table(table_path);states={q for q,b in t}
    palette=set(colors.values());support=states-palette
    assert K<=support and K.isdisjoint(palette)
    changed={key for key,row in t.items() if key[0] not in K and row[2] in K}
    assert len(changed)==14
    assert all(q in support for q,b in changed)
    assert {t[k][2] for k in changed}==K
    assert changed.isdisjoint(borrowed)
    terminals=set()
    for s,q in colors.items():
        for b,child in enumerate(entries[s][1:]):
            if entries[child][0]!='N':terminals.add(t[q,b])
    assert all(row[2] not in K for row in terminals)
    assert 39 not in K
    groups=defaultdict(list)
    for s,q in colors.items():groups[q].append(s)
    shared={q for q,ss in groups.items() if len(ss)>1}
    protected=(shared|{q for q,b in borrowed}|{t[row][2] for row in borrowed}
               |{row[2] for (q,b),row in t.items() if q in support})
    assert K<=protected
    # Every support-row target changed by a selector permutation belongs to
    # K, and every member of K is already represented. Thus this target set,
    # and consequently the emitter's protected-color set, stays fixed.
    assert {t[k][2] for k in changed}==K
    return {'name':name,'source_nodes':len(colors),'source_colors':len(palette),
            'support_colors':len(support),'shared_colors':len(shared),
            'borrowed_rows':len(borrowed),'protected_colors':len(protected),
            'selector_states':sorted(K),'retargeted_rows':[list(k) for k in sorted(changed)],
            'retargeted_rows_are_support_only':True,
            'retargeted_rows_disjoint_from_borrowed':True,
            'terminal_targets_disjoint_from_selectors':True,
            'selector_targets_cover_all_nine_labels':True,
            'explicit_fallback_target_39_outside_selectors':True,
            'theorem_scope':'For every one of the 9! selector permutations and every candidate using this fixed source-color palette and inherited terminal recipes, emitted candidate rows outside support and all emitter acceptance/count tests are unchanged. Runtime validity and initialization are separate.',
            'sources':[{'path':str(p.relative_to(ROOT)),'sha256':sha256(p.read_bytes()).hexdigest()}
                       for p in (graph_path,roles_path,table_path)]}

def main():
    assert __debug__
    original_borrowed_path=INPUTS/'original_terminal_dependencies.json'
    rotated_borrowed_path=INPUTS/'rotated_rebase_evidence.json'
    original_borrowed={tuple(e['row']) for e in json.loads(original_borrowed_path.read_text())['rows']}
    rotated_borrowed={tuple(k) for k in json.loads(rotated_borrowed_path.read_text())['borrowed_rows']}
    data=[]
    for name,stem,borrowed in [('original203','s1_initial',original_borrowed),('rotated202','s2_initial',rotated_borrowed)]:
        data.append(check(name,INPUTS/f'{stem}.json',INPUTS/f'{stem}_roles.json',INPUTS/f'{stem}.tm',borrowed))
    report={'status':'PASS','proof_status':'Ordinary theorem with finite premise checks; not a proof-assistant certificate.',
            'cases':data,'does_not_certify_a_sub246_machine':True,
            'borrowed_row_inputs':[{'path':str(p.relative_to(ROOT)),'sha256':sha256(p.read_bytes()).hexdigest()}
                for p in (original_borrowed_path,rotated_borrowed_path)]}
    (OUT/'selector_commutation_certificate.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
