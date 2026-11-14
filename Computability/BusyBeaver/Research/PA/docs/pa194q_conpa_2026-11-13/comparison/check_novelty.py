#!/usr/bin/env python3
"""Compare a numeric TM action graph to the complete frozen inventory.
No semantic consistency claim follows from graph novelty.
"""
import argparse,json,pathlib
from build_inventory import parse,canon,sha
ap=argparse.ArgumentParser();ap.add_argument('candidate');ap.add_argument('--inventory',default=str(pathlib.Path(__file__).with_name('inventory.json')));ap.add_argument('--output');a=ap.parse_args()
b=pathlib.Path(a.candidate).read_bytes();p=parse(b)
if p is None:raise SystemExit('candidate does not meet numeric table recognition convention')
c=json.loads(pathlib.Path(a.inventory).read_text())
transforms=[(False,False),(True,False),(False,True),(True,True)]
hashes={f'reflection={r},complement={s}':canon(p,r,s)[0] for r,s in transforms}
if any(h is None for h in hashes.values()):raise SystemExit('graph has no root reaching all working states; root-free BFS comparison unavailable')
matches=[{'sha256':r['sha256'],'first_path':r['first_path'],'transform_matches':[k for k,v in hashes.items() if v==r['action_graph_sha256']]} for r in c['raw_tables'] if r['states']==len(p[1]) and r['action_graph_sha256'] in hashes.values()]
result={'candidate':a.candidate,'candidate_sha256':sha(b),'working_states':len(p[1]),'candidate_hashes':hashes,'corpus_commit':c['summary']['commit'],'corpus_raw_tables':c['summary']['raw_tables'],'cosmetic_graph_matches':matches,'graph_novel_under_state_renaming_start_choice_reflection_and_symbol_complement':not matches,'scope':'Finite action-graph comparison only; does not establish valid source simulation, blank-run behavior or consistency equivalence.'}
s=json.dumps(result,indent=2)+'\n'
if a.output:pathlib.Path(a.output).write_text(s)
print(s)
