from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent
runs=[]
for name,seconds,seed in [('run147',300,147),('runB148',240,148)]:
 text=(ROOT/(name+'.log')).read_text()
 done=re.search(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([\d.]+)',text)
 cycles=re.findall(r'CYCLE \d+ best (\d+) now \d+ pool \d+ iterations (\d+) nodes \d+ seconds ([\d.]+)',text)
 if done:
  iterations,accepted,hits,best,elapsed=done.groups()
  r=dict(name=name,requested_seconds=seconds,seed=seed,status='completed',proposals=int(iterations),accepted_moves=int(accepted),saved_hits_below194=int(hits),best_penalized_effective_score=int(best),elapsed_seconds=float(elapsed))
 else:
  best,iterations,elapsed=cycles[-1]
  r=dict(name=name,requested_seconds=seconds,seed=seed,status='resource_killed_exit137'if name=='run147'else'in_progress',completed_flushed_proposals_at_least=int(iterations),last_flushed_best_penalized_effective_score=int(best),last_flushed_elapsed_seconds=float(elapsed))
 runs.append(r)
paths=['setup.py','search.cpp','screen.cpp','templates.txt','templates_B.txt','leaf_attrs.txt','inputs/AX11H.nodes.json','inputs/AX11H.grammar.json','inputs/primary.raw.native.tm','inputs/h_shift_edits.json','run147.log','runB148.log']
r=dict(commit='883da8d55452ea097910ed2509a1eefc833ce292',fixed_working_controls=134,original_macro_word_length=190,expanded_macro_word_length=193,expanded_operand_occurrences=1,source_graph_identity_at_initial_expanded_seed=True,deterministic_setup_replayed=True,new_fixed_atoms={'node32':104,'node53':107},new_fixed_subtree_aliases=[{'children':[107,98],'control':185},{'children':[104,185],'control':92},{'children':[92,90],'control':213}],runs=runs,found_accepted_sub194=False,scope='Randomized bounded discovery only. Source graph and physical acceptance would be checked for any hit. No strict hit was emitted; no lower bound follows. Original run only its logged prefix is certified as examined.',sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest()for p in paths})
(ROOT/'search_receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r['runs'],indent=2))
