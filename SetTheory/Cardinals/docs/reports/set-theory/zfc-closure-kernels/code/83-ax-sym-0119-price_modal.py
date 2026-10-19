#!/usr/bin/env python3
"""Replay a diagnostic inherited-entry price, not a binary-machine bound."""
from pathlib import Path
import json
from verify_candidates import Tree
HERE=Path(__file__).resolve().parent
old=Tree(json.loads((HERE/'data/original203.json').read_text()))
path=HERE/'focused_milp_results/dictionary_max24_freq2_zero7_depth64_old1.json'
new=Tree(json.loads(path.read_text()))
normalold={old.norm(('N',i)):i for i in old.nodes}
meta=json.loads((HERE/'data/decoder_entries.json').read_text())
entry={int(i):int(max(v,key=v.get)) for i,v in meta['state_entries'].items()}
matched={i:normalold[new.norm(('N',i))] for i in new.nodes if new.norm(('N',i)) in normalold}
novel=set(new.nodes)-set(matched);mapped={entry[i] for i in matched.values()}
result=dict(status='DIAGNOSTIC',source_nodes=len(new.nodes),matched_source_nodes=len(matched),distinct_inherited_modal_entries=len(mapped),novel_source_nodes=len(novel),static_modal_price=len(mapped)+len(novel),binary_state_bound=False,warning='Modal entries are observed inherited labels; reuse compatibility and further sharing are unproved. This number neither compiles the source nor bounds the states of any correct new binary machine.')
assert (len(new.nodes),len(matched),len(mapped),len(novel),len(mapped)+len(novel))==(201,177,168,24,192)
(HERE/'modal_price_verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
