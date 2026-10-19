from pathlib import Path
import sys,json
H=Path(__file__).resolve().parent;R=H.parent/'context_folds/recovered/67/research';sys.path[:0]=[str(R/'agent_audit/layout_search'),str(R/'agent_logic')]
from verify_reassociation import read_json
import grammar_layout as g
g.original,g.original_root,_=read_json(H/'permuted_prefix_helpers.json')
import dictionary_milp as d
print('required lengths',sorted(map(len,d.required),reverse=True),'controlatoms',sum(x[0]=='A'for x in d.labels.values()))
