#!/usr/bin/env python3
"""Cost/control emission only: no blank-tape logical calibration assertion."""
from pathlib import Path
import sys,json,argparse,hashlib
H=Path(__file__).resolve().parent;R=H.parent/'context_folds/recovered/67/research';sys.path[:0]=[str(R/'agent_logic'),str(H.parent/'source/Computability/BusyBeaver/Research/ZFC'),str(H/'mp_first_corrected/backend')]
from verify_reassociation import Decoder,read_json
import full_grammar_experiment as common
import TMBuilder as b
C=common.load_file('emit_helper',common.REPORT/'code/08-schema-machine-rebracket_axioms.py')
ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(exist_ok=True)
n,r,digest=read_json(a.source);d=Decoder(n,r);n={q:n[q]for q in d.reached};order=[r]+sorted(set(n)-{r});idx={q:i for i,q in enumerate(order)}
def edge(e):
 op=e[0];x=e[1]if len(e)>1 else None
 return {'N':lambda:f'ENode {idx[x]}','I':lambda:f'EInc {x}','D':lambda:f'EDecnz {x}','B':lambda:f'EBreak {x}','C':lambda:f'EContinue {x}','H':lambda:'EHalt'}[op]()
nn={idx[q]:tuple(map(edge,n[q]))for q in order};names={idx[q]:f'prefix_source_{q}'for q in order};names[0]='main().0'
m=C.compile_dag(b,nn,names);C.reextract(m,nn,names);data,labels,missing=common.normalize(m);(a.output/'candidate.tm').write_bytes(data);m.save(str(a.output/'candidate.named.tm'))
report=dict(source_sha256=digest,source_nodes=len(n),metrics=d.metrics(),leaf_sites=len(d.sites),binary_states=len(set(q for q,b in m.states)),sha256=hashlib.sha256(data).hexdigest(),all_edges_reextracted=True,missing_totalized=missing,blank_tape_logical_calibration_proved=False)
(a.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
