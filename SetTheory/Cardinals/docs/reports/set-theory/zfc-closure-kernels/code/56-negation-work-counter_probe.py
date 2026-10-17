#!/usr/bin/env python3
"""Which exact source contracts obstruct a shorter zero-run dispatcher?"""
from pathlib import Path
import importlib.util
import json
import sys
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
REPO = HERE.parent/'source/ProveIt'
BASE = REPO/'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
import candidate252_independent_audit as audit
import permutation252_phase_analysis as phase
strictpath = REPO/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
sys.modules['cost_search'] = SimpleNamespace()
spec=importlib.util.spec_from_file_location('counter_strict',strictpath)
strict=importlib.util.module_from_spec(spec)
spec.loader.exec_module(strict)
raw=(BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in audit.read_table(raw).items()}
prog=(REPO/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_bytes()
sites,cases,targets,first=phase.program_graph(prog)
def check(tab,case):
    site,path,op,r,zero=case
    physical=audit.NEWPHYS[r] if op in ('CI','CD') else r
    guard=(physical,zero) if op=='CD' else None
    pc=audit.successor(path,op,r,zero)
    eff=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
    right=[('b',int(b)) for b in pc or '']
    right += [('r',0,1,(41 if pc is None else 40)-len(pc or '')),('b',1),('box',('plain',eff))]
    try:
        strict.run(tab,path,guard,strict.canon([('b',1)],right),halt=op=='CH',fuel=1500)
        return None
    except (AssertionError,KeyError) as exc:
        return str(exc)

results=[]
for direction in ['L','R']:
    mutant={k:v for k,v in table.items() if k[0]!='74'}
    mutant['58',0]=(0,direction,'84')
    mutant['58',1]=table['58',1]
    assert all(mutant[str(q),b]==table[str(q),b] for q,b in audit.BOX_PAIRS)
    failures=[]
    for i,c in enumerate(cases):
        err=check(mutant,c)
        if err:
            failures.append({'index':i,'case':c,'reason':err})
    results.append({'deleted':74,'incoming_action':[0,direction,84],
                    'failures':failures,'pass_count':len(cases)-len(failures)})
    print(direction,'passed',len(cases)-len(failures),'failures',len(failures),flush=True)
(HERE/'counter-probe.json').write_text(json.dumps(results,indent=2)+'\n')
