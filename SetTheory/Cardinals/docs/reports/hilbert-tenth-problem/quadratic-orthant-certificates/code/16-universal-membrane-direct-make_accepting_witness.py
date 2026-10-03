#!/usr/bin/env python3
"""Create the full sparse natural witness for the accepting L=6,R=0,T=328 run."""
from pathlib import Path
import json,hashlib
from quadratic_core import semantic_table,witness_for_trace
R=Path(__file__).resolve().parent
program=json.loads((R/'virtual3.json').read_text());table=semantic_table(program)
w,last,regs,trace=witness_for_trace(table,328,[6,0,0])
assert last==table['halt'] and regs==(0,11,0)
actual=json.loads((R/'accepting_counter_trace.json').read_text())['trace']
assert [(table['labels'][z['source']],z['registers']) for z in trace]==[(z['control'],z['registers']) for z in actual]
out={'format':'sparse-natural-witness-v1','basis_revision':'strengthened-affine-branch-domain-v3','register_instructions':328,
     'parameters':{'L':6,'R':0},'variable_count':922008,'omitted_coordinates':'All omitted coordinates among 0..922007 are exactly zero.',
     'nonzero_coordinates':[[i,v] for i,v in sorted(w.items())],
     'program_sha256':hashlib.sha256((R/'virtual3.json').read_bytes()).hexdigest(),
     'schema_command':'python build_quadratic.py --steps 328'}
(R/'accepting_quadratic_witness.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'created','coordinate_slots':out['variable_count'],'nonzero_coordinates':len(w),'final_registers':regs},indent=2))
