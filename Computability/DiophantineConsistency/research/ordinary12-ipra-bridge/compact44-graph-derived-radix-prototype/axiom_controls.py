#!/usr/bin/env python3
"""No-Lean focused controls for the fixed-graph exact axiom reports."""
import importlib.util
from pathlib import Path
p=Path(__file__).resolve().parent/'replay.py';s=importlib.util.spec_from_file_location('replay',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
module='DiophantineConsistency.CompactGraphDerivedRadix'
ax='propext, Classical.choice, Quot.sound'
a=('CompactGraphDerivedRadix.graph_digits',ax)
b=('CompactGraphDerivedRadix.fixed_graph_digits',ax)
c=('extra.placeholder',ax)
m.validate_reports(module,[a,b])
cases={'missing-declaration':[a],'extra-declaration':[a,b,('extra',ax)],'duplicate-declaration':[a,b,b],
       'missing-axiom':[a,(b[0],'propext, Quot.sound')], 'extra-axiom':[a,(b[0],ax+', bogus')],
       'changed-axiom':[a,(b[0],'Classical.choice')], 'empty-axioms':[a,(b[0],'')]}
for label,rows in cases.items():
 try:m.validate_reports(module,rows)
 except ValueError:continue
 raise RuntimeError('failed to reject '+label)
print('PASS exact axiom sets and 7 negative controls; no Lean launched')
