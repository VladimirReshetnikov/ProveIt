#!/usr/bin/env python3
"""No-Lean positive and negative controls for exact declaration axiom sets."""
import importlib.util
from pathlib import Path
p=Path(__file__).resolve().parent/'replay.py';s=importlib.util.spec_from_file_location('replay',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
module='DiophantineConsistency.CompactHighResidue'
a=('CompactHighResidue.natural_mod_eight','propext')
b=('CompactHighResidue.model_mod_eight','propext, Classical.choice, Quot.sound')
m.validate_reports(module,[a,b])
cases={
 'missing-declaration':[a],
 'extra-declaration':[a,b,('extra','propext')],
 'duplicate-declaration':[a,b,b],
 'missing-axiom':[a,(b[0],'propext, Quot.sound')],
 'extra-axiom':[a,(b[0],'propext, Classical.choice, Quot.sound, bogus')],
 'changed-axiom':[('CompactHighResidue.natural_mod_eight','Classical.choice'),b],
 'empty-axioms':[a,(b[0],'')],
 'unexpected-natural-axiom':[('CompactHighResidue.natural_mod_eight','propext, Classical.choice'),b]}
for label,rows in cases.items():
 try:m.validate_reports(module,rows)
 except ValueError:continue
 raise RuntimeError('failed to reject '+label)
print('PASS exact axiom sets and 8 negative controls; no Lean launched')
