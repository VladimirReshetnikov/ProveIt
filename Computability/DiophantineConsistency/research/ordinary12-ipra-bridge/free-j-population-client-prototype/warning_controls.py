#!/usr/bin/env python3
"""Check the single exact historical linter-warning allowlist."""
import importlib.util,os
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
p=Path(__file__).resolve().with_name('replay.py');spec=importlib.util.spec_from_file_location('r',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
name='DiophantineConsistency.ArithmeticBinomLegendre'
src=Path('/tmp/ipra-freej-population-client-pair-01/frozen/DiophantineConsistency/ArithmeticBinomLegendre.lean')
text=(Path(__file__).resolve().parent/'observations/failed-pair-01/DiophantineConsistency_ArithmeticBinomLegendre.log').read_text()
if not m.warnings_accepted(name,src,text):raise ValueError('observed warning unexpectedly rejected')
for other_name,other_text in ((name,text.replace(':78:10:',':78:11:')),(name,text+'extra warning: changed\n'),('DiophantineConsistency.ArithmeticPow',text),(name,'')):
 if m.warnings_accepted(other_name,src,other_text):raise ValueError(('unexpected acceptance',other_name,other_text))
if not m.warnings_accepted('DiophantineConsistency.ArithmeticPow',src,''):raise ValueError('warning-free other module rejected')
print('PASS_EXACT_WARNING_CONTROLS')
