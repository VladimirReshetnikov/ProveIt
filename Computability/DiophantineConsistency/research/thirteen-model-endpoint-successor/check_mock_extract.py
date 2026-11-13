#!/usr/bin/env python3
"""Check the provisional mock contains exactly the anchored endpoint front."""
import hashlib
import os
from pathlib import Path
import subprocess
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('reject optimized Python')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
SOURCE=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ModelThirteenCarrier.lean'
MOCK=HERE/'MockModelThirteenCarrier.lean'
anchor='ca2b5071e3c647e4bf3039ac52e4308a179dcfa6'
rel=SOURCE.relative_to(ROOT).as_posix()
p=subprocess.run(['git','show',f'{anchor}:{rel}'],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
raw=SOURCE.read_bytes()
if raw!=p.stdout:raise ValueError('current endpoint source differs from anchored blob')
s=raw.decode();a=s.index('/-- The common thirteen-coordinate front');b=s.index('/-! ### The completion map',a);block=s[a:b]
head='import DiophantineConsistency.Thirteen69Nodes\nset_option autoImplicit false\nset_option Elab.async false\nnoncomputable section\nnamespace DiophantineConsistency.ModelThirteenCarrier\nopen AdaptiveEquationSyntax2011\n'
expected=head+block+'\nend DiophantineConsistency.ModelThirteenCarrier\n'
if MOCK.read_text()!=expected:raise ValueError('mock is not the exact extracted source plus wrapper')
print('PASS_PROVISIONAL_MOCK_EXTRACT',len(block.encode()),hashlib.sha256(block.encode()).hexdigest())
