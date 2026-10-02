#!/usr/bin/env python3
from pathlib import Path
import json
import os
ROOT = Path(__file__).resolve().parent.parent
OUT = Path(os.environ.get('A202058_REPLAY_OUT', ROOT/'build/replay'))
for name in ['a_seq.json','a_seq_m.json','concavity_violations.json','m_concavity_violations.json']:
    assert json.loads((ROOT/'results'/name).read_text()) == json.loads((OUT/name).read_text()), name
print('Both regenerated root sequences and violation lists match frozen results')
