import sys
if not sys.flags.isolated:
    sys.stderr.write("REJECTED: isolated Python (-I) is required\n")
    raise SystemExit(2)
sys.dont_write_bytecode = True

#!/usr/bin/env python3
"""Replay Report137's finite exact algebra using only Python's standard library."""
import sys
sys.dont_write_bytecode=True
import json
from pathlib import Path

# This executable accepts no output path; JSON goes to stdout only. The release
# verifier loads the same verified source bytes and owns all output guards.
if __name__=='__main__':
    sys.path.insert(0,str(Path(__file__).absolute().parent))
import gaussian
import models
import regularized
import inverse


def run():
    return {'schema':'report137-replay-v1',
            'gaussian':gaussian.checks(),'singular_models_and_constants':models.checks(),
            'synthetic_regularization':regularized.checks(),'inverse':inverse.checks()}

if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True,indent=2,ensure_ascii=True))
