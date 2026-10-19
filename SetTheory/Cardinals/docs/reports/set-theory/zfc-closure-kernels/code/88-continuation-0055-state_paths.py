"""Separate immutable packaged state inputs from fresh verification outputs."""
from pathlib import Path
import os,tempfile

ROOT=Path(__file__).resolve().parents[2]

def output_directory(requested=None):
    value=requested if requested is not None else os.environ.get('ZFC_STATE_OUTPUT')
    if value is None:
        parent=ROOT/'verification';parent.mkdir(parents=True,exist_ok=True)
        target=Path(tempfile.mkdtemp(prefix='state-',dir=parent))
    else:
        target=Path(value).expanduser().resolve()
        protected=[ROOT/name for name in ('experiments','vendor','code','proof','machines','results')]
        if target==ROOT or any(target==p or p in target.parents for p in protected):
            raise ValueError('State verification outputs must not overwrite packaged inputs, certificates, code, or proofs')
        target.mkdir(parents=True,exist_ok=True)
    return target
