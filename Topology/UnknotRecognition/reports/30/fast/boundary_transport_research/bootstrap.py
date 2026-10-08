"""Locate the packaged/repository fast tree without machine-specific paths."""

import importlib.util
import os
from pathlib import Path
import sys


def enable_fast():
    supplied = os.environ.get('PROVEIT_FAST_ROOT')
    if supplied:
        path = Path(supplied).expanduser().resolve()
        if not (path/'fastunknot'/'boundary_transport.py').is_file():
            raise SystemExit('PROVEIT_FAST_ROOT must name the fast directory containing '
                             'fastunknot/boundary_transport.py')
        sys.path.insert(0,str(path))
        return path
    if importlib.util.find_spec('fastunknot') is not None:
        return None
    for parent in Path(__file__).resolve().parents:
        for relative in ('fast','code/fast','Topology/UnknotRecognition/fast',
                         'ProveIt/Topology/UnknotRecognition/fast'):
            candidate = parent/relative
            if (candidate/'fastunknot'/'boundary_transport.py').is_file():
                sys.path.insert(0,str(candidate))
                return candidate
    raise SystemExit('Set PROVEIT_FAST_ROOT to the fast directory, or put it on PYTHONPATH.')
