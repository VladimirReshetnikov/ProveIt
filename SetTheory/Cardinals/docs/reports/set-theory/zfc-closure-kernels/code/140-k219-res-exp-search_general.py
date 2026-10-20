"""Portable dependency shim for the archived nonlocal reassociation driver."""
from pathlib import Path
import os
import additive_binder as z
s,b,BASE,WORK=z.s,z.b,z.BASE,z.ROOT
PARENT=Path(os.environ['K221_BASE']).resolve()
