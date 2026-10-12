"""Load the research overlay without modifying a repository checkout."""
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = Path(os.environ.get('PROVEIT_UNKNOT_ROOT',
    HERE/'runtime' if (HERE/'runtime/fast').is_dir()
    else HERE.parent/'ProveIt/Topology/UnknotRecognition'))
INCOMING = Path(os.environ.get('CANCELLATION_PACKAGE',
    HERE.parent/'incoming_review/unknot_cancellation_20261012/unknot_cancellation_20261012'))
sys.path.insert(0, str(REPO/'fast'))
import fastunknot
fastunknot.__path__.insert(0, str(HERE/'fastunknot'))
fastunknot.__path__.append(str(INCOMING/'repro/Topology/UnknotRecognition/fast/fastunknot'))
import normal_orbit_research
normal_orbit_research.__path__.append(
    str(INCOMING/'repro/Topology/UnknotRecognition/fast/normal_orbit_research'))
