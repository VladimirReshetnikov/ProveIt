"""Use the new overlay with byte-verified pinned production dependencies."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'reference'))
import fastunknot
fastunknot.__path__.insert(0, str(ROOT / 'overlay/fast/fastunknot'))
