"""Relocatable, pinned paths for the selected source experiment generators."""
import os,sys,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BASELINE=Path(os.environ.get('FORMALISM_BASELINE',ROOT/'baseline'))
OUTPUT=Path(os.environ.get('FORMALISM_OUTPUT',ROOT/'generated'))
PORTABLE=Path(os.environ.get('FORMALISM_PORTABLE',ROOT.parent/'vendor'/'K221'/'portable'))
PINS={'sites218.json': 'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9', 'k218.native.tm': '2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f', 'decoder_allocation.json': '81d5dcb786c0a31e176dae1d4dcfeb4ee8fa5ce2f3c8dbdd36175c9ba2e0c43c'}
for name,digest in PINS.items():
    if hashlib.sha256((BASELINE/name).read_bytes()).hexdigest()!=digest:raise ValueError('Baseline hash mismatch: '+name)
VENDOR_PINS={'source_language.py':'4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f','build221.py':'3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba'}
for name,digest in VENDOR_PINS.items():
    if not (PORTABLE/name).is_file():raise FileNotFoundError('Set FORMALISM_PORTABLE to the central K221/portable directory: '+str(PORTABLE/name))
    if hashlib.sha256((PORTABLE/name).read_bytes()).hexdigest()!=digest:raise ValueError('Vendor hash mismatch: '+name)
OUTPUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(PORTABLE))
