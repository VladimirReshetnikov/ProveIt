"""Pinned K221 input discovery for the supplemental encoding experiments."""
from pathlib import Path
import os,sys,hashlib,json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
BASE=Path(os.environ.get('K221_BASE',ROOT/'inputs'/'K221_Construction_2026-10-20')).resolve()
OUT=Path(os.environ.get('ENCODING_OUTPUT',ROOT/'generated')).resolve()
OUT.mkdir(parents=True,exist_ok=True)
P=BASE/'portable'
TABLE=BASE/'machine'/'k221.native.tm'
SITES=BASE/'machine'/'sites221.json'
EXPECTED_TABLE='e6dc479f09ded05dd1c0639b60a0c453483f42e6b77c29562d433cac528c1ecc'
EXPECTED_SITES='691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9'
for path,want in [(TABLE,EXPECTED_TABLE),(SITES,EXPECTED_SITES)]:
    if not path.is_file():raise FileNotFoundError(f'Set K221_BASE to the extracted K221 packet; missing {path}')
    got=hashlib.sha256(path.read_bytes()).hexdigest()
    if got!=want:raise ValueError(f'Pinned input hash mismatch: {path}: {got}')
sys.path.insert(0,str(P))
import source_language as s
import build221 as b
T=b.read_table(TABLE.read_bytes())
ROWS=json.loads(SITES.read_text())
TREE=s.tree(ROWS)
GROUPS,_=b.decoder_map(T,TREE)
ENGINE=set(q for q,bit in T)-set(GROUPS)
assert len(ENGINE)==49 and len(GROUPS)==172
