#!/usr/bin/env python3
"""Exactly regenerate the selected omit-zero source; no vendor import."""
from pathlib import Path
import argparse,hashlib,json
from source_format import read_tree,subtree,replace,write_sites,compact,metrics
BASE='b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9'
WANT='86ca1b05c5bfada9d77ece84b88a165a7d61fe3dd8623273d94d1e81f87ac8e3'
p=argparse.ArgumentParser();p.add_argument('--baseline',type=Path,default=Path(__file__).resolve().parents[1]/'baseline/sites218.json');p.add_argument('--output',type=Path,required=True);a=p.parse_args()
raw=a.baseline.read_bytes();assert hashlib.sha256(raw).hexdigest()==BASE
old=read_tree(json.loads(raw));new=replace(old,'11111',subtree(old,'111111'));data=compact(write_sites(new));assert hashlib.sha256(data).hexdigest()==WANT
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(data)
print(json.dumps({'status':'EXACT_SOURCE_REGENERATED','sha256':WANT,'metrics':metrics(new)},indent=2))
