#!/usr/bin/env python3
"""Rebuild any released graph polynomial with exact integer arithmetic."""
import argparse
import hashlib
import json
from pathlib import Path
from paired_graph import compile_paired
from quotient_aliases import quotient, dump
from quartic_equalities import compress_pairs

ROOT=Path(__file__).resolve().parent

def build(profile):
    raw=(ROOT/profile['source']).read_bytes()
    p,c=compile_paired(json.loads(raw),profile['hubs'])
    p,c=quotient(p,c,seed=profile['seed'],strategy=profile['strategy'],rounds=profile['rounds'])
    p,c=compress_pairs(p,c)
    c['source_sha256']=hashlib.sha256(raw).hexdigest()
    return p,c

def main():
    pa=argparse.ArgumentParser(description=__doc__)
    pa.add_argument('--profile',required=True)
    pa.add_argument('--output',required=True,type=Path)
    a=pa.parse_args()
    profiles=json.loads((ROOT/'profiles.json').read_text())
    matches=[p for p in profiles if p['name']==a.profile]
    if len(matches)!=1:raise ValueError('Unknown profile')
    p,c=build(matches[0]);dump(a.output/'polynomial.json',p);dump(a.output/'certificate.json',c);dump(a.output/'metrics.json',p['metrics'])
    print(json.dumps(p['metrics'],sort_keys=True))

if __name__=='__main__':main()
