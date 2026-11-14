#!/usr/bin/env python3
"""Offline verification of the compact U208 comparison inputs and certificates.

Usage: python verify_comparison.py COMPARISON_DIRECTORY
"""
from hashlib import sha256
import json
from pathlib import Path
import sys
from canonical_compare import canonicalize, require
from compare_sources import graph

def main():
    directory=Path(sys.argv[1])
    certificate=json.loads((directory/'comparison.json').read_text())
    observed={}
    for entry in certificate['entries']:
        data=(directory/entry['input_file']).read_bytes()
        require(sha256(data).hexdigest()==entry['input_sha256'],'input byte mismatch')
        actual=canonicalize(data)
        for field in ('working_states','rows','start','halt'):
            require(actual[field]==entry[field],'wrong '+field)
        require(actual['state_to_canonical']=={int(k):v for k,v in entry['state_to_canonical'].items()},'state map differs')
        require(actual['canonical_encoding']==certificate['classes'][entry['class']],'full canonical encoding differs')
        observed[entry['class']]=observed.get(entry['class'],0)+1
    require(observed=={'A':5,'B':4},'wrong class multiplicities')
    require(certificate['classes']['A']!=certificate['classes']['B'],'classes equal')
    source_certificate=json.loads((directory/'source_comparison.json').read_text())
    source_rows=[]
    for i,entry in enumerate(source_certificate['entries']):
        data=(directory/f'class{i}.sites.json').read_bytes()
        require(sha256(data).hexdigest()==entry['sha256'],'source byte mismatch')
        source_rows.append(json.loads(data))
    cfgs=[graph(rows) for rows in source_rows]
    require(cfgs[0]==cfgs[1],'source CFG differs')
    require(sum(a[0]!=b[0] for a,b in zip(*source_rows))==720,'source path count differs')
    require(len(cfgs[0])==3909,'source count differs')
    print(json.dumps({'u208_classes':observed,'rows_per_table':416,'u208_source_sites':3909,
                      'full_action_encodings_checked':True,'source_cfgs_equal':True,
                      'source_paths_changed':720},indent=2))

if __name__=='__main__':main()
