#!/usr/bin/env python3
"""Byte-exact seed reconstruction, independent of the independent verifier."""
from pathlib import Path
import json
import hashlib
from build_pool import build, analyze
from build_joint import make_joint

ROOT=Path(__file__).resolve().parents[1]
def encoded(obj):
    return (json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()
def main():
    expected={}
    def add(name,doc,cert,degree=None):
        expected[name+'.json']=doc
        expected[name+'_certificate.json']=cert
        metrics=analyze(doc)
        if degree is not None:metrics['degree']=degree
        expected[name+'_metrics.json']=metrics
    doc,cert,rows=build()
    add('P207',doc,cert,24)
    expected['P207_quadratic_rows.json']=rows
    fused,fusedcert=make_joint(doc)
    add('P206_joint',fused,fusedcert,26)
    for name,partition in [
        ('P208',[[0,1,2],[3,4]]),('P209',[[0],[1,2],[3,4]]),
        ('P210',[[0],[1],[2],[3,4]]),('P211',[[0],[1],[2],[3],[4]])]:
        doc,cert,_=build(partition)
        add('partitions/'+name,doc,cert)
        if name in ('P209','P211'):
            fused,fusedcert=make_joint(doc,0)
            add('partitions/'+('P208_joint' if name=='P209' else 'P210_joint'),
                fused,fusedcert)
    doc,cert,_=build([[0],[1],[2],[3,4]],unweighted_groups=[[3,4]])
    add('partitions/P210_consecutive',doc,cert)
    records=[]
    for name,obj in sorted(expected.items()):
        data=encoded(obj)
        if data!=(ROOT/'equations'/name).read_bytes():
            raise ValueError('Seed rebuild differs: '+name)
        records.append({'file':name,'sha256':hashlib.sha256(data).hexdigest()})
    print(json.dumps({'status':'PASS','byte_exact_files':len(records),'files':records}))
if __name__=='__main__':main()

