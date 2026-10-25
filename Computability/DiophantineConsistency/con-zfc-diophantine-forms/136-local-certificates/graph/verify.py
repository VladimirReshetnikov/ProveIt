#!/usr/bin/env python3
"""Verify all final graph polynomials, optionally rebuilding every coefficient.

The default path imports only two independently written verifiers.  Builders
are imported only with --rebuild, after the independent checks have passed.
"""
import argparse
import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

def canonical(value):
    return (json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()

def need(condition,message):
    if not condition: raise ValueError(message)

def check_readable(path,polynomial):
    parsed=[]
    for line in path.read_text().splitlines():
        if not line.startswith(('+ ','- ')):continue
        c=1 if line[0]=='+' else -1;body=line[2:];mon=[]
        if body!='1':
            for factor in body.split('*'):
                match=re.fullmatch(r'z(\d+)(?:\^([1-4]))?',factor)
                need(match is not None,'Malformed readable monomial')
                mon.extend([int(match.group(1))]*int(match.group(2) or 1))
        parsed.append([c,mon])
    need(parsed==polynomial['terms'],'Readable polynomial transcription mismatch')

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--rebuild',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    inherited=load_module('independent_original_verifier',HERE/'inherited/verify_graph.py')
    local=load_module('independent_local_verifier',HERE/'verify_local.py')
    profiles=json.loads((HERE/'PROFILES.json').read_text());records=[]
    for profile in profiles:
        directory=HERE/profile['name']
        parent_directory=HERE/'parents'/profile['name']
        raw=(HERE/profile['source']).read_bytes();digest=hashlib.sha256(raw).hexdigest()
        need(digest==profile['source_sha256'],'Source digest: '+profile['name'])
        source=json.loads(raw)
        parent=json.loads((parent_directory/'polynomial.json').read_text())
        old=json.loads((parent_directory/'certificate.json').read_text())
        new=json.loads((directory/'polynomial.json').read_text())
        cert=json.loads((directory/'certificate.json').read_text())
        inherited.verify(source,parent,old,digest)
        metrics=local.check(parent,old,new,cert)
        check_readable(directory/'polynomial.txt',new)
        need(json.loads((parent_directory/'metrics.json').read_text())==parent['metrics'],'Parent metric file')
        need(json.loads((directory/'metrics.json').read_text())==metrics,'Final metric file')
        record={'profile':profile['name'],'source_sha256':digest,'metrics':metrics,
            'polynomial_sha256':hashlib.sha256((directory/'polynomial.json').read_bytes()).hexdigest()}
        if args.rebuild:
            builder=load_module('inherited_builder',HERE/'inherited/build.py')
            compressor=load_module('inherited_compressor',HERE/'inherited/compress_aliases.py')
            optimizer=load_module('local_optimizer',HERE/'optimize_aliases.py')
            pa,pc=builder.compile_graph(source,profile['hubs'],True)
            pc['source_sha256']=digest
            pa,pc,_=compressor.compress(pa,pc)
            state,_=optimizer.optimize(pc,pa,profile['seed'])
            na,nc=optimizer.emit(state,pc,pa,profile['quartic_guards'])
            rebuilt={'parent/polynomial.json':pa,'parent/certificate.json':pc,
                     'parent/metrics.json':pa['metrics'],'final/polynomial.json':na,
                     'final/certificate.json':nc,'final/metrics.json':na['metrics']}
            for path,obj in rebuilt.items():
                target=(parent_directory if path.startswith('parent/') else directory)/path.split('/',1)[1]
                need(canonical(obj)==target.read_bytes(),'Byte reconstruction mismatch: '+profile['name']+'/'+path)
            record['byte_identical_rebuild_files']=list(rebuilt)
        records.append(record)
    result={'status':'pass','profiles':records,
      'scope':'Exact finite algebra and zero-set correspondence certificates. The mathematical proof and inherited C222/ZF/ZFC calibration are specified in the article.'}
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output: args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
