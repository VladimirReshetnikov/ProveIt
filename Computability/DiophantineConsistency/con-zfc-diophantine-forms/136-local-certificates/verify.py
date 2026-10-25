#!/usr/bin/env python3
"""Read-only integrated verification of all released mathematical artifacts."""
from pathlib import Path
from collections import defaultdict
import argparse
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
import sys
import tempfile
from copy import deepcopy

ROOT = Path(__file__).resolve().parent

def require(value, message):
    if not value:
        raise ValueError(message)

def load(path):
    return json.loads((ROOT/path).read_text())

def sparse(terms):
    result=defaultdict(int)
    for c,m in terms:
        result[tuple(sorted(m))]+=c
    return {m:c for m,c in result.items() if c}

def check_printed_residuals():
    text=(ROOT/'direct_residuals.tex').read_text()
    bodies=re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}',text,re.S)
    rows=load('direct/integer306/equation.json')['residuals']
    require(len(bodies)==len(rows),'Printed residual count')
    for i,(body,row) in enumerate(zip(bodies,rows)):
        body=re.sub(r'\\\\(?:\[[^\]]*\])?','',body)
        body=re.sub(r'\s+','',body).replace('&','').replace('{}','')
        prefix='r_{'+str(i)+'}='
        require(body.startswith(prefix),'Printed residual index')
        expression=body[len(prefix):]
        recovered=[]
        for word in re.findall(r'[+-]?[^+-]+',expression):
            match=re.fullmatch(r'([+-]?)(\d*)((?:z_\{\d+\}(?:\^\{\d+\})?)*)',word)
            require(match is not None,'Unsupported printed monomial in row '+str(i)+': '+word)
            sign,num,variables=match.groups()
            require(bool(num or variables),'Empty printed term')
            coefficient=int(num or 1)*(-1 if sign=='-' else 1)
            indices=[]
            for index,power in re.findall(r'z_\{(\d+)\}(?:\^\{(\d+)\})?',variables):
                indices.extend([int(index)]*int(power or 1))
            recovered.append([coefficient,indices])
        require(sparse(recovered)==sparse(row['terms']),'Printed residual mismatch: '+str(i))
    return len(rows)

def run(relative, *extra):
    flags=['-B']+(['-O'] if sys.flags.optimize else [])
    p=subprocess.run([sys.executable,*flags,str(ROOT/relative),*extra],
                     cwd=ROOT,capture_output=True,text=True,check=False)
    if p.returncode:
        raise RuntimeError(relative+' failed:\n'+p.stderr[-4000:]+p.stdout[-4000:])
    return json.loads(p.stdout)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    value=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value

def graph_negative_controls():
    checker=module('independent_graph_quotient_checker','graph/verify_local.py')
    name='sparse1122'
    parent=load('graph/parents/'+name+'/polynomial.json')
    old=load('graph/parents/'+name+'/certificate.json')
    new=load('graph/'+name+'/polynomial.json')
    cert=load('graph/'+name+'/certificate.json')
    cases=[]
    changed=deepcopy(new); changed['terms'][0][0]*=-1
    cases.append(('changed constant',changed,cert))
    changed=deepcopy(cert); changed['equality_cycles']=changed['equality_cycles'][1:]
    cases.append(('omitted equality class',new,changed))
    changed=deepcopy(cert); changed['unit_path']=changed['unit_path'][:-1]
    cases.append(('omitted unit condition',new,changed))
    changed=deepcopy(cert)
    candidates=[i for i,t in enumerate(changed['parent_to_child'])
                if t is not None and new['variables'][t]['kind']=='alias']
    first=candidates[0]; target=changed['parent_to_child'][first]
    second=next(i for i in candidates if
        new['variables'][changed['parent_to_child'][i]]['normalized_variable'] !=
        new['variables'][target]['normalized_variable'])
    changed['parent_to_child'][first]=changed['parent_to_child'][second]
    cases.append(('cross-class alias identification',new,changed))
    rejected=[]
    for label,p,c in cases:
        try:
            checker.check(parent,old,p,c)
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise ValueError('Corruption accepted: '+label)
    return rejected

def integrity():
    path=ROOT/'MANIFEST.sha256'
    if not path.exists():
        return {'status':'not yet sealed','files':0}
    count=0
    for line in path.read_text().splitlines():
        if not line:
            continue
        expected,relative=line.split('  ',1)
        target=ROOT/relative
        require(target.is_file(),'Missing inventory file: '+relative)
        require(hashlib.sha256(target.read_bytes()).hexdigest()==expected,
                'Integrity mismatch: '+relative)
        count+=1
    return {'status':'pass','files':count}

def source_pins():
    records=load('provenance/ROOT_SOURCE_PINS.json')
    for entry in records:
        raw=(ROOT/entry['local']).read_bytes()
        blob=b'blob '+str(len(raw)).encode()+b'\0'+raw
        require(len(raw)==entry['size'] and
                hashlib.sha1(blob).hexdigest()==entry['git_blob_sha1'],
                'Pinned Git blob mismatch: '+entry['local'])
    pins=load('graph/SOURCE_PINS.json')
    for label,path,key in [
        ('source306','direct/parent/integer324-equation.json','parent_sha256'),
        ('source306','direct/integer306/equation.json','sha256'),
        ('source442','graph/sources/source442.json','sha256')]:
        require(hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==pins[label][key],
                'Graph source provenance mismatch: '+path)
    return {'status':'pass','exact_git_blobs':len(records),'graph_source_links':3}

def rebuild_direct():
    with tempfile.TemporaryDirectory(prefix='conzfc-direct-rebuild-') as temporary:
        target=Path(temporary)
        shutil.copy2(ROOT/'direct/build.py',target/'build.py')
        shutil.copytree(ROOT/'direct/parent',target/'parent')
        flags=['-B']+(['-O'] if sys.flags.optimize else [])
        result=subprocess.run([sys.executable,*flags,str(target/'build.py')],
                              cwd=target,capture_output=True,text=True,check=False)
        require(result.returncode==0,'Direct rebuild failed: '+result.stderr)
        expected=sorted(p.name for p in (ROOT/'direct/integer306').iterdir() if p.is_file())
        actual=sorted(p.name for p in (target/'integer306').iterdir() if p.is_file())
        require(actual==expected,'Direct rebuild file inventory')
        for name in expected:
            require((ROOT/'direct/integer306'/name).read_bytes()==
                    (target/'integer306'/name).read_bytes(),
                    'Direct rebuild byte mismatch: '+name)
        return {'status':'pass','byte_identical_files':expected}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild',action='store_true',help='Also reconstruct the direct equation and all selected graph JSON artifacts.')
    parser.add_argument('--output',type=Path,help='Write a receipt; after sealing choose a path outside the release.')
    args=parser.parse_args()
    inventory=integrity()
    pins=source_pins()
    direct=run('direct/verify.py')
    review=run('direct/review/review306.py')
    graphs=run('graph/verify.py',*(['--rebuild'] if args.rebuild else []))
    require((ROOT/'direct/integer306/equation.json').read_bytes()==
            (ROOT/'graph/sources/source306.json').read_bytes(),
            'Direct equation differs from graph source')
    printed=check_printed_residuals()
    for identity in load('EQUATION_IDENTITIES.json'):
        raw=(ROOT/identity['path']).read_bytes()
        require(len(raw)==identity['bytes'] and
                hashlib.sha256(raw).hexdigest()==identity['sha256'],
                'Normative equation identity mismatch')
    rejected=graph_negative_controls()
    direct_rebuild=rebuild_direct() if args.rebuild else {'status':'not requested'}
    result={'status':'pass','python_optimized':bool(sys.flags.optimize),
            'integrity':inventory,'source_pins':pins,'direct':direct,'direct_rebuild':direct_rebuild,'separate_direct_review':review,
            'graphs':graphs,'printed_residuals_checked':printed,
            'graph_source_matches_direct_equation':True,
            'graph_negative_controls_rejected':rejected,
            'scope':'Exact finite algebra, source bindings, zero-set certificates and displayed residuals. Unbounded proofs and inherited C222/ZF/ZFC calibration are stated separately.'}
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()
