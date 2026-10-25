#!/usr/bin/env python3
"""Offline exact checks for the entire delivered arithmetic construction.

The independent semantic, affine and contraction checkers import no producer.
Rebuilding is optional and is performed only in a fresh temporary directory.
"""
from pathlib import Path
from copy import deepcopy
from hashlib import sha256
import argparse,json,subprocess,sys,tempfile

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import check_affine_export as affine
import check_contraction as contraction
import audit_combined as semantic


def require(ok,message):
    if not ok:raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def canonical(value):
    return json.dumps(value,sort_keys=True,separators=(',',':')).encode()


def must_reject(label,action):
    try:action()
    except (ValueError,KeyError,IndexError):return label
    raise ValueError('negative control was accepted: '+label)


def readable(equation,label):
    lines=[f'{label}: P(z_0,...,z_{len(equation["variables"])-1}) = sum_(j=1)^{len(equation["residuals"])} R_j^2 = 0.',
           'Domain: all z_i are nonnegative integers.','']
    for i,row in enumerate(equation['residuals'],1):
        terms=[]
        for coefficient,monomial in row['terms']:
            factors=[]
            for k in sorted(set(monomial)):
                exponent=monomial.count(k)
                factors.append('z_'+str(k)+('^'+str(exponent) if exponent>1 else ''))
            magnitude=[] if abs(coefficient)==1 and factors else [str(abs(coefficient))]
            terms.append(('- ' if coefficient<0 else '+ ')+'*'.join(magnitude+factors))
        text=' '.join(terms)
        if text.startswith('+ '):text=text[2:]
        lines.append(f'R_{i:03d} = {text}')
    return '\n'.join(lines)+'\n'


def run(rebuild=False):
    ledger=read(HERE/'SOURCE_LEDGER.json')
    sourcepaths=set()
    for item in ledger['source_files']:
        name=item['path']
        require(name not in sourcepaths,'duplicate source-ledger path')
        sourcepaths.add(name)
        path=HERE/name
        require(path.is_file(),'missing retained source: '+name)
        require(sha256(path.read_bytes()).hexdigest()==item['sha256'],'retained source differs: '+name)
    parent=HERE/'source/shared_binomial/parent_raw_metadata.json'
    result={'status':'PASS','source_files_authenticated':len(sourcepaths),
        'ordinary_proof':'PROOF.md','new_object_language_proof_claimed':False,
        'variants':{},'negative_controls':[],'rebuilds':{}}
    principal_objects=None
    for name,expected in [('principal241',(241,189,30058,85187728)),
                          ('dense239',(239,187,387494,269805528))]:
        directory=HERE/'equations'/name
        metadata_path=directory/'raw/raw_audit_input.json'
        metadata=read(metadata_path)
        raw=read(directory/'raw/equation.json')
        target=read(directory/'natural/equation.json')
        cert=read(directory/'natural/elimination_certificate.json')
        expanded=read(directory/'natural/expanded_polynomial.json')
        boundary=semantic.audit(metadata_path,parent,True)
        require(boundary['checks']==225,'semantic audit count changed')
        ar,ac=affine.verify(metadata,raw)
        require((ar['original_variables'],ar['original_rows'],ar['nonnegative_affine_restorations'],
                 ar['retained_variables'],ar['retained_rows'])==(777,725,428,349,297),
                'unexpected semantic/affine graph census')
        receipt,polynomial=contraction.verify(raw,target,cert)
        require(receipt==read(directory/'natural/VERIFICATION.json'),'stored contraction receipt differs')
        require(polynomial==expanded['terms'],'collected coefficient list differs')
        require(receipt['exact_degree']==4,'polynomial is not an exact quartic')
        actual=tuple(receipt[k] for k in ('variables','rows','expanded_monomials','coefficient_height'))
        require(actual==expected,'unexpected complete equation census')
        live={v for c,m in polynomial for v in m}
        require(live==set(range(receipt['variables'])),'declared coordinate is unused')
        require(all(type(c) is int and c!=0 and m==sorted(m) for c,m in polynomial),
                'noncanonical integer coefficient list')
        require((directory/'natural/residuals.txt').read_text()==readable(target,name),
                'readable residual list differs from exact JSON')
        result['variants'][name]={'semantic_checks':boundary['checks'],
            'frame_atoms':boundary['frame_atom_count'],'independent_seed_indices':boundary['seed_count'],
            'semantic_metadata_sha256':boundary['raw_sha256'],'affine':ar,'contraction':receipt,
            'equation_sha256':sha256((directory/'natural/equation.json').read_bytes()).hexdigest(),
            'polynomial_sha256':sha256((directory/'natural/expanded_polynomial.json').read_bytes()).hexdigest()}
        if name=='principal241':principal_objects=(metadata,raw,target,cert)
    metadata,raw,target,cert=principal_objects
    bad=deepcopy(raw);bad['residuals'][0]['terms'][0][0]+=1
    result['negative_controls'].append(must_reject('changed exported raw coefficient',lambda:affine.verify(metadata,bad)))
    badcert=deepcopy(cert);badcert['steps'][0]['restoration'][0][0]+=1
    result['negative_controls'].append(must_reject('changed natural restoration',
        lambda:contraction.verify(raw,target,badcert)))
    badtarget=deepcopy(target);badtarget['residuals'][0]['terms'][0][0]+=1
    changedcert=deepcopy(cert);changedcert['target_equation_sha256']=sha256(canonical(badtarget)).hexdigest()
    result['negative_controls'].append(must_reject('changed target coefficient with repaired hash',
        lambda:contraction.verify(raw,badtarget,changedcert)))
    with tempfile.TemporaryDirectory(prefix='conzfc241-negative-') as td:
        changed=deepcopy(metadata)
        changed['cap_certificate']['semantic_frame_atoms'].pop()
        temp=Path(td)/'corrupt_frame.json';temp.write_text(json.dumps(changed))
        result['negative_controls'].append(must_reject('omitted semantic frame atom',
            lambda:semantic.audit(temp,parent,True)))
        changed=deepcopy(metadata)
        row=next(r for r in changed['rows'] if r['label']=='modular.common_root')
        row['terms'][0][0]+=1
        temp=Path(td)/'corrupt_root.json';temp.write_text(json.dumps(changed))
        result['negative_controls'].append(must_reject('changed common-root equation',
            lambda:semantic.audit(temp,parent,True)))
    if rebuild:
        for name,cap in [('principal241',32),('dense239',64)]:
            with tempfile.TemporaryDirectory(prefix='conzfc241-rebuild-') as td:
                output=Path(td)/name
                command=[sys.executable,'-B']
                if sys.flags.optimize:command.append('-O')
                command += [str(HERE/'build.py'),'--support-cap',str(cap),'--output',str(output)]
                done=subprocess.run(command,cwd=HERE,capture_output=True,text=True)
                require(done.returncode==0,'portable rebuild failed: '+done.stderr[-3000:])
                old=HERE/'equations'/name
                oldpaths={str(p.relative_to(old)) for p in old.rglob('*.json')}
                newpaths={str(p.relative_to(output)) for p in output.rglob('*.json')}
                require(oldpaths==newpaths,'rebuild JSON inventory differs')
                for rel in sorted(oldpaths):
                    require((old/rel).read_bytes()==(output/rel).read_bytes(),
                            'byte-exact rebuild differs: '+name+'/'+rel)
                result['rebuilds'][name]={'json_files':len(oldpaths),'byte_identical':True,
                                         'optimized_python':bool(sys.flags.optimize)}
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true')
    p.add_argument('--output',type=Path)
    a=p.parse_args();result=run(a.rebuild)
    body=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(body)
    print(body,end='')
