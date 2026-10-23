#!/usr/bin/env python3
"""Finite release audit; reconstruct in a temporary copy, leaving release intact."""
import gzip,hashlib,json,random,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def require(ok,msg):
    if not ok:raise ValueError(msg)
def fixed_values(manifest):
    d=json.loads((ROOT/manifest).read_text());out={}
    ports=[int.from_bytes(gzip.decompress((ROOT/'coefficients'/(n+'.bin.gz')).read_bytes()),'little') for n in ['beta','K','MC','MF_source']]
    for row in d['live_fixed_coefficients']:
        enc=(ROOT/row['file']).read_bytes();raw=gzip.decompress(enc)
        require(hashlib.sha256(enc).hexdigest()==row['gzip_sha256'],'compressed fixed leaf hash')
        require(hashlib.sha256(raw).hexdigest()==row['raw_sha256'],'raw fixed leaf hash')
        require(raw[0] in (0,1) and len(raw)>=2,'signed fixed leaf encoding')
        x=int.from_bytes(raw[1:],'little')*(-1 if raw[0] else 1)
        recipe=row['recipe']
        if isinstance(recipe,dict):expected=1<<recipe['power_of_two']
        else:
            expected=0
            for t in recipe:
                z=t['coefficient']
                for p,e in zip(ports,t['powers']):z*=p**e
                expected+=z
        require(expected==x,'fixed coefficient recipe mismatch: '+row['name']);out[row['name']]=x
    return out
def eval_dag(d,values,fixed,p):
    out=[]
    for row in d['nodes']:
        k=row['kind']
        if k=='literal':x=row['value']
        elif k=='fixed':x=fixed[row['name']]
        elif k=='variable':x=values[row['name']]
        else:
            a,b=out[row['left']],out[row['right']]
            x=a+b if k=='add' else a-b if k=='sub' else a*b
        out.append(x%p)
    return out[d['output']]
def structure(d):
    live=set();todo=[d['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i);node=d['nodes'][i]
        if 'left' in node:
            require(0<=node['left']<i and 0<=node['right']<i,'nonacyclic circuit');todo.extend([node['left'],node['right']])
    require(len(live)==len(d['nodes']),'dead gates')
    counts={k:sum(x['kind']==k for x in d['nodes']) for k in ('add','sub','mul')}
    require(counts==d['operation_counts'],'operation count')
    return sum(counts.values())
def leading(d,fixed,p):
    degrees=[];coeff=[]
    for row in d['nodes']:
        k=row['kind']
        if k=='variable':deg,co=1,1
        elif k=='literal':deg,co=0,row['value']%p
        elif k=='fixed':deg,co=0,fixed[row['name']]%p
        else:
            a,b=row['left'],row['right']
            if k=='mul':deg,co=degrees[a]+degrees[b],coeff[a]*coeff[b]%p
            else:
                deg=max(degrees[a],degrees[b]);ca=coeff[a] if degrees[a]==deg else 0;cb=coeff[b] if degrees[b]==deg else 0
                co=(ca+cb if k=='add' else ca-cb)%p
        degrees.append(deg);coeff.append(co)
    return degrees[d['output']],coeff[d['output']]
def main():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for record in pins['exact_inherited_files']:
        raw=(ROOT/record['local_file']).read_bytes()
        require(hashlib.sha256(raw).hexdigest()==record['sha256'],'inherited file SHA256')
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob==record['expected_upstream_git_blob_sha1'],'inherited Git blob pin')
    fixed9=fixed_values('fixed_coefficients.json');fixed10=fixed_values('fixed_coefficients10.json');rng=random.Random(20261023)
    summaries=[]
    for W in [220,239]:
        dags={kind:json.loads((ROOT/'generated'/f'sparse{W}_nine_{kind}.json').read_text()) for kind in ['positive','natural','positive_degree_certificate','natural_degree_certificate']}
        for kind,d in dags.items():
            ops=structure(d)
            if 'certificate' in kind:
                degree,co=leading(d,fixed9,1000000007);require(degree==108296*W+53272 and co!=0,'nine degree certificate')
                lam=pow(2,2134939,1000000007)
                expected=pow(2,2050,1000000007)*pow(lam,54148*W+26496,1000000007)%1000000007
                require(co==expected,'closed-form leading coefficient')
            else:summaries.append(dict(W=W,domain=d['domain'],operations=ops,degree=d['degree']))
        for p in [1000000007,1000000009,2147483647]:
            for _ in range(32):
                nat={n:rng.randrange(1000) for n in dags['natural']['variables']};pos={n:x+1 for n,x in nat.items()}
                vals=[eval_dag(dags[k],pos if 'positive' in k else nat,fixed9,p) for k in dags]
                require(len(set(vals))==1,'natural/positive/certificate identity replay')
        ten=json.loads((ROOT/'generated'/f'sparse{W}_ten_integer.json').read_text());ops=structure(ten);degree,co=leading(ten,fixed10,1000000007)
        require(degree==ten['exact_degree'] and co!=0,'ten-integer degree certificate')
        summaries.append(dict(W=W,domain='integers',operations=ops,degree=degree))
    with tempfile.TemporaryDirectory(prefix='proveit_sparse_audit_') as td:
        copy=Path(td)/'release';shutil.copytree(ROOT,copy,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        scripts=['build_sparse_nine.py','build_sparse_ten.py','materialize.py','materialize_ten.py','verify_source.py']
        for name in scripts:
            command=[sys.executable]
            if not __debug__:command.append('-O')
            command.append(str(copy/name));r=subprocess.run(command,capture_output=True,text=True)
            require(r.returncode==0,name+' failed: '+r.stdout+r.stderr)
        command=[sys.executable]
        if not __debug__:command.append('-O')
        command.extend([str(copy/'audit_nine_independent.py'),'--root',str(copy),'--output',str(copy/'nine_independent_audit.json')])
        r=subprocess.run(command,capture_output=True,text=True)
        require(r.returncode==0,'independent exact nine-variable audit failed: '+r.stdout+r.stderr)
        commands=[[str(copy/'audit_exported_circuits.py'),str(copy),'--out',str(copy/'independent_export_certificate.json')]]
        for W in [220,239]:
            source=str(copy/f'targets_sparse{W}.json')
            commands.append([str(copy/'audit_sparse_source.py'),source,source,'--out',str(copy/f'source_independent{W}.json')])
        for tail in commands:
            command=[sys.executable]
            if not __debug__:command.append('-O')
            r=subprocess.run(command+tail,capture_output=True,text=True)
            require(r.returncode==0,'independent artifact audit failed: '+r.stdout+r.stderr)
        files=[*ROOT.glob('generated/*.json'),ROOT/'fixed_coefficients.json',ROOT/'fixed_coefficients10.json',ROOT/'source_certificate.json',ROOT/'nine_independent_audit.json',ROOT/'independent_export_certificate.json',ROOT/'source_independent220.json',ROOT/'source_independent239.json',*ROOT.glob('coefficients/fixed/*.bin.gz'),*ROOT.glob('coefficients/fixed10/*.bin.gz')]
        for p in files:require(p.read_bytes()==(copy/p.relative_to(ROOT)).read_bytes(),'nonreproducible artifact '+str(p.relative_to(ROOT)))
    print(json.dumps(dict(status='PASS',scope='Finite structural, arithmetic, exact-degree and source audits; no decision of consistency or new end-to-end formal proof',circuit_variants=summaries,regenerated_files=len(files),modular_identity_replays=2*3*32),indent=2))
if __name__=='__main__':main()
