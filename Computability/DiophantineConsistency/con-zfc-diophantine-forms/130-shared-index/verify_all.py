#!/usr/bin/env python3
"""Offline verification of the complete delivered packet.

Source and mathematical files remain unchanged. Builders that write their own
directory run in a temporary copy. No finite test is used as a substitute for
the ordinary mathematical proofs in the report and each construction's proof.
"""
from collections import defaultdict
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, tempfile

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest_check():
    obj = read(HERE/'MANIFEST.json')
    names = set()
    for item in obj['files']:
        rel = Path(item['path'])
        require(not rel.is_absolute() and '..' not in rel.parts, 'unsafe manifest path')
        require(item['path'] not in names, 'duplicate manifest entry')
        names.add(item['path'])
        path=HERE/rel
        require(path.is_file(),'missing file: '+item['path'])
        require(path.stat().st_size==item['size'],'file size differs: '+item['path'])
        require(digest(path)==item['sha256'],'file digest differs: '+item['path'])
    import package_release
    actual={p.relative_to(HERE).as_posix() for p in package_release.paths()}
    require(actual==names,'delivered file inventory differs from manifest')
    return {'status':'PASS','files':len(names)}


def additional_sources():
    obj=read(HERE/'SOURCE_SNAPSHOT.json')
    require(obj['commit']=='f4d8db99e060339f3306a04d507c35bc1d0d68c5',
            'source snapshot changed')
    for item in obj['additional_retained_sources']:
        require(digest(HERE/item['retained_path'])==item['sha256'],
                'additional source changed: '+item['retained_path'])
    return {'status':'PASS','retained_files':len(obj['additional_retained_sources']),
            'incoming_archive_pins':len(obj['incoming_archives'])}


def run_python(script, arguments=(), cwd=None):
    command=[sys.executable,'-B']
    if sys.flags.optimize:
        command.append('-O')
    command += [str(script),*map(str,arguments)]
    result=subprocess.run(command,cwd=cwd or HERE,capture_output=True,text=True)
    require(result.returncode==0,'child verification failed: '+str(script)+
            '\n'+result.stdout[-3000:]+'\n'+result.stderr[-3000:])
    return result.stdout


def integer_lift():
    parent=read(HERE/'direct/equations/principal241/natural/equation.json')
    equation=read(HERE/'integer964/equation.json')
    expanded=read(HERE/'integer964/expanded_polynomial.json')
    n=len(parent['variables'])
    require(len(equation['variables'])==4*n,'integer lift variable count')
    require(equation['residuals'][:len(parent['residuals'])]==parent['residuals'],
            'integer lift original residuals differ')
    require(len(equation['residuals'])==len(parent['residuals'])+n,'integer lift row count')
    for i,row in enumerate(equation['residuals'][len(parent['residuals']):]):
        actual={tuple(m):c for c,m in row['terms']}
        expected={():1,(i,):8,**{(n+3*i+j,n+3*i+j):-1 for j in range(3)}}
        require(actual==expected,'three-square guard differs at '+str(i))
    coefficients=defaultdict(int)
    for row in equation['residuals']:
        for c,m in row['terms']:
            require(type(c) is int and len(m)<=2,'nonquadratic or nonintegral residual')
            for d,k in row['terms']:
                coefficients[tuple(sorted(m+k))]+=c*d
    terms=[[c,list(m)] for m,c in sorted(coefficients.items()) if c]
    require(terms==expanded['terms'],'integer lift complete expansion differs')
    require({i for c,m in terms for i in m}==set(range(4*n)),
            'unused integer lift variable')
    metrics={'variables':len(equation['variables']),
             'quadratic_rows':len(equation['residuals']),
             'exact_degree':max(len(m) for c,m in terms),
             'expanded_monomials':len(terms),
             'max_abs_expanded_coefficient':max(abs(c) for c,m in terms)}
    require(metrics==equation['metrics'],'integer lift metadata differs')
    require(tuple(metrics.values())==(964,430,4,33083,85187969),
            'integer lift verified census changed')
    return {'status':'PASS',**metrics}


def center_rebuild(work):
    copied=work/'center246'
    shutil.copytree(HERE/'center246',copied,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
    run_python(copied/'build_verify.py',cwd=copied)
    files=['equation.json','center_defect.json','RESULTS.json']
    for name in files:
        require((copied/name).read_bytes()==(HERE/'center246'/name).read_bytes(),
                'center rebuild differs: '+name)
    result=read(copied/'RESULTS.json')
    require(result['ok'] and len(result['checks'])==151,'center check count/status')
    return {'status':'PASS','byte_identical_files':files,'checks':len(result['checks']),
            'operations':result['operations'],'exact_degree':result['exact_degree'],
            'equation_sha256':digest(HERE/'center246/equation.json')}


def run(rebuild=False, only_manifest=False):
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),
            'manifest':manifest_check()}
    if only_manifest:
        return result
    result['additional_sources']=additional_sources()
    with tempfile.TemporaryDirectory(prefix='conzfc-release-') as directory:
        work=Path(directory)
        direct_output=work/'direct.json'
        arguments=['--output',direct_output]+(['--rebuild'] if rebuild else [])
        run_python(HERE/'direct/verify.py',arguments)
        result['direct']=read(direct_output)
        positive_output=work/'positive.json'
        run_python(HERE/'positive/verify.py',['--output',positive_output])
        result['positive']=read(positive_output)
        result['center246']=center_rebuild(work)
        run_python(HERE/'build_report_support.py',['--check'])
        result['report_binding']=read(HERE/'REPORT_BINDING.json')
        result['integer964']=integer_lift()
    result['equations']={
        'principal241':digest(HERE/'direct/equations/principal241/natural/equation.json'),
        'dense239':digest(HERE/'direct/equations/dense239/natural/equation.json'),
        'positive86':digest(HERE/'positive/quotient_absorbed.json'),
        'positive246':digest(HERE/'center246/equation.json'),
        'integer964':digest(HERE/'integer964/equation.json')}
    result['proof_scope']='Finite artifact verification; unbounded equivalence uses the supplied ordinary proofs and identified inherited calibration.'
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--rebuild',action='store_true')
    parser.add_argument('--manifest-only',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=run(args.rebuild,args.manifest_only)
    body=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        output=args.output.resolve()
        require(not output.is_relative_to(HERE),'receipt output must be outside the frozen packet')
        output.parent.mkdir(parents=True,exist_ok=True)
        output.write_text(body)
    print(json.dumps({'status':result['status'],'manifest_files':result['manifest']['files'],
                      'optimized_python':result['optimized_python'],
                      'rebuild':bool(args.rebuild)},indent=2))
