#!/usr/bin/env python3
"""Rebuild Report210 checks, tables, PDF and deterministic ZIP without network access."""
import argparse, ast, hashlib, json, os, shutil, subprocess, sys, zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
STATIC=['Report210.tex','verify_families.py','reproduce.py','README.txt','requirements.txt','SOURCES.txt']
GENERATED=['data/exact_checks.json','tables/exact.tex']

def require(ok,message):
    if not ok: raise RuntimeError(message)

def dump(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')

def run(cmd,cwd,log,env=None):
    result=subprocess.run(cmd,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log.write_text(result.stdout,encoding='utf-8')
    require(result.returncode==0,'command failed; inspect '+str(log))
    return result.stdout

def tables(data):
    lines=[r'\begin{table}[htbp]\centering\small',
           r'\caption{Direct enumeration and the exact disjoint lower envelope}\label{tab:exact}',
           r'\begin{tabular}{r r r r r r}\toprule',
           r'$k$ & $G_k$ & $J_k$ & $G_k+J_k$ & $M_{2k}$ & Omitted \\ \midrule']
    for r in data['exhaustive']:
        total=r['G']+r['J']
        lines.append(f"{r['k']} & {r['G']} & {r['J']} & {total} & {r['M']} & {r['M']-total} "+r'\\')
    lines += [r'\bottomrule\end{tabular}',r'\end{table}']
    return {'tables/exact.tex':'\n'.join(lines)+'\n'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--initialize',action='store_true',help='Authoring only: permit missing baseline generated files')
    ap.add_argument('--self-test-failure',action='store_true',help='Intentionally fail before any writes')
    args=ap.parse_args()
    if args.self_test_failure: require(False,'intentional failure: guards are active')
    out=args.out.resolve()
    require(out!=ROOT and ROOT not in out.parents,'output must be outside the source directory')
    require(not out.exists(),'output directory already exists; choose a fresh directory')
    for name in STATIC:
        require((ROOT/name).is_file(),'missing static member '+name)
        if name.endswith('.py'):
            require(not any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse((ROOT/name).read_text()))),'assert guard found in '+name)
    out.mkdir(parents=True)
    stage=out/'Report210'; stage.mkdir()
    logs=out/'logs'; logs.mkdir()
    for name in STATIC: shutil.copyfile(ROOT/name,stage/name)
    flags=['-O'] if sys.flags.optimize else []
    for script in ['verify_families.py']:
        run([sys.executable,*flags,script],stage,logs/(script+'.log'))
        probe=subprocess.run([sys.executable,*flags,script,'--self-test-failure'],cwd=stage,text=True,capture_output=True)
        require(probe.returncode!=0 and 'intentional failure' in probe.stderr,'script false-guard probe failed: '+script)
    data=json.loads((stage/'data/exact_checks.json').read_text())
    require(data['status']=='passed','failed data status')
    require(data['exhaustive_max_k']==8 and data['partition_max_n']==10,'unexpected check range')
    require(data['explicit_guard_calls']>400000,'too few explicit guards')
    for name,value in tables(data).items():
        (stage/name).parent.mkdir(parents=True,exist_ok=True)
        (stage/name).write_text(value,encoding='utf-8')
    for name in GENERATED:
        if not (ROOT/name).exists():
            require(args.initialize,'missing baseline '+name)
        else: require((ROOT/name).read_bytes()==(stage/name).read_bytes(),'generated baseline mismatch: '+name)
    env=os.environ.copy(); env.update(SOURCE_DATE_EPOCH='1791072000',FORCE_SOURCE_DATE='1',TZ='UTC',LC_ALL='C')
    probe=subprocess.run(['kpsewhich','pdflatex.fmt'],cwd=stage,env=env,text=True,capture_output=True)
    if probe.returncode or not probe.stdout.strip():
        dist=Path(run(['kpsewhich','-var-value=TEXMFDIST'],stage,logs/'texdist.log',env).strip())
        require(dist.is_dir(),'installed TeX tree is missing')
        trees=[dist]; sibling=dist.parent.parent/'texmf'
        if sibling.is_dir(): trees.append(sibling)
        env['TEXMF']='{'+','.join(map(str,trees))+'}'
        env['TEXFORMATS']=str(stage)+os.pathsep
        run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','pdflatex.ini'],stage,logs/'format.log',env)
        require((stage/'pdflatex.fmt').is_file(),'private TeX format was not created')
        maps=[]
        for name in ['cm.map','cmextra.map','latxfont.map','symbols.map','lm.map']:
            path=Path(run(['kpsewhich',name],stage,logs/(name+'.log'),env).strip())
            require(path.is_file(),'missing installed font map '+name); maps.append(path.read_bytes())
        (stage/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    previous=None; stable=False
    for i in range(1,6):
        run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','Report210.tex'],stage,logs/f'latex{i}.log',env)
        pdf=(stage/'Report210.pdf').read_bytes()
        if i>=3 and pdf==previous: stable=True; break
        previous=pdf
    require(stable,'PDF did not reach byte stability')
    latex=(logs/f'latex{i}.log').read_text()
    require('Overfull \\hbox' not in latex and 'Overfull \\vbox' not in latex,'overfull PDF layout')
    require('undefined references' not in latex and 'undefined citations' not in latex,'unresolved PDF reference')
    if (ROOT/'Report210.pdf').exists():
        require((ROOT/'Report210.pdf').read_bytes()==(stage/'Report210.pdf').read_bytes(),'rebuilt PDF baseline mismatch; verify the TeX/font toolchain')
    else: require(args.initialize,'missing baseline Report210.pdf')
    members=STATIC+GENERATED+['Report210.pdf']
    archive=out/'Report210-reproducibility.zip'
    with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_STORED) as z:
        for name in sorted(members):
            info=zipfile.ZipInfo('Report210/'+name,(2026,10,4,0,0,0))
            info.create_system=3; info.external_attr=0o100644<<16
            z.writestr(info,(stage/name).read_bytes())
    receipt={'members':{name:hashlib.sha256((stage/name).read_bytes()).hexdigest() for name in sorted(members)},
             'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
             'source_generated_baselines_checked':not args.initialize,
             'verification_subprocess_optimization':sys.flags.optimize,
             'producer_false_guard_probes_passed':True,
             'pdf_rebuilt_to_byte_stability':True,
             'zip_member_count':len(members)}
    dump(out/'reproduction.json',receipt)
    print(json.dumps(receipt,indent=2,sort_keys=True))

if __name__=='__main__':main()
