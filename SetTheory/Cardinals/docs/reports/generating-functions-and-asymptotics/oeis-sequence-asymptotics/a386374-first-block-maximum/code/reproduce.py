#!/usr/bin/env python3
"""Rebuild Report208 checks, tables, PDF and a deterministic ZIP. No network access."""
import argparse, hashlib, json, os, shutil, subprocess, sys, zipfile
from pathlib import Path

ROOT=Path(__file__).resolve().parent
STATIC=['Report208.tex','verify.py','independent_check.py','reproduce.py','README.txt','requirements.txt','SOURCES.txt']
GENERATED=['data/validation.json','data/independent.json','tables/exact.tex','tables/diagnostic.tex','tables/phase.tex']

def require(ok,message):
    if not ok: raise RuntimeError(message)

def dump(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')

def number(s):
    # Preserve the recorded decimal string exactly in the displayed table.
    if 'e' in s.lower():
        mant,exp=s.lower().split('e')
        return mant+r'\times10^{'+str(int(exp))+'}'
    return s

def tables(validation,independent):
    w=independent['weak_first_22']; u=independent['strict_first_23']
    lines=[r'\begin{table}[htbp]\centering',r'\caption{Exact initial counts}\label{tab:exact}',
           r'\begin{tabular}{r r r}\toprule',r'$n$ & $a_n$ & $u_n$ \\\midrule']
    lines += [f'{n} & {w[n]} & {u[n]} '+r'\\' for n in range(13)]
    lines += [r'\bottomrule\end{tabular}\end{table}']
    exact='\n'.join(lines)+'\n'
    lines=[r'\begin{table}[htbp]\centering\small',
           r'\caption{Relative errors of the fixed-range root-free diagnostics}\label{tab:diagnostic}',
           r'\begin{tabular}{r r r r}\toprule',r'$n$ & Order $0$ & Order $1$ & Order $2$ \\\midrule']
    # Three significant figures improve readability; data retains full precision.
    for row in validation['diagnostics_not_proof']:
        vals=[number(format(float(x),'.3g')) for x in row['relative_rootfree_errors']]
        lines.append(str(row['n'])+' & '+' & '.join('$'+x+'$' for x in vals)+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{table}']
    diagnostic='\n'.join(lines)+'\n'
    lines=[r'\begin{table}[htbp]\centering',r'\caption{Real-index phase diagnostics}\label{tab:phase}',
           r'\begin{tabular}{r r r r}\toprule',r'$m$ & $\log_{10}n$ at peak & Peak $nP/m$ & Trough $nP/\log m$ \\\midrule']
    rows=validation['phase_diagnostics_not_proof']
    require(len(rows)%2==0,'phase records must pair')
    for i in range(0,len(rows),2):
        peak,trough=rows[i:i+2]
        require(peak['m']==trough['m'] and peak['type']=='peak' and trough['type']=='trough','phase pair')
        lines.append(f"{peak['m']} & {float(peak['log10n']):.6f} & {float(peak['nP_over_m']):.9f} & {float(trough['nP_over_logm']):.9f} "+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{table}']
    return {'tables/exact.tex':exact,'tables/diagnostic.tex':diagnostic,'tables/phase.tex':'\n'.join(lines)+'\n'}

def run(cmd,cwd,log,env=None):
    result=subprocess.run(cmd,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log.write_text(result.stdout,encoding='utf-8')
    require(result.returncode==0,'command failed; inspect '+str(log))
    return result.stdout

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--initialize',action='store_true',help='Authoring only: permit missing baseline generated files')
    ap.add_argument('--self-test-failure',action='store_true',help='Intentionally fail before any writes')
    args=ap.parse_args()
    if args.self_test_failure: require(False,'intentional failure: guards are active')
    out=args.out.resolve()
    require(out!=ROOT and ROOT not in out.parents,'output must be outside the source directory')
    out.mkdir(parents=True,exist_ok=True)
    stage=out/'Report208'; stage.mkdir(exist_ok=True)
    logs=out/'logs'; logs.mkdir(exist_ok=True)
    for name in STATIC:
        require((ROOT/name).is_file(),'missing static member '+name)
        shutil.copyfile(ROOT/name,stage/name)
    flags=['-O'] if sys.flags.optimize else []
    run([sys.executable,*flags,'verify.py'],stage,logs/'verify.log')
    run([sys.executable,*flags,'independent_check.py'],stage,logs/'independent.log')
    valname='validation_optimized.json' if sys.flags.optimize else 'validation.json'
    indname='independent_optimized.json' if sys.flags.optimize else 'independent_normal.json'
    validation=json.loads((stage/valname).read_text())
    independent=json.loads((stage/indname).read_text())
    require(independent.pop('optimization')==sys.flags.optimize,'optimization flag mismatch')
    require(validation['exact_checks']['oeis_terms']==22,'weak displayed count')
    require(validation['exact_checks']['strict_oeis_terms']==23,'strict displayed count')
    require(independent['explicit_guard_calls']==36,'independent check count')
    require(not validation['exact_checks']['assert_statements_used'] and not independent['assert_statements_used'],'assert-free checks')
    # Independently compare both exact recurrences to all rational-EGF values.
    sys.path.insert(0,str(stage))
    import verify
    require(verify.exact(21)==independent['weak_first_22'],'weak cross-check')
    require(verify.strict_exact(22)==independent['strict_first_23'],'strict cross-check')
    caught=False
    try: verify.check(False,'intentional guard probe')
    except RuntimeError: caught=True
    require(caught,'producer guard is inactive')
    dump(stage/'data/validation.json',validation)
    dump(stage/'data/independent.json',independent)
    for name,value in tables(validation,independent).items():
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
        run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','Report208.tex'],stage,logs/f'latex{i}.log',env)
        pdf=(stage/'Report208.pdf').read_bytes()
        if i>=3 and pdf==previous: stable=True; break
        previous=pdf
    require(stable,'PDF did not reach byte stability')
    latex=(logs/f'latex{i}.log').read_text()
    require('Overfull \\hbox' not in latex and 'Overfull \\vbox' not in latex,'overfull PDF layout')
    require('undefined references' not in latex and 'undefined citations' not in latex,'unresolved PDF reference')
    members=STATIC+GENERATED+['Report208.pdf']
    archive=out/'Report208-reproducibility.zip'
    with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_STORED) as z:
        for name in sorted(members):
            info=zipfile.ZipInfo('Report208/'+name,(2026,10,4,0,0,0))
            info.create_system=3; info.external_attr=0o100644<<16
            z.writestr(info,(stage/name).read_bytes())
    receipt={'members':{name:hashlib.sha256((stage/name).read_bytes()).hexdigest() for name in sorted(members)},
             'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
             'source_generated_baselines_checked':not args.initialize,
             'producer_false_guard_caught':caught,
             'pdf_rebuilt_to_byte_stability':True,
             'independent_optimization_flag_removed_for_canonical_data':True}
    dump(out/'reproduction.json',receipt)
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
