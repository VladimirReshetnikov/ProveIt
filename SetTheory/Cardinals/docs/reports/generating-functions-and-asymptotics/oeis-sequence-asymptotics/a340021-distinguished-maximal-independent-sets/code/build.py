"""Deterministic public rebuild for Report206. Run with Python or Python -O.
Outputs are finite checks/illustrations, not certificates of asymptotic constants.
"""
from decimal import Decimal
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent
EPOCH = '1791072000'  # 2026-10-04 00:00:00 UTC
PUBLIC = ['Report206.tex', 'Report206.pdf', 'README.txt', 'requirements.txt',
          'build.py', 'verify_exact.py', 'independent_checks.py', 'diagnostics.py',
          'exact_results.json', 'independent_results.json', 'diagnostics.json',
          'tables.tex', 'checks.json']

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def dump(name, obj):
    (ROOT/name).write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n', encoding='utf-8')

def execute(script):
    flags = ['-O'] if sys.flags.optimize else []
    result = subprocess.run([sys.executable, *flags, str(ROOT/script)], cwd=ROOT,
                            text=True, capture_output=True, check=True)
    require(not result.stderr.strip(), f'{script} wrote unexpected stderr: {result.stderr}')
    return json.loads(result.stdout)

def failure_guards():
    # These subprocesses must fail identically under BOTH Python modes, regardless
    # of which mode invoked build.py. Deliberate errors are caught by this driver.
    for script in ['verify_exact.py', 'independent_checks.py', 'build.py']:
        for optimize in [False, True]:
            source = ("import importlib.util; "
                      f"s=importlib.util.spec_from_file_location('guard', {str(ROOT/script)!r}); "
                      "m=importlib.util.module_from_spec(s); s.loader.exec_module(m); "
                      "m.require(False, 'EXPECTED_GUARD_FAILURE')")
            flags = ['-O'] if optimize else []
            result = subprocess.run([sys.executable,*flags,'-c',source],
                                    text=True,capture_output=True)
            require(result.returncode != 0 and 'EXPECTED_GUARD_FAILURE' in result.stderr,
                    f'guard did not fail correctly: {script}, optimized={optimize}')
    return 6

def sci(value):
    d=Decimal(str(value))
    if not d:
        return '$0$'
    s=f'{d:.5E}'
    mantissa, exponent=s.split('E')
    return '$'+mantissa+r'\times10^{'+str(int(exponent))+'}$'

def fixed(value):
    return f'{Decimal(str(value)):.6f}'

def tables(exact, diagnostic):
    lines=[r'\begin{longtable}{r r}',
           r'\caption{The twenty displayed reference terms, all reproduced exactly.}\label{tab:exact}\\',
           r'\toprule $n$ & $U_n$ \\ \midrule',
           r'\endfirsthead',r'\toprule $n$ & $U_n$ \\ \midrule',r'\endhead',
           r'\bottomrule\endfoot']
    for n,value in enumerate(exact['oeis_terms']):
        lines.append(f'{n} & {value} '+r'\\')
    lines += [r'\end{longtable}',
        r'\begin{table}[htbp]\centering\small',
        r'\caption{Noncertified relative errors $H_R(n)/b_n-1$. The symmetry error is excluded.}\label{tab:orders}',
        r'\begin{tabular}{r r r r r}\toprule',
        r'$n$ & $R=1$ & $R=2$ & $R=3$ & $R=4$ \\ \midrule']
    for row in diagnostic['algebraic_orders'][:4]:
        n=row['n']
        label={'1000000':'$10^6$','1000000000000':'$10^{12}$'}.get(n,n)
        lines.append(label+' & '+' & '.join(sci(q['relative_error']) for q in row['approximations'])+r' \\')
    lines += [r'\bottomrule\end{tabular}\end{table}',
        r'\begin{table}[htbp]\centering\small',
        r'\caption{Noncertified carrier switch probabilities. $q_k=q_{k+1}$ at $s=0$; substantial outside mass may remain at finite $k$.}\label{tab:switch}',
        r'\begin{tabular}{r r r r r r}\toprule',
        r'$k$ & $s$ & $q_k(t)$ & $q_{k+1}(t)$ & Outside pair & Logistic $q_{k+1}$ \\ \midrule']
    for row in diagnostic['switches']:
        if row['s']==0 or row['k']==300:
            lines.append(f"{row['k']} & {row['s']} & "+' & '.join(fixed(row[k]) for k in ['P_k','P_k1','outside','logistic_P_k1'])+r' \\')
    lines += [r'\bottomrule\end{tabular}\end{table}',
        r'\begin{table}[htbp]\centering\small',
        r'\caption{Noncertified Newton errors $z_j-n$ with $R=4$. The target is the identity count, not the exact unlabeled count.}\label{tab:inverse}',
        r'\begin{tabular}{r r r r r}\toprule',
        r'Target $n$ & $j=0$ & $j=1$ & $j=2$ & $j=3$ \\ \midrule']
    for row in diagnostic['inverse']:
        label='$10^6$' if row['target_n']==10**6 else str(row['target_n'])
        lines.append(label+' & '+' & '.join(sci(v) for v in row['errors'])+r' \\')
    lines += [r'\bottomrule\end{tabular}\end{table}',r'\clearpage']
    return '\n'.join(lines)+'\n'

def main():
    require(sys.version_info >= (3,10), 'Python 3.10 or newer is required')
    exact=execute('verify_exact.py')
    independent=execute('independent_checks.py')
    diagnostic=execute('diagnostics.py')
    require(exact['status']=='PASS' and independent['status']=='PASS','finite checks failed')
    require(exact['burnside_rows'][:8]==independent['permutation_burnside_rows'],
            'independent black-size rows disagree')
    guard_count=failure_guards()
    dump('exact_results.json',exact)
    dump('independent_results.json',independent)
    dump('diagnostics.json',diagnostic)
    (ROOT/'tables.tex').write_text(tables(exact,diagnostic),encoding='utf-8')
    dump('checks.json',{'status':'PASS','independent_rows_match_through_n':7,
        'deliberate_failure_guard_cases':guard_count,
        'normal_and_optimized_guards_tested':True,
        'scope':'Finite and formal checks; floating diagnostics are not error certificates.'})
    env=dict(os.environ,SOURCE_DATE_EPOCH=EPOCH,FORCE_SOURCE_DATE='1',TZ='UTC',LC_ALL='C')
    with tempfile.TemporaryDirectory(prefix='report206-tex-') as tmp:
        work=Path(tmp)
        for name in ['Report206.tex','tables.tex']:
            shutil.copyfile(ROOT/name,work/name)
        def tex_run(command):
            result=subprocess.run(command,cwd=work,env=env,text=True,capture_output=True)
            require(result.returncode==0,'TeX command failed:\n'+result.stdout+result.stderr)
            return result.stdout.strip()
        probe=subprocess.run(['kpsewhich','pdflatex.fmt'],cwd=work,env=env,text=True,capture_output=True)
        if probe.returncode or not probe.stdout.strip():
            dist=Path(tex_run(['kpsewhich','-var-value=TEXMFDIST']))
            require(dist.is_dir(),'installed TeX tree is missing')
            trees=[dist]
            sibling=dist.parent.parent/'texmf'
            if sibling.is_dir(): trees.append(sibling)
            env['TEXMF']='{'+','.join(map(str,trees))+'}'
            env['TEXFORMATS']=str(work)+os.pathsep
            tex_run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
                     '-halt-on-error','-jobname=pdflatex','pdflatex.ini'])
            require((work/'pdflatex.fmt').is_file(),'private TeX format was not created')
            maps=[]
            for name in ['cm.map','cmextra.map','latxfont.map','symbols.map','lm.map']:
                path=Path(tex_run(['kpsewhich',name]))
                require(path.is_file(),'missing installed font map: '+name)
                maps.append(path.read_bytes())
            (work/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
        previous=None
        stable=False
        for i in range(5):
            tex_run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error',
                     '-file-line-error','Report206.tex'])
            pdf=(work/'Report206.pdf').read_bytes()
            if i>=2 and pdf==previous:
                stable=True
                break
            previous=pdf
        require(stable,'PDF did not reach byte stability in five passes')
        log=(work/'Report206.log').read_text(errors='replace')
        require('Overfull \\hbox' not in log,'overfull horizontal boxes in PDF:\n'+log)
        require('Overfull \\vbox' not in log,'overfull vertical boxes in PDF')
        require('There were undefined references' not in log,'undefined TeX references')
        (ROOT/'Report206.pdf').write_bytes(pdf)
    manifest={'report':'Report206','source_date_epoch':int(EPOCH),
              'files':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sorted(PUBLIC)}}
    dump('MANIFEST.json',manifest)
    with zipfile.ZipFile(ROOT/'Report206.zip','w',compression=zipfile.ZIP_STORED) as archive:
        for name in sorted(PUBLIC+['MANIFEST.json']):
            info=zipfile.ZipInfo(name,date_time=(2026,10,4,0,0,0))
            info.create_system=3
            info.external_attr=0o100644<<16
            info.compress_type=zipfile.ZIP_STORED
            archive.writestr(info,(ROOT/name).read_bytes())
    print(json.dumps({'status':'PASS','zip_sha256':hashlib.sha256((ROOT/'Report206.zip').read_bytes()).hexdigest(),
                      'file_count':len(PUBLIC)+1},indent=2,sort_keys=True))

if __name__=='__main__':
    main()
