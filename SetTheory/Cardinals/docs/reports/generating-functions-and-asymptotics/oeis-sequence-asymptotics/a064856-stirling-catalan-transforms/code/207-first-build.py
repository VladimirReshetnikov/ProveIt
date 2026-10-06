#!/usr/bin/env python3
"""Deterministic complete public build of Report207, including under python -O."""
from decimal import Decimal
from pathlib import Path
import ast
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import zipfile
ROOT=Path(__file__).resolve().parent
EPOCH='1791072000'
PUBLIC=['Report207.tex','Report207.pdf','README.txt','requirements.txt','build.py',
        'verify_exact.py','diagnostics.py','supplementary.py','exact_results.json',
        'diagnostics.json','supplementary.json','tables.tex','table_cells.json','checks.json']
def require(ok,message):
    if not ok:raise RuntimeError(message)
def dump(name,obj):
    (ROOT/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n',encoding='utf-8')
def execute(script):
    flags=['-O'] if sys.flags.optimize else []
    p=subprocess.run([sys.executable,*flags,str(ROOT/script)],cwd=ROOT,text=True,capture_output=True)
    require(p.returncode==0,f'{script} failed:\n'+p.stderr)
    require(not p.stderr.strip(),f'{script} wrote unexpected stderr:\n'+p.stderr)
    return json.loads(p.stdout)
def negative_guards():
    # Extract only each actual guard definition with AST; no numerical work is
    # skipped in the real build. Isolated false calls must fail in BOTH modes.
    count=0
    for name in ['verify_exact.py','supplementary.py','build.py']:
        tree=ast.parse((ROOT/name).read_text())
        fun=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='require')
        prelude='checks=0\n' if name=='verify_exact.py' else 'checks=[]\n'
        src=prelude+ast.unparse(fun)+"\nrequire(False,'EXPECTED_GUARD_FAILURE')\n"
        for opt in [False,True]:
            p=subprocess.run([sys.executable,*(['-O'] if opt else []),'-c',src],text=True,capture_output=True)
            require(p.returncode!=0 and 'EXPECTED_GUARD_FAILURE' in p.stderr,
                    f'negative guard removed: {name}, optimized={opt}')
            count+=1
    return count

def render(value,style):
    d=Decimal(str(value))
    if style=='int':return str(int(d))
    if style=='fixed':return f'{d:.6f}'
    if not d:return '$0$'
    m,e=f'{d:.5E}'.split('E')
    return '$'+m+r'\times10^{'+str(int(e))+'}$'
def resolve(data,path):
    for key in path:data=data[key]
    return data

def tables(data):
    lines=[];ledger=[]
    def cell(file,path,style='sci'):
        value=resolve(data[file],path);s=render(value,style)
        ledger.append({'file':file,'path':path,'value':value,'format':style,'rendered':s})
        return s
    def start(title,caption,headers,label):
        lines.extend([r'\Needspace{'+('24' if label=='tab:terms' else '17')+r'\baselineskip}',r'\subsection{'+title+'}',r'\begin{longtable}{'+'r'*len(headers)+'}',
                      r'\caption{'+caption+r'}\label{'+label+r'}\\',r'\toprule '+' & '.join(headers)+r' \\ \midrule',
                      r'\endfirsthead',r'\toprule '+' & '.join(headers)+r' \\ \midrule',r'\endhead',r'\bottomrule\endfoot'])
    def row(cells):lines.append(' & '.join(cells)+r' \\')
    def end():lines.append(r'\end{longtable}')
    E='exact_results.json';D='diagnostics.json';S='supplementary.json'
    start('Exact initial terms','The 24 reference terms, reproduced by integer arithmetic.',['$n$','$a_n$','$n$','$a_n$'],'tab:terms')
    for n in range(12):
        # Index columns refer to explicit generated enumeration, stored in the ledger too.
        row([cell(E,['reference_indices',n],'int'),cell(E,['terms_through_80',n],'int'),cell(E,['reference_indices',n+12],'int'),cell(E,['terms_through_80',n+12],'int')])
    end()
    start('Resummed scalar errors',r'Noncertified relative errors $G_J(n)/a_n-1$. The comparison uses the scaled exact integral.',['$n$','$J=0$','$J=1$','$J=2$'],'tab:resummed')
    for i in range(len(data[D]['counts'])):row([cell(D,['counts',i,'n'],'int')]+[cell(D,['counts',i,'resummed_relative_errors',j]) for j in range(3)])
    end()
    start('Divergent coefficients and exact completion',r'Large-order ratios $c_k/[-(24/\pi)4^{-k}\Gamma(k)]$. Finite values need not approach the limit monotonically.',['$k$','Ratio'],'tab:large')
    for i in range(len(data[D]['large_order'])):row([cell(D,['large_order',i,'k'],'int'),cell(D,['large_order',i,'c_over_large_order_equivalent'],'fixed')])
    end()
    start('Convergent completion errors',r'Noncertified relative error of the first $q$ incomplete-gamma terms for $F_0(L)$.',['$L$','$q=11$','$q=31$','$q=81$','$q=161$'],'tab:completion')
    for i in range(len(data[D]['completion'])):row([cell(D,['completion',i,'L'],'int')]+[cell(D,['completion',i,'truncations',j,'relative_error']) for j in range(4)])
    end()
    start('Explicit inverse errors',r'For targets $X=a_n$, noncertified real-index errors of the fixed-log formulas.',['$n$','$v_0-n$','$v_1-n$'],'tab:inverse')
    for i in range(len(data[D]['inverse'])):row([cell(D,['inverse',i,'n'],'int')]+[cell(D,['inverse',i,k]) for k in ['v0_minus_n','v1_minus_n']])
    end()
    start('Finite Newton diagnostics',r'For targets $X=a_n$, three Newton iterations for $G_J$; the final error is against the true real index $n$.',['$n$','$J$','$s_3-n$',r'$n^{J+1}L(s_3-n)$'],'tab:newton')
    for i in range(len(data[S]['inversion'])):row([cell(S,['inversion',i,'n'],'int'),cell(S,['inversion',i,'J'],'int'),cell(S,['inversion',i,'s3_minus_n']),cell(S,['inversion',i,'scaled_inverse_error'],'fixed')])
    end()
    start('Ewens comparison',r'Noncertified total variation from a 220-cycle truncated floating recurrence. The limiting scaled constant is $3\sqrt{2/\pi}/8\approx0.299207$.',['$n$',r'$d_{\rm TV}$',r'$\sqrt L\,d_{\rm TV}$','Mass residual'],'tab:tv')
    for i in range(len(data[D]['total_variation'])):row([cell(D,['total_variation',i,'n'],'int')]+[cell(D,['total_variation',i,k],'fixed' if k!='probability_mass_residual' else 'sci') for k in ['tv','sqrt_log_n_times_tv','probability_mass_residual']])
    end()
    start('Boundary density diagnostics',r'Noncertified $L^1$ errors of the leading Gamma density and its first correction; normalized mass is checked separately.',['$n$','Leading error','Corrected error',r'$L^2$ corrected'],'tab:boundary')
    for i in range(len(data[S]['boundary'])):row([cell(S,['boundary',i,'n'],'int')]+[cell(S,['boundary',i,k],'fixed') for k in ['leading_L1_error','corrected_L1_error','scaled_corrected_L1_error']])
    end()
    result='\n'.join(lines)+'\n'
    for rec in ledger:
        require(resolve(data[rec['file']],rec['path'])==rec['value'],'table source mismatch')
        require(render(rec['value'],rec['format'])==rec['rendered'],'table formatting mismatch')
        require(rec['rendered'] in result,'rendered table cell missing')
    return result,ledger

def compile_pdf():
    env=dict(os.environ,SOURCE_DATE_EPOCH=EPOCH,FORCE_SOURCE_DATE='1',TZ='UTC',LC_ALL='C')
    with tempfile.TemporaryDirectory(prefix='report207-tex-') as tmp:
        work=Path(tmp)
        for name in ['Report207.tex','tables.tex']:shutil.copyfile(ROOT/name,work/name)
        def tex_run(command):
            result=subprocess.run(command,cwd=work,env=env,text=True,capture_output=True)
            require(result.returncode==0,'TeX command failed:\n'+result.stdout+result.stderr)
            return result.stdout.strip()
        probe=subprocess.run(['kpsewhich','pdflatex.fmt'],cwd=work,env=env,text=True,capture_output=True)
        if probe.returncode or not probe.stdout.strip():
            dist=Path(tex_run(['kpsewhich','-var-value=TEXMFDIST']))
            require(dist.is_dir(),'installed TeX tree is missing')
            trees=[dist];sibling=dist.parent.parent/'texmf'
            if sibling.is_dir():trees.append(sibling)
            env['TEXMF']='{'+','.join(map(str,trees))+'}'
            env['TEXFORMATS']=str(work)+os.pathsep
            tex_run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','pdflatex.ini'])
            require((work/'pdflatex.fmt').is_file(),'private TeX format was not created')
            maps=[]
            for name in ['cm.map','cmextra.map','latxfont.map','symbols.map','lm.map']:
                path=Path(tex_run(['kpsewhich',name]));require(path.is_file(),'missing font map: '+name);maps.append(path.read_bytes())
            (work/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
        previous=None;stable=False
        for i in range(5):
            tex_run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error','Report207.tex'])
            pdf=(work/'Report207.pdf').read_bytes()
            if i>=2 and pdf==previous:stable=True;break
            previous=pdf
        require(stable,'PDF did not reach byte stability')
        log=(work/'Report207.log').read_text(errors='replace')
        require('Overfull \\hbox' not in log,'overfull horizontal boxes:\n'+log)
        require('Overfull \\vbox' not in log,'overfull vertical boxes')
        require('There were undefined references' not in log,'undefined references')
        (ROOT/'Report207.pdf').write_bytes(pdf)

def main():
    require(sys.version_info>=(3,10),'Python >=3.10 required')
    exact=execute('verify_exact.py')
    require(exact['status']=='PASS' and exact['checks']==1253,'exact checks failed')
    exact['reference_indices']=list(range(24));dump('exact_results.json',exact)
    diagnostic=execute('diagnostics.py');dump('diagnostics.json',diagnostic)
    supp=execute('supplementary.py');require(supp['status']=='PASS','supplementary checks failed');dump('supplementary.json',supp)
    for row in diagnostic['counts']:
        require(all(Decimal(v).is_finite() for v in row['resummed_relative_errors']),'nonfinite scalar diagnostic')
    data={'exact_results.json':exact,'diagnostics.json':diagnostic,'supplementary.json':supp}
    tex,cells=tables(data);(ROOT/'tables.tex').write_text(tex,encoding='utf-8');dump('table_cells.json',cells)
    guard_count=negative_guards()
    dump('checks.json',{'status':'PASS','exact_checks':exact['checks'],'supplementary_checks':len(supp['checks']),
        'table_numeric_cells':len(cells),'negative_guard_cases':guard_count,'both_guard_modes':True,
        'scope':'Finite identity checks and noncertified numerical illustrations; no onset or asymptotic error certification.'})
    compile_pdf()
    dump('MANIFEST.json',{'report':'Report207','source_date_epoch':int(EPOCH),'files':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sorted(PUBLIC)}})
    with zipfile.ZipFile(ROOT/'Report207.zip','w',compression=zipfile.ZIP_STORED) as archive:
        for name in sorted(PUBLIC+['MANIFEST.json']):
            info=zipfile.ZipInfo(name,date_time=(2026,10,4,0,0,0));info.create_system=3
            info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_STORED
            archive.writestr(info,(ROOT/name).read_bytes())
    print(json.dumps({'status':'PASS','zip_sha256':hashlib.sha256((ROOT/'Report207.zip').read_bytes()).hexdigest(),'file_count':len(PUBLIC)+1,'table_cells':len(cells)},indent=2,sort_keys=True))
if __name__=='__main__':main()
