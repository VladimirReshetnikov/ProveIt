"""Render the report's tables from recorded measurements, then compile its LaTeX.

Requires pdflatex on PATH; the algorithm and tests themselves do not need TeX.
The generated report.tex is standalone (no external table inputs).
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def tex(s):
    return str(s).replace('\\', r'\textbackslash{}').replace('_', r'\_').replace('&',r'\&')


def seconds(x):
    return f'{x:.4f}' if x < 1 else f'{x:.3f}'


def main():
    data = json.loads((ROOT/'results/benchmark.json').read_text())
    hardcheck = json.loads((ROOT/'results/hard-case-verification.json').read_text())
    cases = data['cases']
    hard = next(x for x in cases if x['id']=='scan-23')
    kh = hard['optimized']['answer']
    testlog = (ROOT/'results/test-output.txt').read_text()
    count = int(re.search(r'Ran (\d+) tests', testlog)[1])
    assert testlog.rstrip().endswith('OK')
    macros = {'HardTime': f"{hard['optimized']['median_seconds']:.2f}",
              'TimeLimit': f"{data['limit_seconds']:g}", 'TestCount': str(count),
              'HardRank': str(kh['reduced_rank']), 'HardUnreduced':str(kh['rank']),
              'HardPeakObjects':str(kh['stats']['max_objects_before_elimination']),
              'HardWidth':str(kh['stats']['max_boundary']),
              'PythonVersion':'Python '+data['python'].split()[0],
              'HostPlatform':data['platform'], 'CpuModel':data['cpu_model']}
    metrics = '\n'.join('\\newcommand{\\'+name+'}{'+tex(value)+'}' for name,value in macros.items())
    scan = [r'\small',r'\begin{longtable}{@{}lrrrrr@{}}',r'\toprule',
            r'Input family & $n$ & Reduced rank & Old (s) & New (s) & Speedup\\',r'\midrule',
            r'\endfirsthead',r'\toprule',
            r'Input family & $n$ & Reduced rank & Old (s) & New (s) & Speedup\\',
            r'\midrule',r'\endhead',r'\bottomrule\endfoot']
    for r in cases:
        if r['method']!='scan': continue
        label = r['label'].split(',')[0]
        label = label.replace('unknot sigma_1..sigma_n','Stabilized unknot')
        # Labels containing commas (torus families) are supplied separately.
        if r['label'].startswith('T(2,'): label = '$T(2,k)$'
        elif r['label'].startswith('T(3,'): label = '$T(3,k)$'
        else: label = tex(label)
        b,a = r['baseline'],r['optimized']
        old = seconds(b['median_seconds']) if b['status']=='ok' else '$>'+str(int(data['limit_seconds']))+'$'
        ratio = f"{r['speedup']:.2f}" if 'speedup' in r else '$>'+f"{r['speedup_lower_bound']:.2f}"+'$'
        scan.append(f"{label} & {r['crossings']} & {a['answer']['reduced_rank']} & "
                    f"{old} & {seconds(a['median_seconds'])} & {ratio}\\\\")
    scan += [r'\end{longtable}',r'\normalsize']
    pipeline = [r'\begin{center}\small',r'\begin{tabular}{@{}lrrrl@{}}',r'\toprule',
                r'Example & Old (ms) & New (ms) & Speedup & New decisive stage\\',r'\midrule']
    stages = {'modular-jones':'Bracket','modular-determinant':'Determinant',
              'reidemeister-reduction':'R1/R2', 'reduced-khovanov-F2-scan':'Khovanov'}
    labels = {'conway':'Conway','figure_eight':'Figure eight',
              'grid_determinant_one_knot':'Determinant-one grid',
              'grid_scrambled_unknot':'Scrambled grid unknot','hard_unknot_8':'Hard unknot (8)',
              'kinoshita_terasaka':'Kinoshita--Terasaka','torus_3_5':'$T(3,5)$',
              'trefoil':'Trefoil','unknot':'Unknot example','unknot_braid40':'Unknot braid (40)'}
    for r in cases:
        if r['method']!='pipeline':continue
        pipeline.append(f"{labels[r['label']]} & {r['baseline']['median_seconds']*1000:.3f} & "
                        f"{r['optimized']['median_seconds']*1000:.3f} & {r['speedup']:.2f} & "
                        f"{stages[r['optimized']['answer']['method']]}\\\\")
    pipeline += [r'\bottomrule\end{tabular}\end{center}']
    scaling = [r'\begin{center}\small',r'\begin{tabular}{@{}lrrrr@{}}',r'\toprule',
               r'Subroutine & $n$ & Old (s) & New (s) & Speedup\\',r'\midrule']
    for r in cases:
        if r['method'] not in ('order','simplify'):continue
        scaling.append(f"{'Scan ordering' if r['method']=='order' else 'R1/R2 cleanup'} & "
                       f"{r['crossings']} & {seconds(r['baseline']['median_seconds'])} & "
                       f"{seconds(r['optimized']['median_seconds'])} & {r['speedup']:.1f}\\\\")
    scaling += [r'\bottomrule\end{tabular}\end{center}']
    verified = hardcheck['orders']
    assert len(verified)==2 and all(r['status']=='ok' for r in verified)
    paragraph = (r'The automatic greedy order and the natural input order both give reduced '
                 r'rank $2949$ and identical unreduced ranks in every cube degree, with '
                 r'intermediate $d^2=0$ checks. The respective elapsed times in these '
                 f"debug runs are {verified[0]['median_seconds']:.2f} and "
                 f"{verified[1]['median_seconds']:.2f} seconds. "
                 r'Two exploratory alternative-order checks (reverse natural order and a '
                 r'greedy order starting at crossing $35$) did not finish within the external '
                 r'run limits. No agreement is claimed for them. This illustrates important '
                 r'order sensitivity; these debug runs are not the three-repetition benchmark. '
                 r'The completed outputs are in \code{results/hard-case-verification.json}; '
                 r'the unsuccessful attempts are described in '
                 r'\code{results/additional-order-notes.txt}.')
    replacements = {'METRICS':metrics, 'HARDVERIFICATION':paragraph, 'SCAN_TABLE':'\n'.join(scan),
                    'PIPELINE_TABLE':'\n'.join(pipeline), 'SCALING_TABLE':'\n'.join(scaling)}
    source = (ROOT/'docs/report.template.tex').read_text()
    for name,value in replacements.items():source = source.replace('%%'+name+'%%',value)
    (ROOT/'docs/report.tex').write_text(source)
    for _ in range(3):
        result = subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','report.tex'],
                                cwd=ROOT/'docs',capture_output=True,text=True)
        if result.returncode:
            print(result.stdout[-6000:])
            raise SystemExit(result.returncode)
    print('Built docs/report.pdf and standalone docs/report.tex')

if __name__ == '__main__':
    main()
