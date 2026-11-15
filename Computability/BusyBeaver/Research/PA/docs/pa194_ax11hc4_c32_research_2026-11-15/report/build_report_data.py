from pathlib import Path
import csv,hashlib,json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def tex(s):
    return ''.join({'&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}','\\':r'\textbackslash{}'}.get(c,c) for c in str(s))
def write(name,s): (HERE/name).write_text(s+'\n')

main=json.loads((ROOT/'construction/ax11hc4/receipts/purejs.json').read_text())
comp=json.loads((ROOT/'construction/receipts/js_startup.json').read_text())
rebuild=json.loads((ROOT/'construction/receipts/js_reconstruction.json').read_text())

tables=[('PA194AX11HC4',ROOT/'construction/ax11hc4/machine/pa194_ax11hc4.tm','table_ax11hc4.tex'),('PA194C32',ROOT/'construction/cycle32/pa194_cycle32.tm','table_c32.tex')]
hash_lines=[r'\subsection{Exact dense-table identities}']
for name,path,out in tables:
    data=path.read_bytes();digest=hashlib.sha256(data).hexdigest()
    hash_lines += [r'\textbf{'+name+r'}\par',r'{\small\ttfamily '+digest[:32]+r'\allowbreak '+digest[32:]+r'}\par']
    rows={}
    for line in data.decode().splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=f'{w}{d}{n}'
    assert len(rows)==388 and {q for q,b in rows}==set(range(194))
    body=[r'\begingroup\small\ttfamily\renewcommand{\arraystretch}{0.96}',r'\begin{longtable}{rll@{\hspace{1.2cm}}rll}',r'\toprule',r'$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 \\',r'\midrule\endfirsthead',r'\toprule',r'$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 \\',r'\midrule\endhead',r'\bottomrule\endfoot']
    for q in range(97):
        p=q+97;body.append(f'{q}&{rows[q,0]}&{rows[q,1]}&{p}&{rows[p,0]}&{rows[p,1]}'+r'\\')
    body.extend([r'\end{longtable}',r'\endgroup']);write(out,'\n'.join(body))
write('hashes.tex','\n'.join(hash_lines))

def parse(p):
    d={}
    for l in p.read_text().splitlines():
        q,b,w,m,n=l.split();d[int(q),int(b)]=(int(w),m,int(n))
    return d
for suffix,parent,new,receipt in [
 ('ax11hc4',ROOT/'construction/ax11hc4/reference/parent.native.tm',ROOT/'construction/ax11hc4/machine/pa194_ax11hc4.native.tm',main['startup']),
 ('c32',ROOT/'construction/pa194.native.tm',ROOT/'construction/cycle32/pa194_cycle32.native.tm',comp.get('candidate',comp.get('candidate_startup',{})) )]:
    a,b=parse(parent),parse(new)
    changed=[q for q in sorted(a) if a[q]!=b[q]]
    body=[r'\begin{center}\small',r'\begin{tabular}{rrll}',r'\toprule',r'Native state & Read & Parent action & New action\\',r'\midrule']
    for q,bit in changed:
        def act(x):return f'{x[0]}{x[1]}{x[2]}'
        body.append(f'{q}&{bit}&'+r'\texttt{'+act(a[q,bit])+r'}&\texttt{'+act(b[q,bit])+r'}\\')
    body.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}']);write('edits_'+suffix+'.tex','\n'.join(body))

with (ROOT/'comparison/family_comparison33.csv').open(newline='') as f: families=list(csv.DictReader(f))
body=[r'\begingroup\small',r'\begin{longtable}{p{0.25in}>{\raggedright\arraybackslash}p{1.55in}>{\raggedright\arraybackslash}p{2.10in}>{\raggedright\arraybackslash}p{2.00in}}',r'\toprule',r'\# & Mechanism / examples & Change & Main proof obligation\\',r'\midrule\endfirsthead',r'\toprule',r'\# & Mechanism / examples & Change & Main proof obligation\\',r'\midrule\endhead',r'\bottomrule\endfoot']
for f in families:
    body.append(tex(f['family_id'])+'&'+tex(f['family'])+r'\par '+tex(f['designs'])+'&'+tex(f['recurring_behavior'])+'&'+tex(f['proof_obligation'])+r'\\[0.5em]')
body.extend([r'\end{longtable}',r'\endgroup']);write('families.tex','\n'.join(body))

incoming=[
 ('AX11GDH','AX11GDH, AX11GDHS, AX11GDHF, AX11GDHR','Eleven-entry interface, independent binder and diagonal; symmetric, accelerated and helper-return realizations.'),
 ('Comparison / SF','AX11H\u005fSF, LC\u005fAX11H\u005fSF','Compatible history selectors with guarded physical acceleration.'),
 ('GD','GD, GDH, GDHS','Ten-entry independent-binder / diagonal protocol with different contradiction detectors.'),
 ('LCfast','LCAX11GHF, LCAX11GHSF','Continuation reassociation and two physical shortcuts.'),
 ('Loop return','LCG, LCGS','Continuation reassociation with a third guarded return shortcut.'),
 ('Witness','H5X, JH5X','Uniformly interderivable axiom-head changes, including a free consequent.')]
body=[r'\begin{center}\small',r'\begin{longtable}{>{\raggedright\arraybackslash}p{1.0in}>{\raggedright\arraybackslash}p{2.35in}>{\raggedright\arraybackslash}p{2.85in}}',r'\toprule',r'Incoming packet & New named realizations (PA194 prefix) & Distinguishing mechanism\\',r'\midrule\endfirsthead',r'\toprule',r'Incoming packet & New named realizations (PA194 prefix) & Distinguishing mechanism\\',r'\midrule\endhead',r'\bottomrule\endfoot']
for row in incoming:body.append('&'.join(map(tex,row))+r'\\[0.5em]')
body.extend([r'\end{longtable}',r'\end{center}']);write('incoming.tex','\n'.join(body))

results=[json.loads((ROOT/f'research/startup193/result_append{bit}.json').read_text()) for bit in [0,1]]
assert sum(r['simulations'] for r in results)==22575210
assert sum(r['transitions'] for r in results)==4167291032
body=[r'\begin{table}[ht]\centering\small',r'\begin{tabular}{lrr}',r'\toprule',r'Outcome & Append 0 & Append 1\\',r'\midrule']
for label,key in [('Edit pairs','pairs'),('Blank starts','simulations'),('Literal transitions','transitions'),('Halts','halts'),('Certified outward rays','outward_rays'),('Bounded, unresolved','bounded'),('Complete source-frame hits','frame_hits')]:
    body.append(label+'&'+'&'.join(format(r[key],',') for r in results)+r'\\')
body.extend([r'\bottomrule',r'\end{tabular}',r'\caption{The completed new two-edit bootstrap screen. No acceptance is inferred from a runtime-only certificate.}',r'\end{table}']);write('search_results.tex','\n'.join(body))
print('Generated exact report tables and data includes.')
