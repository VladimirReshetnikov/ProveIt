"""Generate the complete, compact printed definition from frozen JSON data."""
from pathlib import Path
import json,hashlib,collections

WORK=Path(__file__).resolve().parents[1]
OUT=WORK/'report'
S=json.loads((WORK/'source/anchor219.json').read_text())
P=json.loads((WORK/'equations/integer85_degree16964.json').read_text())
def v(i):return rf'v_{{{i}}}'
def token(coeff,mon,first=False):
    count=collections.Counter(mon)
    body=''.join(v(i)+(rf'^{{{n}}}' if n>1 else '') for i,n in sorted(count.items()))
    mag=abs(coeff)
    if not body or mag!=1:body=str(mag)+body
    sign='-' if coeff<0 else ('' if first else '+')
    return sign+body
def term_width(coeff,mon):
    return (len(str(abs(coeff))) if abs(coeff)!=1 or not mon else 0)+sum(3.8+len(str(i))*.45+(1 if mon.count(i)>1 else 0) for i in set(mon))+1

def emit():
    OUT.mkdir(parents=True,exist_ok=True)
    profiles=[]
    for f in (WORK/'equations').glob('integer*.json'):
        q=json.loads(f.read_text());profiles.append(q['metrics'])
    profiles.sort(key=lambda m:m['variables'])
    lines=[r'\begin{table}[htbp]',r'\centering',r'\caption{Delivered integer-polynomial tradeoffs. All coordinates range over $\Z$.}',r'\label{tab:metrics}',r'\small',r'\begin{tabular}{rrrrr}',r'\toprule',r'Variables & Exact degree & Residuals & Operations & $H$\\',r'\midrule']
    for m in profiles:
        values=[m['variables'],m['degree'],m['residuals'],m['live_binary_operations'],m['coefficient_height_bound_exponent']]
        st=['{:,}'.format(x).replace(',',r'\,') for x in values]
        if m['variables']==85:st=[r'\textbf{'+x+'}' for x in st]
        lines.append(' & '.join(st)+r'\\')
    lines +=[r'\bottomrule',r'\end{tabular}',r'\end{table}']
    (OUT/'metrics_table.tex').write_text('\n'.join(lines)+'\n')
    free=P['retained_source_indices'];lines=[r'\[',r'\begin{gathered}']
    for off in range(0,len(free),14):
        lines.append(','.join(map(str,free[off:off+14]))+(r',\\' if off+14<len(free) else '.'))
    lines +=[r'\end{gathered}',r'\]']
    (OUT/'free_indices.tex').write_text('\n'.join(lines)+'\n')

    triples=[]
    for definition in P['definitions']:
        i,j=definition['variable'],definition['source_row']
        eps=next(cc for cc,mon in S['residuals'][j]['terms'] if mon==[i])
        triples.append((i,j,eps))
    if len(triples)!=124:raise ValueError('Wrong pivot count')
    # Entries are across each row; reading left-to-right and then down is
    # the original dependencies-first reconstruction sequence.
    lines=[r'\begin{longtable}{rrrr@{\qquad}rrrr}',r'\caption{Reconstruction instructions, read left-to-right and then down.}\label{tab:pivots}\\',r'\toprule',r'Step & $v$ & Row $j$ & $\epsilon$ & Step & $v$ & Row $j$ & $\epsilon$\\',r'\midrule\endfirsthead',r'\toprule',r'Step & $v$ & Row $j$ & $\epsilon$ & Step & $v$ & Row $j$ & $\epsilon$\\',r'\midrule\endhead',r'\bottomrule\endfoot']
    for j in range(0,len(triples),2):
        line=[]
        for kk in [j,j+1]:
            if kk>=len(triples):line.extend(['']*4)
            else:
                vv,rr,ee=triples[kk];line.extend([str(kk+1),str(vv),str(rr),str(ee)])
        lines.append(' & '.join(line)+r'\\')
    lines.append(r'\end{longtable}')
    (OUT/'pivot_table.tex').write_text('\n'.join(lines)+'\n')

    req=[(0,'v_2','2^{20}v_0','v_{186}','v_{187}','v_{188}'),
         (1,'v_{17}','v_1','v_{177}','v_{178}','v_{179}+1'),
         (2,'v_{100}-1','v_1','v_{177}','v_{178}','v_{179}+1'),
         (4,'v_{101}','v_0+v_2','v_{150}','v_{151}','v_{152}'),
         (3,'v_{102}','v_0','v_{141}','v_{142}','v_{143}'),
         (4,'v_{106}','v_8-1','v_{153}','v_{154}-1','v_{155}'),
         (4,'v_{109}','v_9','v_{156}','v_{157}','v_{158}'),
         (4,'v_{112}','v_{10}','v_{159}','v_{160}','v_{161}'),
         (4,'v_{115}','v_{11}','v_{162}','v_{163}','v_{164}'),
         (4,'v_{118}','v_{12}','v_{165}','v_{166}','v_{167}'),
         (4,'v_{122}','v_{13}','v_{171}','v_{172}','v_{173}'),
         (4,'v_{125}','v_{14}','v_{174}','v_{175}','v_{176}'),
         (4,'v_{130}','v_{15}','v_{180}','v_{181}','v_{182}'),
         (3,'v_{119}','v_4','v_{168}','v_{169}','v_{170}'),
         (3,'v_{126}','v_1','v_{177}','v_{178}','v_{179}+1'),
         (4,'v_{133}','2v_{16}','v_{183}','v_{184}','v_{185}')]
    lines=[r'\begin{table}[htbp]',r'\centering',r'\caption{The sixteen literal power requests. The base in group $j$ is $n_j$.}',r'\label{tab:requests}',r'\begin{tabular}{rrrrrrr}',r'\toprule',r'$i$ & Group $j$ & $m_i$ & $k_i$ & $D_i$ & $Y_i$ & $Z_i$\\',r'\midrule']
    for i,row in enumerate(req):lines.append(str(i)+' & '+str(row[0])+' & '+' & '.join('$'+s+'$' for s in row[1:])+r'\\')
    lines.extend([r'\bottomrule',r'\end{tabular}',r'\end{table}'])
    (OUT/'requests_table.tex').write_text('\n'.join(lines)+'\n')

    deleted=set(P['source_removed_rows']);lines=[r'\begingroup',r'\small',r'\allowdisplaybreaks[4]',r'\setlength{\jot}{3.8pt}',r'\begin{align*}']
    count=0
    for j,row in enumerate(S['residuals']):
        if j in deleted:continue
        count+=1;chunks=[];chunk=[];width=0
        for ci,(cc,mon) in enumerate(row['terms']):
            tw=term_width(cc,mon)
            if width+tw>73 and chunk:chunks.append(chunk);chunk=[];width=0
            chunk.append(token(cc,mon,first=(ci==0)));width+=tw
        if chunk:chunks.append(chunk)
        for ci,part in enumerate(chunks):
            line=(rf'R_{{{j}}}&=' if ci==0 else r'&\quad')+''.join(part)
            lines.append(line+r'\\' + (r'[2pt]' if ci==len(chunks)-1 else r'*'))
    if count!=147:raise ValueError('wrong source row count')
    lines.extend([r'\end{align*}',r'\endgroup'])
    (OUT/'source_rows.tex').write_text('\n'.join(lines)+'\n')
    ledger={'principal_sha256':hashlib.sha256((WORK/'equations/integer85_degree16964.json').read_bytes()).hexdigest(),
      'source_sha256':hashlib.sha256((WORK/'source/anchor219.json').read_bytes()).hexdigest(),
      'free_variables':85,'pivots':124,'source_rows':147,
      'generated':{name:hashlib.sha256((OUT/name).read_bytes()).hexdigest() for name in ['metrics_table.tex','free_indices.tex','pivot_table.tex','requests_table.tex','source_rows.tex']}}
    (OUT/'PRINTED_DEFINITION.json').write_text(json.dumps(ledger,sort_keys=True,indent=2)+'\n')
    print(json.dumps(ledger))
if __name__=='__main__':emit()
