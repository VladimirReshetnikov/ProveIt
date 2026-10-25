#!/usr/bin/env python3
"""Rebuild literal report tables and the explicit unrestricted-integer lift."""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,hashlib,json

HERE=Path(__file__).resolve().parent

def jread(p):return json.loads(p.read_text())
def write(p,obj):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(obj,separators=(',',':'),sort_keys=True)+'\n')

def term_tex(c,indices,first=False):
    count=Counter(indices)
    mon=''.join('z_{%s}'%i+('^{%s}'%e if e>1 else '') for i,e in sorted(count.items()))
    mag=abs(c)
    val=(str(mag) if mag!=1 or not mon else '')+mon
    return ('-' if c<0 else ('' if first else '+'))+val

def report_texts(eq,dense):
    def macros(prefix,d):
        m=d['metrics']
        return {prefix+'Vars':len(d['variables']),prefix+'Rows':len(d['residuals']),
                prefix+'Terms':m['expanded_monomials'],prefix+'Height':m['max_abs_expanded_coefficient']}
    nums={**macros('Main',eq),**macros('Dense',dense)}
    nums.update(MainLast=nums['MainVars']-1,MainRowLast=nums['MainRows']-1,IntegerVars=4*nums['MainVars'])
    metric='\n'.join('\\newcommand{\\%s}{%s}'%(k,format(v,',') if k.endswith(('Terms','Height')) else v) for k,v in nums.items())+'\n'
    lines=[r'\begingroup\footnotesize',r'\setlength{\tabcolsep}{3pt}',
           r'\begin{longtable}{@{}r p{0.88\linewidth}@{}}',
           r'\toprule Residual & Integer polynomial (continued across rows when necessary)\\\midrule\endhead']
    for j,row in enumerate(eq['residuals']):
        ts=[term_tex(c,ids,i==0) for i,(c,ids) in enumerate(row['terms'])]
        # Six monomials per continuation keep long pooled rows compact and readable.
        for i in range(0,len(ts),6):
            label=('$Q_{%d}=$'%j) if i==0 else ''
            text=r'\,'.join(ts[i:i+6])
            lines.append(label+' & $'+text+r'$\\'+('[5pt]' if i+6>=len(ts) else ''))
    lines.extend([r'\bottomrule\end{longtable}',r'\endgroup'])
    residual='\n'.join(lines)+'\n'
    lines=[r'\begingroup\footnotesize',r'\begin{longtable}{@{}r p{0.40\linewidth}r p{0.40\linewidth}@{}}',
           r'\toprule Index & Name & Index & Name\\\midrule\endhead']
    n=len(eq['variables']);half=(n+1)//2
    for j in range(half):
        left=f'{j} & \\pathfile{{{eq["variables"][j]["name"]}}}'
        k=j+half
        right=f'{k} & \\pathfile{{{eq["variables"][k]["name"]}}}' if k<n else ' & '
        lines.append(left+' & '+right+r'\\')
    lines.extend([r'\bottomrule\end{longtable}',r'\endgroup'])
    return {'metrics.tex':metric,'residuals.tex':residual,'variables.tex':'\n'.join(lines)+'\n'}

def integer_lift(eq,poly):
    n=len(eq['variables']);vars=[{'kind':'original_integer','name':v['name']} for v in eq['variables']]
    rows=list(eq['residuals'])
    acc={tuple(ids):c for c,ids in poly['terms']}
    for i in range(n):
        ids=[n+3*i+j for j in range(3)]
        vars.extend({'kind':'three_square_guard','name':f'guard{i}.{s}'} for s in 'abc')
        terms=[[1,[]],[8,[i]]]+[[-1,[j,j]] for j in ids]
        rows.append({'label':f'integer_domain_guard_{i}','terms':terms})
        for c,a in terms:
            for d,b in terms:
                m=tuple(sorted(a+b));acc[m]=acc.get(m,0)+c*d
    collected=[[v,list(k)] for k,v in sorted(acc.items()) if v]
    metrics={'variables':len(vars),'quadratic_rows':len(rows),'exact_degree':max(map(lambda t:len(t[1]),collected)),
             'expanded_monomials':len(collected),'max_abs_expanded_coefficient':max(abs(t[0]) for t in collected)}
    result={'schema':'sum-of-squares-quartic-v1','domain':'unrestricted integers','variables':vars,
            'residuals':rows,'metrics':metrics,'polynomial':'sum of every listed residual squared',
            'source':'principal241 plus 8*z+1=a^2+b^2+c^2 for every coordinate',
            'scope':'mechanical domain conversion, not an integer-variable frontier claim'}
    return result,{'schema':'sparse-integer-polynomial-v1','domain':'unrestricted integers','variables':len(vars),'terms':collected}

def main(check=False):
    eq=jread(HERE/'direct/equations/principal241/natural/equation.json')
    dense=jread(HERE/'direct/equations/dense239/natural/equation.json')
    poly=jread(HERE/'direct/equations/principal241/natural/expanded_polynomial.json')
    texts=report_texts(eq,dense)
    for name,text in texts.items():
        dest=HERE/'report'/name
        if check:
            if dest.read_text()!=text:raise ValueError('report mismatch: '+name)
        else:dest.write_text(text)
    lift,expanded=integer_lift(eq,poly)
    for name,data in [('equation.json',lift),('expanded_polynomial.json',expanded)]:
        dest=HERE/'integer964'/name
        if check:
            if jread(dest)!=data:raise ValueError('integer lift mismatch '+name)
        else:write(dest,data)
    result={'status':'PASS','report_tables':len(texts),'main_equation_sha256':hashlib.sha256((HERE/'direct/equations/principal241/natural/equation.json').read_bytes()).hexdigest(),
            'principal':eq['metrics'],'dense':dense['metrics'],'integer_lift':lift['metrics']}
    if not check:write(HERE/'REPORT_BINDING.json',result)
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args();main(args.check)
