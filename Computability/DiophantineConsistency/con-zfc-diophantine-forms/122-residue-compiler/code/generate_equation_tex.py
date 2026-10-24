#!/usr/bin/env python3
"""Typeset both complete residual quartics; Python standard library only.

From anywhere:
    python3 code/generate_equation_tex.py

The default package root is this script's parent directory.  The inputs
are equations/natural332/natural/equation.json and natural333 analogously.
Every emitted mathematical term is parsed back from the generated LaTeX
and compared to the corresponding exact JSON coefficient and monomial.
"""
from pathlib import Path
from collections import Counter
import argparse, csv, hashlib, io, json, re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def tex_text(value):
    mapping={"\\":r"\textbackslash{}", "&":r"\&", "%":r"\%", "$":r"\$",
             "#":r"\#", "_":r"\_", "{":r"\{", "}":r"\}",
             "~":r"\textasciitilde{}", "^":r"\textasciicircum{}"}
    return ''.join(mapping.get(c,c) for c in str(value))


def render_term(coefficient, monomial, first=False):
    require(isinstance(coefficient,int) and coefficient!=0,"invalid coefficient")
    prefix=('- ' if coefficient<0 else '' if first else '+ ')
    factors=[]
    for variable,power in sorted(Counter(monomial).items()):
        item='z_{'+str(variable)+'}'
        if power!=1:
            item+='^{'+str(power)+'}'
        factors.append(item)
    if not factors:
        return prefix+str(abs(coefficient))
    number='' if abs(coefficient)==1 else str(abs(coefficient))+r'\,'
    return prefix+number+r'\,'.join(factors)


FACTOR=re.compile(r'z_\{(\d+)\}(?:\^\{(\d+)\})?')


def parse_term(source):
    """Inverse parser for the printed polynomial notation, not its comments."""
    s=source.strip()
    sign=-1 if s.startswith('-') else 1
    if s.startswith(('-', '+')):
        s=s[1:].strip()
    factors=list(FACTOR.finditer(s))
    if not factors:
        require(s.isdecimal(),'malformed printed constant: '+source)
        return [sign*int(s),[]]
    prefix=s[:factors[0].start()].replace(r'\,','').strip()
    require(not prefix or prefix.isdecimal(),'malformed printed coefficient: '+source)
    coefficient=sign*(int(prefix) if prefix else 1)
    monomial=[]
    for factor in factors:
        monomial.extend([int(factor[1])]*int(factor[2] or '1'))
    leftover=FACTOR.sub('',s[factors[0].start():]).replace(r'\,','').strip()
    require(not leftover,'unparsed printed mathematical syntax: '+source)
    return [coefficient,monomial]


def verify_tex(tex,rows):
    blocks=re.findall(r'% BEGIN_RESIDUAL (\d+)\n(.*?)% END_RESIDUAL \1\n',tex,re.S)
    require(len(blocks)==len(rows),'a residual is missing or duplicated in LaTeX')
    term_count=0
    for expected_index,(index,body) in enumerate(blocks):
        require(int(index)==expected_index,'residual order changed')
        body=body.replace(r'\begin{align*}','').replace(r'\end{align*}','')
        body=re.sub(r'R_\{'+str(expected_index)+r'\}\s*=\{\}&','',body)
        body=body.replace(r'\quad','').replace('&','').replace(r'\\*','').replace(r'\\','')
        printed=[piece.strip() for piece in re.split(r'(?=[+-])',body) if piece.strip()]
        parsed=[parse_term(piece) for piece in printed]
        require(parsed==rows[expected_index]['terms'],
                'printed coefficients/monomials differ in residual '+str(expected_index))
        term_count+=len(parsed)
    return term_count


def tsv(rows):
    out=io.StringIO(newline='')
    writer=csv.writer(out,delimiter='\t',lineterminator='\n')
    writer.writerows(rows)
    return out.getvalue()


def generate(root,n,terms_per_line):
    source=root/'equations'/('natural'+str(n))/'natural/equation.json'
    data=json.loads(source.read_text())
    variables=data['variables'];rows=data['residuals'];m=len(rows)
    require(len(variables)==n,'unexpected variable count')
    require(data['domain']=='nonnegative integers','unexpected domain')
    require(m>0,'empty residual list')
    for row in rows:
        require(row['terms'],'zero residual cannot be printed silently')
        for c,monomial in row['terms']:
            require(isinstance(c,int) and c!=0,'invalid residual coefficient')
            require(monomial==sorted(monomial),'unsorted source monomial')
            require(len(monomial)<=2,'source residual is not quadratic')
            require(all(isinstance(v,int) and 0<=v<n for v in monomial),'invalid variable index')
    require(any(len(monomial)==2 for row in rows for _,monomial in row['terms']),
            'no quadratic term, so degree four is not established')
    source_hash=hashlib.sha256(source.read_bytes()).hexdigest()
    metrics=data.get('metrics',{})
    counts=(f"{n:,} variables; {m:,} quadratic residuals; degree 4. "
            f"The collected polynomial has {metrics['expanded_monomials']:,} monomials "
            f"and coefficient height {metrics['max_abs_expanded_coefficient']:,}.")
    parts=[r'''\documentclass[10pt]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern,microtype,amsmath,amssymb}
\usepackage[letterpaper,margin=0.65in]{geometry}
\usepackage[hidelinks]{hyperref}
\allowdisplaybreaks[4]
\setlength{\parindent}{0pt}
\setlength{\parskip}{5pt}
\setlength{\jot}{2pt}
\emergencystretch=2em
\begin{document}
''', '\\title{Complete '+str(n)+'-variable quartic\\\\Explicit quadratic residuals}\n',
        r'\author{ProveIt research artifact}'+'\n',r'\date{24 October 2026}'+'\n',r'\maketitle'+'\n',
        '\\section*{The single equation}\n',
        'Every unknown ranges over $\\mathbb N=\\{0,1,2,\\ldots\\}$, in the exact order\n',
        '\\[\n(z_0,z_1,\\ldots,z_{'+str(n-1)+'}).\n\\]\n',
        'The complete equation is\n\\[\n\\boxed{P_{'+str(n)+'}(z_0,\\ldots,z_{'+str(n-1)+'})'
        '=\\sum_{i=0}^{'+str(m-1)+'} R_i(z_0,\\ldots,z_{'+str(n-1)+'})^2=0.}\n\\]\n',
        tex_text(counts)+'\n\n',
        'All $R_i$ are printed below, without omitted coefficients or implicit auxiliary variables. '
        'The symbols $R_i$ are polynomial abbreviations and are not additional unknowns. '
        'The index list is zero based and agrees with the supplied JSON. '
        'Original coordinate names and kinds are supplied in \\texttt{variables-'+str(n)+'.tsv}; '
        'residual names and term counts are supplied in \\texttt{residuals-'+str(n)+'.tsv}.\n\n',
        'The report accompanying this equation proves its natural unsolvability equivalent to '
        '$\\operatorname{Con}(\\mathrm{ZFC})$, using the explicitly identified inherited '
        'C222 calibration. This typesetting file records the entire finite polynomial; '
        'it does not assert a new proof-assistant formalization.\n\n',
        'Source: \\texttt{'+tex_text(str(source.relative_to(root)))+'}.\\\\\n',
        'SHA-256: \\texttt{\\small '+source_hash+'}.\n',
        '\\section*{Complete residual list}\n']
    printed_lines=0
    for i,row in enumerate(rows):
        rendered=[render_term(c,monomial,first=(j==0)) for j,(c,monomial) in enumerate(row['terms'])]
        parts.extend(['% BEGIN_RESIDUAL '+str(i)+'\n',r'\begin{align*}'+'\n'])
        chunks=[rendered[j:j+terms_per_line] for j in range(0,len(rendered),terms_per_line)]
        for line,chunk in enumerate(chunks):
            leader='R_{'+str(i)+'}={}& ' if line==0 else r'&\quad '
            end=r' \\*' if line+1<len(chunks) else ''
            parts.append(leader+' '.join(chunk)+end+'\n')
            printed_lines+=1
        parts.extend([r'\end{align*}'+'\n','% END_RESIDUAL '+str(i)+'\n'])
    parts.append(r'\end{document}'+'\n')
    tex=''.join(parts)
    parsed_count=verify_tex(tex,rows)
    expected_count=sum(len(row['terms']) for row in rows)
    require(parsed_count==expected_count,'total residual-term count mismatch')
    target=root/('equation-'+str(n)+'.tex')
    target.write_text(tex)
    variables_path=root/('variables-'+str(n)+'.tsv')
    variables_path.write_text(tsv([['index','mathematical_name','source_name','kind']]+
        [[i,'z_'+str(i),v['name'],v.get('kind','')] for i,v in enumerate(variables)]))
    residuals_path=root/('residuals-'+str(n)+'.tsv')
    residuals_path.write_text(tsv([['index','mathematical_name','source_label','term_count']]+
        [[i,'R_'+str(i),row['label'],len(row['terms'])] for i,row in enumerate(rows)]))
    return {'variables':n,'residuals':m,'source_residual_terms':expected_count,
        'parsed_printed_terms':parsed_count,'mathematical_lines':printed_lines,
        'maximum_terms_per_line':terms_per_line,'source_sha256':source_hash,
        'tex_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
        'tex_file':target.name,'variables_file':variables_path.name,
        'residuals_file':residuals_path.name,'all_printed_coefficients_and_indices_exact':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--terms-per-line',type=int,default=5)
    args=parser.parse_args()
    require(1<=args.terms_per_line<=6,'choose between one and six terms per line')
    root=args.root.resolve()
    result={'schema':'complete_quartic_typesetting_check_v1',
        'equations':[generate(root,n,args.terms_per_line) for n in (332,333)]}
    (root/'equation-typesetting-check.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
