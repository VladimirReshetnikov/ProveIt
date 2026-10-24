#!/usr/bin/env python3
"""Independent exact replay of guards, substitutions and SOS coefficients.
No builder or elimination implementation is imported.
"""
import argparse, copy, hashlib, json, subprocess, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent

def require(ok,why):
    if not ok:raise ValueError(why)
def canon(d):return (json.dumps(d,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(d):return hashlib.sha256(canon(d)).hexdigest()
def gather(terms):
    out={}
    for c,m in terms:
        require(type(c) is int,'coefficient is not an integer')
        key=tuple(sorted(m));out[key]=out.get(key,0)+c
    return {m:c for m,c in out.items() if c}
def listing(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def expand_substitution(row,v,replacement):
    terms=[]
    for m,c in row.items():
        block=[(c,())]
        for w in m:
            factor=replacement.items() if w==v else [((w,),1)]
            block=[(a*b,tuple(sorted(u+z))) for a,u in block for z,b in factor]
        terms.extend((a,u) for a,u in block)
    return gather(terms)

def check(source,domain,eq,expanded,certificate):
    n=len(source['variables']);guards=domain['guards']
    require(certificate['source_natural_sha256']==sha(source),'source digest')
    require(certificate['target_equation_sha256']==sha(eq),'target digest')
    require(certificate['guard_indices']==guards,'guard list differs from domain proof')
    require(len(guards)==170 and len(set(guards))==170,'guard count or repeats')
    names=copy.deepcopy(source['variables']);rows=[copy.deepcopy(r) for r in source['residuals']]
    for v in guards:
        require(0<=v<n,'guard coordinate outside source')
        a,b,c=range(len(names),len(names)+3)
        names.extend({'name':'guard.'+str(v)+'.'+s,'kind':'guard'} for s in 'abc')
        rows.append({'label':'nonnegative.'+str(v),
                     'terms':listing(gather([(1,[v]),(-1,[a,a]),(-1,[b,b]),(-1,[c,c]),(-1,[c])]))})
    guarded=copy.deepcopy(source);guarded['domain']='integers';guarded['variables']=names;guarded['residuals']=rows
    require(certificate['guarded_equation_sha256']==sha(guarded),'guarded system digest')
    work={i:gather(r['terms']) for i,r in enumerate(rows)};live=set(range(len(names)))
    for step in certificate['steps']:
        rid,v,sgn=step['row_id'],step['variable'],step['sign']
        require(rid in work and v in live and sgn in (-1,1),'invalid or repeated pivot')
        require(listing(work[rid])==step['row'],'pivot row differs')
        replacement=gather(step['definition'])
        require(all(v not in m for m in replacement),'cyclic restoration')
        require(all(w in live for m in replacement for w in m),'restoration uses eliminated variable')
        expected=gather([(sgn,[v])]+[(-sgn*d,m) for m,d in replacement.items()])
        require(expected==work[rid],'monic restoration identity fails')
        del work[rid];live.remove(v)
        for r in work:
            work[r]=expand_substitution(work[r],v,replacement)
            require(all(len(m)<=2 for m in work[r]),'residual degree exceeds two')
    retained=certificate['retained'];unused=certificate['unused']
    require(set(retained).isdisjoint(unused) and set(retained)|set(unused)==live,'live partition')
    used={v for row in work.values() for m in row for v in m}
    require(sorted(used)==retained,'retained variable set')
    ids=[i for i in sorted(work) if work[i]]
    require(ids==certificate['row_ids'],'residual row ordering')
    ren={v:i for i,v in enumerate(retained)}
    expected_rows=[{'label':rows[i]['label'],
                    'terms':listing({tuple(ren[v] for v in m):d for m,d in work[i].items()})} for i in ids]
    require(eq['variables']==[names[v] for v in retained],'final variable names')
    require(eq['residuals']==expected_rows,'final quadratic residuals')
    require(eq['domain']=='unrestricted integers','final domain')
    square_terms=[]
    for row in expected_rows:
        terms=row['terms']
        square_terms.extend((a*b,ma+mb) for a,ma in terms for b,mb in terms)
    polynomial=gather(square_terms)
    require(expanded['terms']==listing(polynomial),'expanded SOS coefficient mismatch')
    met={'variables':len(retained),'residuals':len(ids),'degree':max(map(len,polynomial)),
         'monomials':len(polynomial),'coefficient_height':max(map(abs,polynomial.values()))}
    require(met==eq['metrics'],'metrics differ')
    require(met['variables']==977 and met['degree']==4,'claimed dimension/degree')
    leading=next((m,c) for m,c in sorted(polynomial.items()) if len(m)==4)
    return {'status':'PASS','metrics':met,'guard_count':len(guards),
            'integer_contractions':len(certificate['steps']),
            'degree_four_witness':[leading[1],list(leading[0])],
            'scope':'Exact finite algebra; unbounded domain/consistency proofs are separate.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
    p=subprocess.run([sys.executable,str(ROOT/'code/check_domain_certificate.py')],capture_output=True,text=True)
    require(p.returncode==0,'domain certificate rejected: '+p.stderr)
    source=json.loads((ROOT/'equations_v3/cap64/equation.json').read_text())
    domain=json.loads((ROOT/'DOMAIN_CERTIFICATE.json').read_text())
    q=ROOT/'integer977';eq=json.loads((q/'equation.json').read_text())
    expanded=json.loads((q/'expanded_polynomial.json').read_text())
    certificate=json.loads((q/'elimination_certificate.json').read_text())
    result=check(source,domain,eq,expanded,certificate)
    bad=copy.deepcopy(certificate);bad['steps'][0]['definition'][0][0]+=1
    try:check(source,domain,eq,expanded,bad)
    except ValueError:pass
    else:raise ValueError('altered restoration accepted')
    badpoly=copy.deepcopy(expanded);badpoly['terms'][0][0]+=1
    try:check(source,domain,eq,badpoly,certificate)
    except ValueError:pass
    else:raise ValueError('altered coefficient accepted')
    result['negative_controls']=['altered restoration rejected','altered expanded coefficient rejected']
    result['optimized_python']=not __debug__
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
