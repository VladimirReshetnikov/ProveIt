#!/usr/bin/env python3
"""Human-readable residuals, coordinate table and complete affine restorations."""
import argparse,collections,json,re
from pathlib import Path
def lin(a,b,k):
    z=collections.Counter(a)
    for m,c in b.items():z[m]+=k*c
    return {m:c for m,c in z.items() if c}
def fmt(terms,tex=False):
    out=[]
    for c,m in terms:
        body=str(abs(c))
        if m:body+=(' ' if tex else '*')+(' '.join('x_{'+str(i)+'}' for i in m) if tex else '*'.join('x'+str(i) for i in m))
        out.append(('- ' if c<0 else '+ ')+body)
    return out
def parse_math(text,tex=False):
    if tex:
        text=text.replace('\\\\',' ').replace('\\quad',' ').replace('&',' ')
        pattern=r'([+-])\s*(\d+)((?:\s*x_\{\d+\})*)'
    else:pattern=r'([+-])\s*(\d+)((?:\*x\d+)*)'
    terms=[];end=0
    for m in re.finditer(pattern,text):
        if text[end:m.start()].strip():raise ValueError('unparsed residual syntax')
        c=int(m[2])*(-1 if m[1]=='-' else 1);ids=list(map(int,re.findall(r'\d+',m[3])));terms.append([c,ids]);end=m.end()
    if text[end:].strip():raise ValueError('trailing residual syntax')
    return terms
def main():
    p=argparse.ArgumentParser();p.add_argument('--release',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--check',action='store_true');a=p.parse_args();manifest=json.loads((a.release/'ENDPOINTS.json').read_text());counts={}
    for name,item in manifest['endpoints'].items():
        out=a.release/item['directory'];equation=json.loads((out/'equation.json').read_text());source=json.loads((a.release/item['source']).read_text());cert=json.loads((a.release/item['certificate']).read_text());rows=equation['residuals']
        lines=['All coordinates x0,...,x'+str(len(equation['variables'])-1)+' range independently over Z.','The equation is P = sum(r_i^2) = 0; row and coordinate indices are zero-based.','']
        tex=['% Generated complete residual list. Load amsmath in the enclosing document.','\\begingroup\\small','All coordinates are unrestricted integers. Indices are zero-based. The equation is $\\sum_i r_i^2=0$.']
        for i,row in enumerate(rows):
            terms=row['terms'];text=' '.join(fmt(terms));require=(parse_math(text)==terms)
            if not require:raise ValueError('text transcription')
            lines.append(f'r{i} = '+text)
            pieces=fmt(terms,True);parts=[' '.join(pieces[j:j+4]) for j in range(0,len(pieces),4)];math=' \\\\\n &\\quad '.join(parts)
            if parse_math(math,True)!=terms:raise ValueError('TeX transcription')
            tex.append('\\[\\begin{aligned}\nr_{'+str(i)+'} &= '+math+'\n\\end{aligned}\\]')
        tex.append('\\endgroup');text='\n'.join(lines)+'\n';latex='\n'.join(tex)+'\n';table='index\tname\tkind\n'+''.join(f'{i}\t{v["name"]}\t{v["kind"]}\n' for i,v in enumerate(equation['variables']))
        # Reconstruct all source coordinates from retained final coordinates.
        dropped={s['variable'] for s in cert['affine_projections']};keep=[i for i in range(len(source['variables'])) if i not in dropped];restore={i:{(j,):1} for j,i in enumerate(keep)}
        for step in reversed(cert['affine_projections']):
            value={}
            for c,m in step['replacement']:
                if len(m)>1:raise ValueError('nonaffine map')
                value=lin(value,restore[m[0]] if m else {():1},c)
            restore[step['variable']]=value
        names={v['name']:i for i,v in enumerate(source['variables'])}
        for target,inputs in reversed(cert['coordinate_shears']):
            for other,c in inputs.items():restore[names[target]]=lin(restore[names[target]],restore[names[other]],c)
        maps={'schema':'affine_integer_zero_restoration_v1','direction':'original_parent_coordinates_as_affine_polynomials_in_final_coordinates','coordinates':[{'index':i,'name':source['variables'][i]['name'],'terms':[[c,list(m)] for m,c in sorted(restore[i].items())]} for i in range(len(source['variables']))]}
        payloads={'residuals.txt':text,'residuals.tex':latex,'variables.tsv':table,'RESTORATION.json':json.dumps(maps,sort_keys=True,separators=(',',':'))+'\n'}
        for file,content in payloads.items():
            path=out/file
            if a.check:
                if path.read_text()!=content:raise ValueError('readable/map export differs: '+str(path))
            else:path.write_text(content)
        counts[name]={'rows_roundtripped_from_text_and_TeX':len(rows),'restoration_coordinates':len(maps['coordinates'])}
    print(json.dumps({'status':'pass','check_only':a.check,'endpoints':counts},indent=2))
if __name__=='__main__':main()
