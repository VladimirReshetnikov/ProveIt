#!/usr/bin/env python3
"""Replay frozen integral maps, changing the frame and one center row.

The two new source rows use the one-square theorem. Every other step is
an exact integer coordinate or residual transformation checked here.
"""
from pathlib import Path
import argparse, copy, hashlib, json
from polynomial import *

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'inherited/package166'

def read(path):
    return json.loads(path.read_text())

def canonical(x):
    return (json.dumps(x, sort_keys=True, separators=(',',':'))+'\n').encode()

def put(path, value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(canonical(value))

def must(condition,message):
    if not condition:
        raise ValueError(message)

def compare(a,b,label):
    must(a['variables']==b['variables'],label+' variables differ')
    must(len(a['residuals'])==len(b['residuals']),label+' row count differs')
    for i,(u,v) in enumerate(zip(a['residuals'],b['residuals'])):
        must(u['label']==v['label'],label+' row label differs')
        must(poly(u['terms'])==poly(v['terms']),label+f' row {i} differs')

def change_source(eq):
    result=copy.deepcopy(eq)
    names={v['name']:i for i,v in enumerate(eq['variables'])}
    wi=names['shared.W']; ui=names['free_A.u']; vi=names['free_A.v']
    fi=next(i for i,r in enumerate(eq['residuals']) if r['label']=='shared.frame_definition')
    ci=next(i for i,r in enumerate(eq['residuals']) if r['label']=='free_A.cofinal_constructor')
    f=poly(eq['residuals'][fi]['terms']);c=poly(eq['residuals'][ci]['terms'])
    must(f.get((wi,))==1 and not any(wi in m and m!=(wi,) for m in f),'W is not an isolated linear frame coordinate')
    must(c.get((ui,ui))==-1 and c.get((vi,vi))==-1,'old center is not the declared two-square center')
    must(all(vi not in m for i,r in enumerate(eq['residuals']) if i!=ci for m in poly(r['terms'])),'center v is not private')
    # The inherited canonical completeness choices make S odd. Thus the
    # stronger frame W=3+S is even at those choices. Soundness uses only
    # W>=2+S, and does not require evenness at an arbitrary polynomial zero.
    nf=add(f,const(-1))
    nc=add(c,scale(-1,mul(var(ui),var(ui))),mul(var(vi),var(vi)))
    result['residuals'][fi]['terms']=terms(nf)
    result['residuals'][ci]['terms']=terms(nc)
    return result,dict(frame_mode='canonical_parity_constant_increment',
      frame_row=fi,center_row=ci,W=wi,u=ui,deleted_private_v=vi,
      frame_before=terms(f),frame_after=terms(nf),center_before=terms(c),center_after=terms(nc))

def replay_projection(eq,cert):
    rows=[poly(r['terms']) for r in eq['residuals']]
    removed=set();dead=set()
    for no,s in enumerate(cert['steps']):
        i=s['row_id'];v=s['variable'];rest=poly(s['restoration'])
        must(i not in removed and v not in dead,'repeated elimination')
        must(all(v not in m for m in rest),'self-referential restoration')
        pivot=add(var(v),scale(-1,rest))
        must(rows[i] in (pivot,scale(-1,pivot)),f'nonmonic projection at step {no}')
        rows=[subst(p,v,rest) for p in rows]
        must(not rows[i],f'pivot {no} did not vanish')
        must(all(degree(p)<=2 for p in rows),'projection raised degree')
        removed.add(i);dead.add(v)
    keepv=cert['retained_original_variables'];keepr=cert['retained_original_rows']
    must(set(keepr)==set(range(len(rows)))-removed,'row retention mismatch')
    must(all(not p for i,p in enumerate(rows) if i not in keepr),'deleted row is nonzero')
    return dict(domain='unrestricted integers',polynomial='sum(square(row) for row in residuals)',
       variables=[eq['variables'][i] for i in keepv],
       residuals=[dict(label=eq['residuals'][i]['label'],terms=terms(reindex(rows[i],keepv))) for i in keepr])

def translate(eq,shifts):
    result=copy.deepcopy(eq)
    for r in result['residuals']:
        p=poly(r['terms'])
        for v,s in shifts:
            p=subst(p,v,add(var(v),const(s)))
        r['terms']=terms(p)
    return result

def replay_final(eq,cert):
    rows=[poly(r['terms']) for r in eq['residuals']]
    for no,op in enumerate(cert['operations']):
        kind=op['type']
        if kind in ('translation','shear','projection'):
            v=op['variable']
            rest=add(var(v),const(op['delta'])) if kind=='translation' else poly(op['restoration'])
            if kind=='projection':
                i=op['row'];pivot=add(var(v),scale(-1,rest))
                must(rows[i] in (pivot,scale(-1,pivot)),f'final nonmonic pivot {no}')
            rows=[subst(p,v,rest) for p in rows]
        elif kind=='row_add':
            must(op['source']!=op['target'],'self row addition')
            rows[op['target']]=add(rows[op['target']],scale(op['multiple'],rows[op['source']]))
        else:
            raise ValueError('unknown operation '+kind)
        must(all(degree(p)<=2 for p in rows),f'degree raised at final operation {no}')
    keepv=cert['retained_variables'];keepr=cert['retained_rows']
    must(all(not p for i,p in enumerate(rows) if i not in keepr),'deleted final row is nonzero')
    return dict(domain='unrestricted integers',polynomial='sum(square(row) for row in residuals)',
       variables=[eq['variables'][i] for i in keepv],
       residuals=[dict(label=eq['residuals'][i]['label'],terms=terms(reindex(rows[i],keepv))) for i in keepr])

def drop_unused(eq):
    used=sorted({v for r in eq['residuals'] for _,m in r['terms'] for v in m})
    removed=[i for i in range(len(eq['variables'])) if i not in used]
    must(len(removed)==1 and eq['variables'][removed[0]]['name']=='free_A.v','unexpected unused variable')
    result=copy.deepcopy(eq)
    result['variables']=[eq['variables'][i] for i in used]
    for r in result['residuals']:
        r['terms']=terms(reindex(poly(r['terms']),used))
    return result,removed[0]

def math_string(p,latex=False):
    items=[]
    for m,c in sorted(p.items()):
        abs_c=abs(c)
        counts={v:m.count(v) for v in dict.fromkeys(m)}
        if latex:
            mon=' '.join('x_{'+str(v)+'}'+('^{'+str(k)+'}' if k>1 else '') for v,k in counts.items())
            body=(str(abs_c) if abs_c!=1 or not m else '')+mon
        else:
            mon='*'.join('x'+str(v)+('**'+str(k) if k>1 else '') for v,k in counts.items())
            body=(str(abs_c)+('*' if m else '') if abs_c!=1 or not m else '')+mon
        items.append(('-' if c<0 else '+',body))
    if not items:return '0'
    return (('-' if items[0][0]=='-' else '')+items[0][1])+''.join(' '+s+' '+b for s,b in items[1:])

def export(eq,path):
    text='\n'.join(f'R{i} = '+math_string(poly(r['terms'])) for i,r in enumerate(eq['residuals']))+'\n'
    (path/'residuals.txt').write_text(text)
    lines=['% Generated from equation.json by code/build_one_square.py',r'\begingroup\small']
    for i,r in enumerate(eq['residuals']):
        ts=sorted(poly(r['terms']).items())
        chunks=[ts[j:j+7] for j in range(0,len(ts),7)]
        lines.append(r'\begin{equation*}\begin{split}')
        for j,chunk in enumerate(chunks):
            s=math_string(dict(chunk),True)
            if j:
                if not s.startswith('-'):s='+ '+s
                lines.append(r'&\quad '+s+(r'\\' if j<len(chunks)-1 else ''))
            else:
                lines.append('R_{'+str(i)+'}={}&'+s+(r'\\' if len(chunks)>1 else ''))
        lines.append(r'\end{split}\end{equation*}')
    lines.append(r'\endgroup')
    (path/'residuals.tex').write_text('\n'.join(lines)+'\n')
    (path/'variables.tsv').write_text('coordinate\tinherited_name\n'+''.join(f'{i}\t{v["name"]}\n' for i,v in enumerate(eq['variables'])))

def build(out):
    raw=read(BASE/'stages/compressed/raw_source.json')
    fac=read(BASE/'stages/compressed/factored_source.json')
    newfac,delta=change_source(fac)
    newraw,rawdelta=change_source(raw)
    # Horn refactoring leaves the two semantic rows literally unchanged.
    for label in ('shared.frame_definition','free_A.cofinal_constructor'):
        oldr=next(r for r in raw['residuals'] if r['label']==label)
        facr=next(r for r in fac['residuals'] if r['label']==label)
        must(poly(oldr['terms'])==poly(facr['terms']),'changed row participates in Horn factoring')
    pc=read(BASE/'stages/compressed/projection_certificate.json')
    shifts=read(BASE/'stages/compressed/translation_certificate.json')['shifts']
    oldprojected=replay_projection(fac,pc)
    compare(oldprojected,read(BASE/'stages/compressed/projected.json'),'baseline projection')
    old=translate(oldprojected,shifts)
    compare(old,read(BASE/'stages/compressed/equation.json'),'baseline translation')
    new=translate(replay_projection(newfac,pc),shifts)
    summary={}
    for profile in ('balanced','compact'):
        cert=read(BASE/'equations'/profile/'certificate.json')
        oldfinal=replay_final(old,cert)
        compare(oldfinal,read(BASE/'equations'/profile/'equation.json'),'baseline '+profile)
        final,deleted=drop_unused(replay_final(new,cert))
        n=len(final['variables'])
        final.update(schema='one_scaled_square_conzfc_v1',name=f'P{n}_{profile}',
             source_pin='02a78a08603cbae248c19c23a75907c6c6bd6443',
             proof='proofs/ONE_SQUARE_CENTER.md and report/report.tex')
        endpoint=out/f'P{n}_{profile}'
        put(endpoint/'equation.json',final)
        put(endpoint/'expanded_polynomial.json',dict(variables=n,terms=terms(expand(final))))
        met=metric(final);summary[final['name']]=met
        put(endpoint/'metrics.json',met)
        put(endpoint/'certificate.json',dict(source_delta=delta,raw_delta=rawdelta,
          inherited_projection_steps=len(pc['steps']),final_profile=profile,
          inherited_final_operations=len(cert['operations']),deleted_final_coordinate=deleted,
          source_equation_sha256=hashlib.sha256((BASE/'equations'/profile/'equation.json').read_bytes()).hexdigest(),
          output_sha256=hashlib.sha256(canonical(final)).hexdigest()))
        export(final,endpoint)
    put(out/'SUMMARY.json',summary)
    return summary

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,default=ROOT/'equations')
    args=ap.parse_args()
    print(json.dumps(build(args.output),indent=2))
