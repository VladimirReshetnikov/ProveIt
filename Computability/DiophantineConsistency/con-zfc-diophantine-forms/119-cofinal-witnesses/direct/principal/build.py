#!/usr/bin/env python3
"""Guard-free factorial output via an integer consecutive-product modulus.

Builds a new literal signed source, then applies the frozen integral
projection/factorization/translation tools. The semantic theorem is
separate in PROOF.md.
"""
from pathlib import Path
from collections import Counter
import json,hashlib,copy,sys,argparse

HERE=Path(__file__).resolve().parent
PARENT=HERE/'parent'
sys.dont_write_bytecode=True
sys.path.insert(0,str(PARENT/'direct'))
import terminal_elimination as E
import factor_horn as H
import translate_coordinates as T

def need(ok,why):
    if not ok:raise ValueError(why)

def read(n):return json.loads((PARENT/n).read_text())
def digest(obj):return hashlib.sha256(E.canonical_bytes(obj)).hexdigest()

def specialize():
    source=read('direct/derived16_signed_shell/guarded.json')
    mixed=read('direct/derived16_signed_shell/mixed_source.json')
    raw=read('architecture/derived16_shell/raw/raw_audit_input.json')
    need((len(source['variables']),len(source['residuals']))==(739,532),'frozen guarded source dimensions')
    need(source['residuals'][:469]==mixed['residuals'],'literal mixed prefix')
    byname={v['name']:i for i,v in enumerate(source['variables'])}
    need({n:byname[n] for n in ['t0','y','fact0.output','pow0.output','mul.1','mul.2','mul.36','add.34']}==
         {'t0':0,'y':2,'fact0.output':3,'pow0.output':7,'mul.1':4,'mul.2':5,'mul.36':27,'add.34':26},'semantic coordinate bindings')
    need(source['residuals'][1]['terms']==[[-1,[3,4]],[1,[5]]],'old radius row')
    need(source['residuals'][11]['terms']==[[-18,[]],[-1,[0]],[-1,[1]],[-1,[2]],[-1,[3]],[1,[26]]],'old R row')
    rows=copy.deepcopy(source['residuals']);changes=[]
    for rid,p in [(1,{(5,):1,(4,27):-1}),
                  (11,{(26,):1,():-18,(0,):-1,(1,):-1,(2,):-1,(27,):-1})]:
        new=dict(rows[rid],terms=E.as_terms(p));changes.append({'row':rid,'old':rows[rid],'new':new});rows[rid]=new
    # The existing 27=F^2 wire is shared by the radius and the R majorant.
    need(E.normalize(rows[12]['terms'])=={(27,):1,(3,3):-1},'shared factorial square')
    labels={r['label']:i for i,r in enumerate(rows)}
    need([labels['nonnegative.'+str(i)] for i in [0,3,12]]==[469,471,474],'guard rows')
    removed=sorted(byname[f'nonnegative.{i}.{s}'] for i in [0,3,12] for s in 'abc')
    need(len(removed)==9,'three private guard triples')
    for rid,r in enumerate(rows):
        if rid not in [469,471,474]:need(not any(v in removed for c,m in r['terms'] for v in m),'private guard support')
    square_coordinate=len(source['variables'])
    horizon={'label':'cofinal.horizon_square','terms':E.as_terms({(0,):1,(square_coordinate,square_coordinate):-1})}
    modulus={'label':'cofinal.signed_factorial_beta_modulus','terms':E.as_terms({(2,):1,(7,7):-1,(7,):1})}
    # V^2 appears directly as a quadratic monomial; no extra square wire
    # is introduced for the consecutive-product modulus.
    guard_changes=[{'row':469,'old':rows[469],'new':horizon},
                   {'row':471,'old':rows[471],'new':None},
                   {'row':474,'old':rows[474],'new':modulus}]
    rows[469]=horizon;rows[474]=modulus
    retained=[i for i in range(len(source['variables'])) if i not in removed]+[square_coordinate]
    remap={v:i for i,v in enumerate(retained)}
    variables=source['variables']+[{'name':'cofinal.horizon_root','kind':'integer_square'}]
    out=copy.deepcopy(source);out.pop('metrics',None);out.pop('elimination',None)
    out['variant']='cofinal_signed_factorial_consecutive_modulus_source'
    out['variables']=[variables[i] for i in retained]
    out['residuals']=[{'label':r['label'],'terms':[[c,[remap[v] for v in m]] for c,m in r['terms']]}
                       for i,r in enumerate(rows) if i!=471]
    # Raw audit data changes precisely the same two algebraic definitions.
    newraw=copy.deepcopy(raw)
    need(raw['rows'][2]['terms']==[[-1,[4,5]],[1,[6]]],'raw radius binding')
    need(raw['rows'][39]['terms']==[[-1,[4]],[-1,[53]],[1,[54]]],'raw R binding')
    newraw['rows'][2]['terms']=[[-1,[5,56]],[1,[6]]]
    newraw['rows'][39]['terms']=[[-1,[56]],[-1,[53]],[1,[54]]]
    newraw['local_majorant']['base']='2+t+x+y+F^2'
    newraw['cofinal_signed_factorial']={'horizon':'16+s^2','radius':'F^2*t^2','R':'2+t+x+y+F^2','beta_modulus':'V*(V-1)',
                                      'F_initially_signed':True,'new_source_equivalence_requires':'PROOF.md'}
    cert={'schema':'signed_factorial_source_transformation_v1','input_sha256':digest(source),'output_sha256':digest(out),
          'old_dimensions':[739,532],'new_dimensions':[len(out['variables']),len(out['residuals'])],
          'algebraic_changes':changes,'guard_changes':guard_changes,'removed_old_coordinates':removed,
          'appended_old_index':square_coordinate,'retained_old_coordinates':retained,
          'presemantic_positivity':'For every integer V, y=V*(V-1)>=0, hence y+1>=1.',
          'ordinary_source_equivalence_claimed_by_code':False,'new_raw_sha256':digest(newraw)}
    return out,newraw,cert

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'regenerated');ap.add_argument('--cap',type=int,default=16);args=ap.parse_args()
    out=args.output;out.mkdir(parents=True,exist_ok=True)
    source,raw,sourcecert=specialize()
    # Factor before projecting, exactly as in the inherited 517 construction.
    # Early projection can delete the named roots needed by its certificate.
    factored,fc=H.transform(source)
    compact,p2,m2=E.optimize(factored,max_support=args.cap);E.verify(factored,compact,p2)
    shifts={i:-1 for i,v in enumerate(compact['variables']) if v['name'].startswith('crt.encoded') or v['name'] in ['t0','M0'] or v['name'].endswith('minus1')}
    centered=T.translate(compact,shifts);expanded=E.expand(centered)
    inverse=T.translate(centered,{v:-s for v,s in shifts.items()})
    need(inverse['variables']==compact['variables'] and inverse['residuals']==compact['residuals'],'two-sided integer translation')
    metrics={'variables':len(centered['variables']),'quadratic_rows':len(centered['residuals']),'exact_degree':max(len(m) for c,m in expanded['terms']),
             'expanded_monomials':len(expanded['terms']),'max_abs_expanded_coefficient':max(abs(c) for c,m in expanded['terms']),
             'max_abs_row_coefficient':max(abs(c) for r in centered['residuals'] for c,m in r['terms'])}
    trans={'schema':'integral_translation_v1','input_sha256':digest(compact),'output_sha256':digest(centered),
           'shifts':[[i,s] for i,s in sorted(shifts.items())],'convention':'old_coordinate = new_coordinate + shift'}
    objects={'signed_source.json':source,'raw_audit_input.json':raw,'source_transformation.json':sourcecert,
             'factored_source.json':factored,'factorization.json':fc,
             'untranslated_equation.json':compact,'projection2.json':p2,'equation.json':centered,'expanded_polynomial.json':expanded,
             'translation.json':trans,'METRICS.json':metrics}
    for name,obj in objects.items():(out/name).write_bytes(E.canonical_bytes(obj))
    print(json.dumps(metrics,sort_keys=True))

if __name__=='__main__':main()
