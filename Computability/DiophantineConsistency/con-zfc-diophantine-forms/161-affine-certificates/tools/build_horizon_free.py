#!/usr/bin/env python3
"""Separate larger-coefficient companion: eliminate the horizon square guard.

The selected growth base is 2^26*(2*t+1), with t now recovered from its
power request. Uses verify_affine as an exact algebra engine; that module
is not an independent checker for this separate construction.
"""
from pathlib import Path
import argparse,copy,hashlib,json,zipfile
import verify_affine as V

ROOT=Path(__file__).resolve().parent
OUT=ROOT.parent/'stages'/'horizon'
def put(p,obj):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def recertify_projection(source,cert):
    c=copy.deepcopy(cert);r=V.rows(source)
    for p in c['steps']:
        value=V.monic_value(r[p['row_id']],p['variable'])
        p['restoration']=V.dump_terms(value)
        p['restoration_degree']=max(map(len,value),default=0)
        r=[V.replace(row,p['variable'],value) for row in r]
    c.pop('input_sha256',None);c.pop('output_sha256',None);c.pop('metrics',None)
    c['schema']='horizon_free_rederived_monic_certificate_v1'
    return c
def recertify_affine(source,cert):
    c=copy.deepcopy(cert);r=V.rows(source);names={v['name']:i for i,v in enumerate(source['variables'])}
    for name,inputs in c['coordinate_shears']:
        i=names[name];value={(i,):1}
        for name,k in inputs.items():value=V.plus(value,{(names[name],):k})
        r=[V.replace(p,i,value) for p in r]
    for i,j,k in c['row_operations']:r[i]=V.plus(r[i],r[j],k)
    for p in c['projections']:
        value=V.monic_value(r[p['row']],p['variable'])
        p['replacement']=V.dump_terms(value)
        r=[V.replace(q,p['variable'],value) for q in r]
    return c
def main():
    global OUT
    parser=argparse.ArgumentParser()
    parser.add_argument("--archive",type=Path,default=V.ARCHIVE)
    parser.add_argument("--output",type=Path,default=OUT)
    args=parser.parse_args()
    V.ARCHIVE=args.archive
    OUT=args.output
    with zipfile.ZipFile(V.ARCHIVE) as z:
        get=lambda n:V.read_json(z,n)
        raw=V.expected_mutation(get('factorial_free_affine/raw_source.json'))
        names={v['name']:i for i,v in enumerate(raw['variables'])};t=names['t0'];d=names['growth.power_base'];root=names['cofinal.horizon_root']
        changes=[]
        for i,r in enumerate(raw['residuals']):
            if r['label']=='growth.base_definition':
                before=copy.deepcopy(r['terms']);V.require(V.polynomial(before)=={(d,):1,(t,):-2,():-34},'unexpected growth base')
                r['terms']=V.dump_terms({(d,):1,(t,):-(1<<27),():-33*(1<<26)})
                changes.append({'row':i,'before':before,'after':r['terms'],'meaning':'d=2^26*(2*(t0+16)+1)'})
            elif r['label']=='cofinal.horizon':
                before=copy.deepcopy(r['terms']);V.require(V.polynomial(before)=={(t,):1,(root,root):-1},'unexpected horizon guard')
                r['terms']=[];changes.append({'row':i,'before':before,'after':[],'meaning':'remove t=16+h^2 guard'})
        V.require(len(changes)==2,'horizon source mutation census')
        fac=V.factor(raw,get('factorial_free_affine/factored_source.json'),get('factorial_free_affine/factorization_certificate.json'))
        pc=recertify_projection(fac,get('factorial_free_affine/projection_certificate.json'))
        pr=V.project(fac,pc);tr=V.translate(pr,get('factorial_free_affine/translation_certificate.json'))
        put(OUT/'raw_source.json',raw);put(OUT/'projection_certificate.json',pc)
        put(OUT/'source_changes.json',{'source_archive_sha256':hashlib.sha256(V.ARCHIVE.read_bytes()).hexdigest(),'changes':changes,'growth_multiplier':1<<26})
        for profile,n in [('principal',242),('companion',241)]:
            ac=recertify_affine(tr,get(f'factorial_free_affine{n}_balanced/certificate.json'))
            src=V.affine(tr,ac);r=V.rows(src);names={v['name']:i for i,v in enumerate(src['variables'])}
            qr=next(i for i,row in enumerate(src['residuals']) if row['label']=='radix.odd_square')
            sr=next(i for i,row in enumerate(src['residuals']) if row['label']=='beta.odd_square_multiplier')
            hr=next(i for i,row in enumerate(src['residuals']) if row['label']=='cofinal.horizon')
            q=names['pow2.output'];s=names['beta.odd_square_multiplier'];h=names['cofinal.horizon_root']
            pivots=[]
            for i,j in [(q,qr),(s,sr)]:
                value=V.monic_value(r[j],i);pivots.append({'row':j,'variable':i,'replacement':V.dump_terms(value)})
                r=[V.replace(row,i,value) for row in r]
            V.require(not r[hr],'horizon row not zero')
            V.require(not any(h in mon for row in r for mon in row),'horizon root remains live')
            kv=[i for i in range(len(src['variables'])) if i not in (q,s,h)];kr=[i for i in range(len(r)) if i not in (qr,sr,hr)]
            eq=V.compact(src,r,kv,kr);eq['variant']='horizon_free_affine_radix_odd_beta_'+profile
            V.require(all(len(m)<=2 for row in V.rows(eq) for m in row),'nonquadratic result')
            P=V.recollect(eq)
            metrics={'domain':'unrestricted integers','variables':len(eq['variables']),'quadratic_residuals':len(eq['residuals']),'degree':max(map(len,P)),'collected_monomials':len(P),'coefficient_height':max(map(abs,P.values())),'residual_height':max(abs(c) for row in V.rows(eq) for c in row.values())}
            V.require({i for m in P for i in m}==set(range(len(eq['variables']))),'unused variable')
            out=OUT/profile
            for name,obj in [('mutated_source.json',src),('affine_certificate.json',ac),('final_certificate.json',{'pivots':pivots,'deleted_zero_row':hr,'unconstrained_removed':h,'retained_original_variables':kv,'retained_original_rows':kr}),('equation.json',eq),('expanded_polynomial.json',{'variables':len(eq['variables']),'terms':V.dump_terms(P)}),('metrics.json',metrics)]:put(out/name,obj)
            print(profile,json.dumps(metrics,sort_keys=True))
if __name__=='__main__':main()
