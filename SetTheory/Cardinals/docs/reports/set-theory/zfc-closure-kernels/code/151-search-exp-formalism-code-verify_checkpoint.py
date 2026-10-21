#!/usr/bin/env python3
"""Independent finite checks and evidence consistency; Python standard library.

This validates the finite countermodels, source counts, exact omission, table
syntax, and receipt consistency. It does not replay the unbounded symbolic
runtime proof: use check_runtime_omit.py with the pinned central vendor for that.
"""
from pathlib import Path
import argparse,hashlib,itertools,json
from source_format import read_tree,subtree,replace,write_sites,compact,metrics
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def model(p,persistent):
    d=load(p);n=d['n'];top=(1<<n)-1;up=d['up'];S=d['accessibility_upsets']
    assert len(up)==len(S)==n
    for i in range(n):
        assert up[i]>>i&1
        for j in range(n):
            if up[i]>>j&1:assert up[j]&~up[i]==0
            if i!=j:assert not(up[i]>>j&1 and up[j]>>i&1)
    U=[a for a in range(1<<n)if all(not(a>>w&1)or up[w]&~a==0 for w in range(n))]
    assert U==d['upsets'];assert all(s in U and s!=0 for s in S)
    def imp(a,b):return sum(1<<w for w in range(n)if up[w]&a&~b==0)
    def neg(a):return imp(a,0)
    def q(a):return sum(1<<w for w in range(n)if S[w]&~a==0)
    assert {str(a):q(a)for a in U}==d['Q']
    assert all(q(a)in U for a in U);assert q(0)==0 and q(top)==top
    normality=0;meet=0
    for a,b in itertools.product(U,repeat=2):
        assert q(a&b)==q(a)&q(b);meet+=1
        assert q(imp(a,b))&~imp(q(a),q(b))==0;normality+=1
    for a in U:assert neg(q(neg(q(a))))&~a==0
    a=d['witness'];assert neg(neg(a))==a
    assert neg(neg(q(a)))&~q(a)!=0
    if persistent:
        assert a&~neg(neg(q(a)))==0
        assert neg(neg(imp(a,q(a))))==top
    return {'file':p.name,'worlds':n,'algebra_elements':len(U),'normality_instances':normality,'meet_instances':meet,'rho6_instances':len(U),'stable_input':a,'quantified_output':q(a),'double_negated_output':neg(neg(q(a))),'input_double_negated_persistence':persistent}
def commuting_model(p):
    d=load(p);up=d['up'];n=len(up);top=(1<<n)-1
    U=[a for a in range(1<<n)if all(not(a>>w&1)or up[w]&~a==0 for w in range(n))]
    assert U==d['upsets']
    def imp(a,b):return sum(1<<w for w in range(n)if up[w]&a&~b==0)
    def neg(a):return imp(a,0)
    def nn(a):return neg(neg(a))
    def modal(S,a):return sum(1<<w for w in range(n)if S[w]&~a==0)
    q=lambda a:modal(d['S'],a)
    r=lambda a:modal(d['T'],a)
    for op,key in [(q,'Q'),(r,'R')]:
        assert {str(a):op(a)for a in U}==d[key]
        assert op(0)==0 and op(top)==top
        for a in U:
            assert op(a)in U
            assert neg(op(neg(op(a))))&~a==0
            for b in U:
                assert op(a&b)==op(a)&op(b)
                assert op(imp(a,b))&~imp(op(a),op(b))==0
    for a in U:assert q(r(a))==r(q(a))
    a=d['witness'];assert nn(a)==a
    qr=nn(q(nn(r(a))));rq=nn(r(nn(q(a))))
    assert qr==d['NNQNNR']and rq==d['NNRNNQ']and qr!=rq
    return {'file':p.name,'worlds':n,'algebra_elements':len(U),'original_commutation_instances':len(U),'normality_instances_per_modality':len(U)**2,'regular_witness':a,'Booleanized_QR':qr,'Booleanized_RQ':rq,'scope':'Failure of generic Booleanized commutation, not a model of the entire native calculus.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);a=ap.parse_args()
    if not __debug__:raise RuntimeError('Assertions must be enabled')
    manifest=load(ROOT/'MANIFEST.sha256.json')
    for name,digest in manifest.items():assert sha(ROOT/name)==digest,('hash mismatch',name)
    results={'status':'PORTABLE_FINITE_CHECKS_PASS','manifest_files':len(manifest),'countermodels':[model(ROOT/'models/qs_countermodel.json',False),model(ROOT/'models/qs_persistent_countermodel.json',True)]}
    source_metrics={}
    for p in sorted((ROOT/'sources').glob('*.sites.json')):source_metrics[p.name]=metrics(read_tree(load(p)))
    assert source_metrics==load(ROOT/'results/selected_source_metrics.json')
    results['sources_checked']=source_metrics
    results['Booleanized_commutation_countermodel']=commuting_model(ROOT/'models/booleanized_commutation_countermodel.json')
    old=read_tree(load(ROOT/'baseline/sites218.json'));new=read_tree(load(ROOT/'sources/omit-zero-push.snapshot.sites.json'))
    assert replace(old,'11111',subtree(old,'111111'))==new
    ow=[x[1:]for x in write_sites(old)];nw=[x[1:]for x in write_sites(new)];assert ow[:4718]+ow[4737:]==nw
    table={}
    for line in (ROOT/'sources/omit-zero-push.tm').read_text().splitlines():
        if not line.strip()or line.startswith('#'):continue
        q,b,w,m,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert b in(0,1)and w in(0,1)and m in('L','R');assert(q,b)not in table;table[q,b]=(w,m,z)
    states={q for q,b in table};assert len(states)==218 and len(table)==436 and 254 not in states
    assert set(table)=={(q,b)for q in states for b in(0,1)}
    assert {z for w,m,z in table.values()}-states=={254}
    receipt=load(ROOT/'runtime/runtime.json');cases=load(ROOT/'runtime/cases.json')
    assert receipt['status']=='ALL_PRIMITIVE_INTERFACES_PROVED'
    assert receipt['driver_sha256']==sha(ROOT/'code/check_runtime_omit.py')
    assert receipt['table_sha256']==sha(ROOT/'sources/omit-zero-push.tm')
    assert receipt['sites_sha256']==sha(ROOT/'sources/omit-zero-push.snapshot.sites.json')
    assert len(cases)==receipt['cases']==6142
    assert sum(c['symbolic_steps']for c in cases)==receipt['symbolic_steps']==1511359
    assert min(c['duration'][0]for c in cases)==receipt['minimum_actual_steps']==12
    rows=write_sites(new);expected=[(i,positive)for i,(_,op,arg)in enumerate(rows)for positive in((False,True)if op=='CD'else(False,))]
    assert [(c['index'],c['positive'])for c in cases]==expected
    blank=load(ROOT/'results/omit-blank.json');assert blank['table_sha256']==receipt['table_sha256']
    assert blank['status']=='PASS'and blank['verified_steps']==312909 and blank['exact_complete_tape_equality']
    results['omit_variant']={'working_states':218,'source_deletion_exact':True,'runtime_cases':6142,'runtime_symbolic_steps':1511359,'blank_steps_receipted':312909,'scope':'Finite source/model checks and receipt consistency only; replay runtime and blank scripts for those independent proofs.'}
    if a.output:a.output.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()
