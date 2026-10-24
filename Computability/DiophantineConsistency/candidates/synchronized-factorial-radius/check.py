#!/usr/bin/env python3
"""Independent exact identities and ordinary-proof controls; no optimizer import."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import zipfile

HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[1]
REPO=RESEARCH.parents[1]
SYNC_SHA='ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf'
RADIUS_SHA='7782ba5510499c8925e3ca6895dc6ac71ecc6ea7cd85727fc95f6dc760dbdcc2'


def need(ok,message):
    if not ok:raise ValueError(message)


def digest(raw):return sha256(raw).hexdigest()


def load(name):return json.loads((HERE/name).read_text())


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    out=importlib.util.module_from_spec(spec);spec.loader.exec_module(out)
    return out


def source_authentication():
    pins=load('SOURCE_PINS.json');checked=[]
    archives={SYNC_SHA:REPO/pins['synchronized_archive'],RADIUS_SHA:REPO/pins['radius_archive']}
    for expected,path in archives.items():need(digest(path.read_bytes())==expected,'whole parent archive')
    for local,pin in pins['inherited_files'].items():
        actual=(HERE/'source'/local).read_bytes()
        need(digest(actual)==pin['sha256'],'source actual hash '+local)
        if 'archive_sha256' not in pin:continue
        with zipfile.ZipFile(archives[pin['archive_sha256']])as z:original=z.read(pin['member'])
        if local=='code/radius_verification_helpers.py':
            need(digest(original)==pin['original_sha256'],'original verifier source')
            text=original.decode().split('\ndef main():')[0]
            old="need(len(b.powers)==27,'changed power count; review new source')"
            new="need(len(b.powers)==25,'changed power count; review new source')"
            need(text.count(old)==1,'unique census-only change')
            original=text.replace(old,new).encode()
        need(actual==original,'full copied source bytes '+local);checked.append(local)
    build=load('BUILD.json')
    need(digest((HERE/'source/code/factorial_radius_power.py').read_bytes())==build['radius_builder_sha256'],'radius override binding')
    for name,wanted in build['sha256'].items():need(digest((HERE/name).read_bytes())==wanted,'complete generated artifact binding '+name)
    return checked


def actual_template_audit(b):
    """Expand only small local cuts, never the huge fixed majorant."""
    from audit_shared_power import P
    from review_synchronized_certificates import decode
    gates={out:(op,a,c)for(op,a,c),out in b.cache.items()}
    stops={a for(n,k),m in b.powers.items()for a in(n,k,m)}
    stops|={a for(n,k),m in b.binomials.items()for a in(n,k,m)}
    stops|={a for n,m in b.factorials.items()for a in(n,m)}
    stops|=set(b.common_index_parameters)
    def variable(atom):return P.coerce(atom[1])if atom[0]=='c'else P.var(atom[1])
    def expanded(atom,cut=stops):
        if atom[0]=='c' or atom in cut or atom not in gates:return variable(atom)
        op,a,c=gates[atom]
        left,right=expanded(a,cut),expanded(c,cut)
        return left+right if op=='add'else left*right
    def row(label):
        found=[r for r in b.rows if r['label']==label]
        need(len(found)==1,'one actual local row '+label)
        return found[0]
    def expression(label):
        out=P()
        for mon,c in decode(row(label)['terms']).items():
            term=P.coerce(c)
            for i in mon:term*=expanded(('v',i))
            out+=term
        return out
    count=0
    def check(label,want):
        nonlocal count
        need(expression(label).key()==want.key(),'actual scalar identity '+label);count+=1
    def named(name):
        found=[('v',i)for i,v in enumerate(b.variables)if v['name']==name]
        need(len(found)==1,'unique raw coordinate '+name)
        return variable(found[0])
    W,A,Z=map(variable,b.shared_parameters)
    # Z itself is an addition gate, so use its expanded positive recipe.
    Z=expanded(b.shared_parameters[2])
    check('shared.last_norm',A*A-1-W**3*(W+2)*Z*Z)
    U,V,B=map(variable,b.common_index_parameters)
    check('shared_index.norm',U*U-1-(A*A-1)*V*V)
    check('shared_index.B_mod_U',B-A-U*named('shared_index.Bquotient'))
    product=P.coerce(1)
    for j,(k,(x,y))in enumerate(b.shared_indices.items()):
        pre='index'+str(j)+'.';X,Y=variable(x),variable(y)
        S,R=named(pre+'S'),named(pre+'R');K=variable(k)
        check(pre+'index_at_most_Y',Y-K-named(pre+'YminusK'))
        check(pre+'norm1',X*X-1-(A*A-1)*Y*Y)
        check(pre+'norm3',S*S-1-(B*B-1)*R*R)
        check(pre+'S_mod_U',S-X-U*named(pre+'Squotient'))
        check(pre+'R_mod_4Y',R-K-4*Y*named(pre+'Rquotient'))
        product*=Y*Y
    check('shared_index.V_positive_product',V-product*(named('shared_index.Vquotient_minus1')+1))
    for j,(n,t)in enumerate(b.shared_bases.items()):
        N,T=variable(n),variable(t)
        check('base'+str(j)+'.T_definition',2*A*N-T-N*N-1)
    for j,((n,k),m)in enumerate(b.powers.items()):
        X,Y=map(variable,b.shared_indices[k]);T=variable(b.shared_bases[n])
        check('pow'+str(j)+'.power_congruence',X+variable(n)*Y-A*Y-variable(m)-T*named('pow'+str(j)+'.quotient'))
    q=variable(tuple(b.shared_binomial_data['radix_atom']))
    for j,((n,k),m)in enumerate(b.binomials.items()):
        pre='choose'+str(j)+'.';N,K=variable(n),variable(k);out=variable(m)
        # Read cached operation results without creating a missing definition.
        def op_lookup(op,a,c):
            hits=[result for(operator,l,r),result in b.cache.items()if operator==op and {l,r}=={a,c}]
            need(len(hits)==1,'unique requested cached operation')
            return hits[0]
        plus=op_lookup('add',tuple(b.shared_binomial_data['radix_atom']),('c',1))
        numerator=variable(b.powers[(plus,n)]);denominator=variable(b.powers[(tuple(b.shared_binomial_data['radix_atom']),k)])
        h,r,rs,os=[named(pre+v)for v in('high','remainder','rslack','oslack')]
        check(pre+'digit_division',numerator-denominator*(q*h+out)-r)
        check(pre+'remainder_bound',denominator-r-rs-1)
        check(pre+'digit_bound',q-out-os-1)
    factorials=[]
    for j,(n,f)in enumerate(b.factorials.items()):
        pre='factorial'+str(j)+'.';N,F=variable(n),variable(f)
        logs=[x for x in b.macro_log if x['macro']=='factorial'and tuple(x['n'])==n]
        need(len(logs)==1 and logs[0]['radius_rule']=='output*n^2','radius macro identity')
        radius=tuple(logs[0]['radius'])
        need(expanded(radius,stops-{radius}).key()==(F*N*N).key(),'exact radius output*n^2')
        # The upper argument is itself a stop. Expand just its defining sum.
        candidates=[(upper,k,out)for(upper,k),out in b.binomials.items()if k==n and
                    expanded(upper,stops-{upper,radius}).key()==(F*N*N+N).key()]
        need(len(candidates)==1,'one actual radius binomial')
        upper,k,out=candidates[0];C=variable(out)
        powers=[m for(base,k),m in b.powers.items()if k==n and
                expanded(base,stops-{base,radius}).key()==(F*N*N+1).key()]
        need(len(powers)==1,'one actual numerator power')
        Pn=variable(powers[0]);r,s=named(pre+'remainder'),named(pre+'slack')
        check(pre+'ceiling',Pn+C-C*F-r-1)
        check(pre+'remainder_bound',C-r-s-1)
        factorials.append(dict(input=list(n),output=list(f),radius=list(radius),zero_output_not_assumed_away=True))
    return dict(exact_local_scalar_rows=count,factorial_templates=factorials,
                power_calls=len(b.powers),index_groups=len(b.shared_indices),distinct_bases=len(b.shared_bases))


def dependency_audit(b):
    """Input licenses use zero bounds for candidate factorial/binomial outputs."""
    definitions={out:(op,a,c)for(op,a,c),out in b.cache.items()}
    lower={('v',i):0 for i in range(len(b.variables))}
    leaves={('v',i):{i}for i in range(len(b.variables))if('v',i)not in definitions}
    def lb(a):return a[1]if a[0]=='c'else lower[a]
    def deps(a):return set()if a[0]=='c'else leaves[a]
    for result,(op,a,c)in definitions.items():
        lower[result]=lb(a)+lb(c)if op=='add'else lb(a)*lb(c)
        leaves[result]=deps(a)|deps(c)
    private={i for i,v in enumerate(b.variables)if ('v',i)not in definitions and
             (v['name'].startswith(('shared.','shared_index.','index','base'))or
              (v['name'].startswith('pow')and v['name'].endswith('.quotient')))}
    licensed=[k for n,k in b.powers]
    licensed+=[a for n,k in b.binomials for a in(n,k)]
    licensed+=list(b.factorials)
    arguments=licensed+[n for n,k in b.powers]
    need(all(not(deps(a)&private)for a in arguments),'private Pell witness in an arithmetic argument')
    need(all(lb(a)>=1 for a in licensed),'positive exponent/binomial/factorial input lacks a syntactic lower bound')
    need(all(lb(f)==0 for f in b.factorials.values()),'factorial candidate was assumed positive')
    zero_bases={n for n,k in b.powers if lb(n)==0}
    need(zero_bases<=set(b.shared_bases),'base without its natural T definition')
    return dict(syntactically_positive_input_occurrences=len(licensed),
                power_base_atoms_with_positive_syntactic_bound=len(set(b.shared_bases)-zero_bases),
                power_base_atoms_proved_positive_by_their_exact_T_row=[list(n)for n in sorted(zero_bases)],
                base_positivity_argument='The independently matched row 2*A*n=T+n^2+1 contradicts n=0 for natural T; no factorial meaning is used.',
                private_pell_inputs_excluded=len(private),
                candidate_factorial_output_lower_bound=0,
                factorial_radius_self_reference='Only the explicitly proved local candidate-output radius is permitted; no Pell coordinate enters an arithmetic input.')


def rejected(thunk,label):
    try:thunk()
    except(ValueError,RuntimeError,KeyError,TypeError,IndexError):return label
    raise ValueError('corruption accepted: '+label)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    authenticated=source_authentication()
    code=HERE/'source/code';up=HERE/'source/provenance/upstream'
    sys.path[:0]=[str(code),str(up),str(RESEARCH/'tools')]
    from review_synchronized_certificates import full_sos,contraction,math_controls
    from review_shared_pell608 import factorial_controls
    import radius_verification_helpers as helper
    import synchronized_builder as compiler
    from direct_source_factored import source_pair_calculus
    from factorial_radius_power import FactorialRadiusPowerBuilder
    compiler.source_pair_calculus=source_pair_calculus
    class Checked(compiler.DeferredBinomialMixin,FactorialRadiusPowerBuilder):pass
    b,cert=compiler.construct(Checked,json.loads((up/'wire_eliminated_source.json').read_text()))
    packet=load('source850/raw_builder.json')
    normalized=lambda x:json.loads(json.dumps(x))
    need(normalized(b.variables)==packet['variables']and normalized(b.rows)==packet['rows']and normalized(b.macro_log)==packet['macro_log'],'full raw reconstruction')
    need(normalized(cert)==load('source850/majorant_certificate.json'),'literal majorant certificate')
    source=load('source850/equation.json')
    verifier=module('independent_affine',HERE/'source/verification/verify_affine_independent.py')
    raw_check=verifier.check(packet,source)
    checks={};metrics={}
    for name in ['source850','natural573','natural509','natural502']:
        eq=load(name+'/equation.json');pol=load(name+'/expanded_polynomial.json')
        metrics[name]=full_sos(eq,pol)
        if name!='source850':checks[name]=contraction(source,eq,load(name+'/elimination_certificate.json'))
    controls=[]
    bad=deepcopy(source);bad['residuals'][0]['terms'][0][0]*=-1
    controls.append(rejected(lambda:verifier.check(packet,bad),'changed affine export coefficient'))
    badraw=deepcopy(packet);r=next(r for r in badraw['rows']if r.get('gate')is not None)
    for term in r['terms']:
        if term[1]==[r['gate']]:term[0]=2;break
    controls.append(rejected(lambda:verifier.check(badraw,source),'nonmonic raw definition'))
    badcert=load('natural502/elimination_certificate.json');badcert['steps'][0]['restoration'][0][0]*=-1
    controls.append(rejected(lambda:contraction(source,load('natural502/equation.json'),badcert),'negative restoring polynomial'))
    badpol=load('natural502/expanded_polynomial.json');badpol['terms'][0][0]+=1
    controls.append(rejected(lambda:full_sos(load('natural502/equation.json'),badpol),'changed final coefficient'))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),authenticated_copied_sources=authenticated,
        metrics=metrics,raw_affine_check=raw_check,contractions=checks,
        actual_source_shape=helper.source_change(True),majorant=helper.majorant(cert),
        actual_frame=helper.frame_audit(b,cert),actual_product=helper.product_index_audit(b),
        actual_local_templates=actual_template_audit(b),actual_dependency_licenses=dependency_audit(b),
        factorial_controls=factorial_controls(),shared_math_controls=math_controls(),
        corruption_controls=controls,
        external_independent_review_tools={name:digest((RESEARCH/'tools'/name).read_bytes())for name in
                                          ['review_synchronized_certificates.py','review_shared_pell608.py']},
        scope='Complete coefficient/row certificates and finite controls; unbounded semantic proof in PROOF.md. No consistency proof, Lean build or internal ZFC claim.')
    rendered=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(rendered)
    print(rendered,end='')


if __name__=='__main__':main()
