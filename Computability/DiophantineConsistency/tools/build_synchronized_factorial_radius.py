#!/usr/bin/env python3
"""Compose the self-bounding factorial with the frozen synchronized engine."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys
import zipfile

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
DEST=ROOT/'candidates/synchronized-factorial-radius'
ARCHIVE=REPO/'docs/incoming/ConZFC_Synchronized_Certificates_2026-10-24.zip'
SHA='ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf'
RADIUS_ARCHIVE=REPO/'docs/incoming/ConZFC_Shared_Pell_608_2026-10-23.zip'
RADIUS_SHA='7782ba5510499c8925e3ca6895dc6ac71ecc6ea7cd85727fc95f6dc760dbdcc2'
COPIES=['code/'+n+'.py'for n in ['synchronized_builder','shared_power','shared_product_power',
        'shared_index_power','direct_source','direct_source_factored','affine_contract',
        'audit_shared_power','audit_shared_product']]+[
        'provenance/upstream/build_equation.py','provenance/upstream/direct_calculus.py',
        'provenance/upstream/wire_eliminated_source.json']


def need(ok,text):
    if not ok:raise RuntimeError(text)


def sha(raw):return sha256(raw).hexdigest()


def encoded(obj):return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()


def source_files():
    need(sha(ARCHIVE.read_bytes())==SHA and sha(RADIUS_ARCHIVE.read_bytes())==RADIUS_SHA,'whole reviewed archives')
    files={};pins={}
    with zipfile.ZipFile(ARCHIVE)as z:
        for name in COPIES:
            raw=z.read('con_zfc_synchronized_certificates/'+name)
            files['source/'+name]=raw;pins[name]=dict(archive_sha256=SHA,member='con_zfc_synchronized_certificates/'+name,sha256=sha(raw),changes=[])
        original=z.read('con_zfc_synchronized_certificates/code/verify_synchronized.py')
        # Retain only the audited generic functions; the old main chooses its
        # own constructor and hardcodes the old 27-call census.
        text=original.decode();need(text.count('\ndef main():')==1,'generic helper boundary')
        text=text.split('\ndef main():')[0]
        before="need(len(b.powers)==27,'changed power count; review new source')"
        after="need(len(b.powers)==25,'changed power count; review new source')"
        need(text.count(before)==1,'one reviewed power census assertion')
        text=text.replace(before,after)
        raw=text.encode();files['source/code/radius_verification_helpers.py']=raw
        pins['code/radius_verification_helpers.py']=dict(archive_sha256=SHA,
            member='con_zfc_synchronized_certificates/code/verify_synchronized.py',
            original_sha256=sha(original),sha256=sha(raw),
            changes=['Retain generic function prefix before main().',[before,after]])
        files['LICENSE.upstream']=z.read('con_zfc_synchronized_certificates/LICENSE')
    with zipfile.ZipFile(RADIUS_ARCHIVE)as z:
        name='con-zfc-shared-pell-2026-10-23/tests/verify_affine_independent.py'
        raw=z.read(name);files['source/verification/verify_affine_independent.py']=raw
        pins['verification/verify_affine_independent.py']=dict(archive_sha256=RADIUS_SHA,member=name,sha256=sha(raw),changes=[])
    own=DEST/'source/code/factorial_radius_power.py'
    pins['code/factorial_radius_power.py']=dict(author='Local composition of the reviewed radius lemma.',sha256=sha(own.read_bytes()))
    files['SOURCE_PINS.json']=encoded(dict(synchronized_archive=str(ARCHIVE.relative_to(REPO)),synchronized_archive_sha256=SHA,
        radius_archive=str(RADIUS_ARCHIVE.relative_to(REPO)),radius_archive_sha256=RADIUS_SHA,
        inherited_files=pins,semantic_change='Only factorial radius changes from (n+2)^(n+2) to output*n^2; factored source, shared frame/product index and deferred binomials unchanged.'))
    return files


def build():
    code=DEST/'source/code';up=DEST/'source/provenance/upstream'
    sys.path[:0]=[str(code),str(up)]
    import synchronized_builder as compiler
    from direct_source_factored import source_pair_calculus
    from factorial_radius_power import FactorialRadiusPowerBuilder
    from affine_contract import contract,independent_verify,polynomial_and_metrics
    compiler.source_pair_calculus=source_pair_calculus
    class SynchronizedRadiusBuilder(compiler.DeferredBinomialMixin,FactorialRadiusPowerBuilder):pass
    rawsource=(up/'wire_eliminated_source.json').read_bytes()
    b,cert=compiler.construct(SynchronizedRadiusBuilder,json.loads(rawsource))
    equation,polynomial,metrics=b.export(sha(rawsource),'synchronized11.self_bounding_factorial',inline_affine=True)
    need((len(b.powers),len(b.shared_indices),len(b.shared_bases),len(b.binomials),len(b.factorials))==(25,20,8,14,2),'actual new sharing census')
    raw=dict(variables=b.variables,rows=b.rows,macro_log=b.macro_log,
             powers=[dict(base=n,exponent=k,output=m)for(n,k),m in b.powers.items()],
             shared_parameters=b.shared_parameters,common_index_parameters=b.common_index_parameters,
             shared_indices=[dict(exponent=k,X=X,Y=Y)for k,(X,Y)in b.shared_indices.items()],
             shared_binomial_data=b.shared_binomial_data)
    files={};census={}
    def save(folder,eq,poly,extra):
        census[folder]=eq['metrics']
        for name,obj in dict({'equation.json':eq,'expanded_polynomial.json':poly},**extra).items():files[folder+'/'+name]=encoded(obj)
    save('source850',equation,polynomial,{'raw_builder.json':raw,'majorant_certificate.json':cert})
    for cap,folder in [(4,'natural573'),(16,'natural509'),(64,'natural502')]:
        child,trace=contract(equation,support_cap=cap,terminal_quadratic=True)
        review=independent_verify(equation,child,trace)
        poly,_=polynomial_and_metrics(child['residuals'],len(child['variables']))
        save(folder,child,poly,{'elimination_certificate.json':trace,'CONTRACTION_CHECK.json':review})
    files['CENSUS.json']=encoded(dict(status='PASS',metrics=census,
        power_calls=25,exponent_groups=20,distinct_bases=8,binomial_calls=14,factorial_calls=2,
        fixed_majorant_exponent=cert['emitted_exponent']))
    files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=sha(Path(__file__).read_bytes()),
        radius_builder_sha256=sha((code/'factorial_radius_power.py').read_bytes()),
        sha256={name:sha(data)for name,data in files.items()},
        scope='Exact new radius method and frozen source/frame/contraction engine; ordinary proof and independent CHECK are separate. No Lean.'))
    return files,census


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    copies=source_files()
    for name,raw in copies.items():
        target=DEST/name
        if args.check:need(target.read_bytes()==raw,'authenticated source copy '+name)
        else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
    generated,census=build()
    for name,raw in generated.items():
        target=DEST/name
        if args.check:need(target.read_bytes()==raw,'deterministic new equation '+name)
        else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,metrics={k:{f:m[f]for f in
          ['variables','quadratic_rows','exact_degree','expanded_monomials','max_abs_expanded_coefficient']}for k,m in census.items()}),indent=2))


if __name__=='__main__':main()
