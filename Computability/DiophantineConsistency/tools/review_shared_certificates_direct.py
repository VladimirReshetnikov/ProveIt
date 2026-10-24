#!/usr/bin/env python3
"""Independent read-only provenance/whole-polynomial audit of shared direct.

No intake program is imported.  The companion note supplies ordinary
unbounded reasoning; the scoped scratch replay is recorded separately.
"""
from collections import defaultdict
import hashlib,json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
HOME=Path('/tmp/dioph-new-arrivals-751bc067e2/ConZFC_Shared_Certificates_2026-10-24/con_zfc_shared_certificates')


def need(ok,text):
    if not ok:raise RuntimeError(text)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    arrival=next(r for r in json.loads((HOME.parent.parent/'ARRIVALS.json').read_text())if 'Shared_Certificates' in r['archive'])
    need(sha((REPO/arrival['archive']).read_bytes())==arrival['sha256'],'actual incoming archive')
    provenance=json.loads((HOME/'provenance/SOURCES.json').read_text())
    sources=[]
    for item in provenance['direct_inherited_texts']:
        raw=(HOME/item['local_path']).read_bytes()
        need(len(raw)==item['delivered_bytes']and sha(raw)==item['delivered_sha256'],'delivered source digest')
        if item['text_relation']=='byte-identical':upstream=raw
        else:
            need(item['text_relation']=='local copy has exactly one additional trailing LF byte'and raw.endswith(b'\n'),'specified exact LF relation')
            upstream=raw[:-1]
        need(len(upstream)==item['upstream_bytes']and sha(upstream)==item['upstream_sha256'],'upstream exact source relation')
        need(hashlib.sha1(b'blob '+str(len(upstream)).encode()+b'\0'+upstream).hexdigest()==item['git_blob_sha1'],'upstream Git blob')
        sources.append(dict(path=item['local_path'],relation=item['text_relation']))
    results={}
    for folder,key,expected in [('direct','affine',(3614,2954,15996,127778545)),('direct/small_height','retained',(6183,5523,17430,1993))]:
        directory=HOME/folder
        eqraw=(directory/'equation.json').read_bytes();poraw=(directory/'expanded_polynomial.json').read_bytes()
        eq,poly=json.loads(eqraw),json.loads(poraw)
        value=defaultdict(int);used=set();n=len(eq['variables'])
        for row in eq['residuals']:
            need(len({tuple(m)for c,m in row['terms']})==len(row['terms']),'canonical residual monomials')
            for c,m in row['terms']:
                need(type(c)is int and c and m==sorted(m)and len(m)<=2 and all(type(i)is int and 0<=i<n for i in m),'literal quadratic row')
                used.update(m)
            for a,ma in row['terms']:
                for b,mb in row['terms']:
                    value[tuple(sorted(ma+mb))]+=a*b
        want={m:c for m,c in value.items()if c};got={tuple(m):c for c,m in poly['terms']}
        need(want==got and len(got)==len(poly['terms'])and used==set(range(n)),'whole SOS polynomial/all variables')
        census=(n,len(eq['residuals']),len(got),max(map(abs,got.values())))
        need(census==expected and max(map(len,got))==4,'exact displayed metrics')
        build=json.loads((directory/'BUILD.json').read_text())
        need(build['sha256']['equation.json']==sha(eqraw)and build['sha256']['expanded_polynomial.json']==sha(poraw),'built literal hashes')
        results[key]=dict(variables=n,quadratic_rows=census[1],quartic_terms=census[2],coefficient_height=census[3],
                          exact_degree=4,all_variables_live=True,equation_sha256=sha(eqraw),expanded_sha256=sha(poraw))
    replay=json.loads(Path('/tmp/proofs62ff-shared-direct-replay/REPLAY.json').read_text())
    need(replay['status']=='PASS'and len(replay['results'])==16 and replay['byte_identical_rebuilt_files']==6 and all(r['returncode']==0 for r in replay['results']),'all sixteen scoped stages')
    result=dict(status='PASS',python_optimization=sys.flags.optimize,arrival=arrival,authenticated_sources=sources,
                literal_results=results,scoped_replay=replay,
                ordinary_review='Shared factorial cancellation, heterogeneous bounds, source/calculus elimination, sharp carrier, positive-power inventory, and nonnegative affine restoration reviewed in companion note.',
                scope='Incoming direct component only; no coordinate-family/native recalibration, inherited program execution, Lean build, or internal-ZFC proof.')
    output=ROOT/'PROPOSAL_REVIEW_SHARED_CERTIFICATES_DIRECT.json'
    if sys.flags.optimize:output=output.with_name(output.stem+'_OPTIMIZED.json')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS shared direct source/Gitblob pins, complete quartics and scoped16stage scratch replay')


if __name__=='__main__':main()
