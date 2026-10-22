#!/usr/bin/env python3
"""Focused independent baseline/candidate checks; never writes into ProveIt."""
from pathlib import Path
import argparse, fcntl, hashlib, json, re, shutil, subprocess, time

HERE=Path(__file__).resolve().parent
ORDER=[('K230S','KCode230'),('K230L','Codes230'),
       ('K215F','Codes222'),('K215F','Thm222'),('K215F','DomRho8'),
       ('K215F','ThmDom'),('K215F','EnumPerm'),('K215F','L1_SoundPerm'),
       ('K215F','L1_CompPerm'),('K215F','SeedPerm'),('K215F','Audit')]

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def verify_sources():
    provenance=json.loads((HERE/'source_provenance.json').read_text())
    for entry in provenance['inputs']:
        assert sha(HERE/entry['output'])==entry['sha256'],entry['output']
    metrics=json.loads((HERE/'source_metrics.json').read_text())
    for name,expected in metrics.items():
        before=(HERE/'baseline/K215F'/f'{name}.v').read_text()
        after=(HERE/'candidate/K215F'/f'{name}.v').read_text()
        for tag,text in [('before',before),('after',after)]:
            assert len(text.encode())==expected[tag+'_bytes']
            assert len(text.splitlines())==expected[tag+'_lines']
        # Check complete declaration headers, including binder order and types.
        for declaration in re.finditer(r'^(?:Lemma|Theorem)\s+(\w+)\b.*?(?=\nProof\.)',before,re.M|re.S):
            lemma=declaration.group(1)
            candidate=re.search(r'^(?:Lemma|Theorem)\s+'+lemma+r'\b.*?(?=\nProof\.)',after,re.M|re.S)
            assert candidate and declaration.group(0)==candidate.group(0),lemma
        template=HERE/'templates'/f'{name}.v'
        generated=(f'(** k225-formal/rocqperm/{name}.v (SHA256 {sha(template)}) under namespace K215F. *)\n'
                   +template.read_text().replace('From NS Require','From K215F Require'))
        assert generated==after,name+' generation'

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path)
    ap.add_argument('--verify-only',action='store_true')
    ap.add_argument('--coqc',default='coqc')
    ap.add_argument('--coqchk',default='coqchk')
    ap.add_argument('--lane',choices=['both','baseline','candidate'],default='both')
    a=ap.parse_args()
    verify_sources()
    if a.verify_only:
        print('PASS: source identities, metrics, declaration headers and template generation.')
        return
    if a.out is None: ap.error('--out is required unless --verify-only is used')
    out=a.out.resolve()
    if out.exists(): raise SystemExit('Use a fresh output directory.')
    out.mkdir(parents=True)
    version=subprocess.check_output([a.coqc,'--version'],text=True)
    (out/'toolchain.log').write_text(version)
    # The distributed inputs retain the production namespace spelling. This
    # exact textual adaptation is required only for Coq 8.18 compatibility.
    normalize='version 8.' in version
    results={'toolchain':version,'namespace_normalization':normalize,'lanes':{}}
    lanes=['baseline','candidate'] if a.lane=='both' else [a.lane]
    for lane in lanes:
        work=out/lane
        shutil.copytree(HERE/lane,work)
        if normalize:
            for p in work.rglob('*.v'):
                p.write_text(p.read_text().replace('From Stdlib Require','From Coq Require'))
        flags=['-Q',str(work/'K230S'),'K230S','-Q',str(work/'K230L'),'K230L',
               '-Q',str(work/'K215F'),'K215F']
        records=[]
        for ns,name in ORDER:
            src=work/ns/(name+'.v')
            cmd=[a.coqc,*flags,str(src)]
            log=out/(lane+'-'+ns+'.'+name+'.log')
            print(lane,ns+'.'+name,flush=True)
            with open('/tmp/proveit-k215-proof-build.lock','a') as lock:
                fcntl.flock(lock,fcntl.LOCK_EX)
                start=time.perf_counter()
                proc=subprocess.run(cmd,cwd=work,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
                elapsed=time.perf_counter()-start
            log.write_text(proc.stdout)
            records.append({'module':ns+'.'+name,'exit_code':proc.returncode,
                'seconds':elapsed,'source_sha256':sha(src),'log':log.name})
            results['lanes'][lane]={'modules':records}
            (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
            if proc.returncode: raise SystemExit(proc.stdout)
            if name=='Audit':
                expected=9 if lane=='baseline' else 12
                assert proc.stdout.count('Closed under the global context')==expected,proc.stdout
                assert 'Axioms:' not in proc.stdout,proc.stdout
                results['lanes'][lane]['audit_closed_reports']=expected
        cmd=[a.coqchk,*flags,'K215F.Audit']
        with open('/tmp/proveit-k215-proof-build.lock','a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            start=time.perf_counter()
            proc=subprocess.run(cmd,cwd=work,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            elapsed=time.perf_counter()-start
        (out/(lane+'-coqchk.log')).write_text(proc.stdout)
        results['lanes'][lane]['coqchk']={'exit_code':proc.returncode,'seconds':elapsed}
        (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
        if proc.returncode: raise SystemExit(proc.stdout)
    print('PASS: focused source closures and recursive kernel checks.',flush=True)

if __name__=='__main__': main()
