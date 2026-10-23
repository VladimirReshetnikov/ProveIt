#!/usr/bin/env python3
"""Reproduce finite certificates; this does not decide or test Con(ZFC).

Python standard library only. The mathematical reductions and the inherited
compiler/calibration theorem are described in report/congruence_carriers.pdf.
"""
from pathlib import Path
from tempfile import TemporaryDirectory
from collections import Counter
import gzip, hashlib, json, os, shutil, subprocess, sys, time

ROOT=Path(__file__).resolve().parent

def require(condition,message):
    if not condition:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def gitsha(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def run(label,script,args=(),optimized=False):
    command=[sys.executable]
    if optimized: command.append('-O')
    command.extend([str(ROOT/script),*map(str,args)])
    result=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    if result.returncode:
        raise RuntimeError(label+'\n'+result.stdout+'\n'+result.stderr)
    print('PASS '+label,flush=True)
    return {'label':label,'returncode':result.returncode}

def authenticate_sources():
    ledger=json.loads((ROOT/'provenance/SOURCE_BLOBS.json').read_text())
    for entry in ledger['files']:
        data=(ROOT/entry['local']).read_bytes()
        require(len(data)==entry['expected_bytes'],'Source size '+entry['local'])
        require(gitsha(data)==entry['git_blob_sha1'],'Source Git identity '+entry['local'])
        require(hashlib.sha256(data).hexdigest()==entry['sha256'],'Source hash '+entry['local'])
    print('PASS '+str(len(ledger['files']))+' primary upstream Git blobs',flush=True)
    return len(ledger['files'])

def check_compact_tuple():
    folder=ROOT/'coefficients/compact44'
    manifest=json.loads((folder/'COEFFICIENT_BINDING.json').read_text())
    values={}
    for entry in manifest['materialization']['files']:
        compressed=(folder/entry['file']).read_bytes()
        raw=gzip.decompress(compressed)
        require(hashlib.sha256(compressed).hexdigest()==entry['gzip_sha256'],'Compact gzip')
        require(hashlib.sha256(raw).hexdigest()==entry['sha256'],'Compact raw')
        require(len(raw)==entry['raw_bytes'],'Compact bytes')
        value=int.from_bytes(raw,'little')
        require(value.bit_length()==entry['bits'],'Compact bit length')
        values[entry['port']]=value
    beta=values['beta']; MC=values['MC']; MF=values['MF_source']; K=values['K']
    B=1<<590069
    require(beta==B-1 and beta%3==1,'Compact beta')
    require(0<MC<beta and beta<MF<2*beta and K>0,'Compact inequalities')
    require(MC%4==2 and (MF-beta)%8==4,'Compact congruences')
    require(MC.bit_count()+(MF-beta).bit_count()==590069,'Compact populations')
    binding=json.loads((ROOT/'positive/ACTIVE_BINDING.json').read_text())
    require(sha(ROOT/'positive'/binding['whole_binding'])==binding['whole_binding_sha256'],
            'Compact active manifest')
    for entry in binding['ports'].values():
        data=(ROOT/'positive'/entry['gzip_payload']).read_bytes()
        require(hashlib.sha256(data).hexdigest()==entry['gzip_sha256'],'Active gzip')
        require(hashlib.sha256(gzip.decompress(data)).hexdigest()==entry['sha256'],'Active port')
    for entry in binding['polynomials']:
        require(sha(ROOT/'positive'/entry['path'])==entry['sha256'],'Active polynomial')
    # Rebuild in a temporary directory; preserved source files are not changed.
    with TemporaryDirectory(prefix='con-zfc-compact-') as td:
        temp=Path(td)
        for name in ['build_coefficients.py','k215_transitions.json']:
            shutil.copyfile(folder/name,temp/name)
        r=subprocess.run([sys.executable,str(temp/'build_coefficients.py')],
                         text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        require(r.returncode==0,'Compact rebuild failed: '+r.stderr)
        rebuilt=json.loads((temp/'COEFFICIENT_BINDING.json').read_text())
        a={k:v for k,v in rebuilt.items() if k!='materialization'}
        b={k:v for k,v in manifest.items() if k!='materialization'}
        require(a==b,'Compact recipe or finite interface mismatch')
        for entry in manifest['materialization']['files']:
            raw=gzip.decompress((temp/entry['file']).read_bytes())
            require(hashlib.sha256(raw).hexdigest()==entry['sha256'],'Compact rebuilt integer')
        # Python/zlib versions can change gzip headers while preserving integers.
        compressed_identical=all((temp/e['file']).read_bytes()==(folder/e['file']).read_bytes()
                                 for e in manifest['materialization']['files'])
    print('PASS complete compact tuple, active bindings, and numerical rebuild',flush=True)
    return {'ports':4,'raw_bytes':295388,'gzip_bytes':9445,
            'rebuilt_raw_integers_identical':True,
            'rebuilt_gzip_bytes_identical_in_this_runtime':compressed_identical}

def check_circuits_and_rebuild():
    names=['p13_degree34.json','p12_product_split2.json','p12_sos_split2.json']
    original={n:(ROOT/'positive'/n).read_bytes() for n in names}
    run('rebuild P13','positive/build13.py')
    run('rebuild P12 and SOS companion','positive/build12.py')
    for name,data in original.items():
        require((ROOT/'positive'/name).read_bytes()==data,'Nonidentical DAG rebuild '+name)
    p=json.loads(original['p12_product_split2.json'])
    s=json.loads(original['p12_sos_split2.json'])
    require(p['witnesses']==s['witnesses'] and p['fixed_numerals']==s['fixed_numerals'],
            'Companion domain')
    require(p['residuals']==s['residuals']==['A0','A1','N'],'Companion residuals')
    def prefix(packet):
        needed=set(packet['residuals'])
        for name,op,x,y in reversed(packet['source']):
            if name in needed: needed.update((x,y))
        return [row for row in packet['source'] if row[0] in needed]
    core=prefix(p)
    require(core==prefix(s) and len(core)==98,'Identical audited residual cone')
    env={r:('var',r) for r in s['residuals']}
    for name,op,x,y in s['source'][len(core):]:
        require(x in env and y in env,'Companion suffix reference')
        env[name]=(op,env[x],env[y])
    sq=lambda x:('*',('var',x),('var',x))
    desired=('+',('+',sq('A0'),sq('A1')),sq('N'))
    # Commutative operands may be canonically swapped by the builder.
    def canonical(x):
        if x[0]=='var':return x
        a,b=canonical(x[1]),canonical(x[2])
        return (x[0],*sorted((a,b),key=repr)) if x[0] in ('+','*') else (x[0],a,b)
    require(canonical(env[s['output']])==canonical(desired),'Companion SOS identity')
    require(len(s['source'])==103 and s['exact_degree']==172,'Companion metrics')
    print('PASS byte-identical DAGs and exact SOS companion finalizer',flush=True)

def main():
    started=time.monotonic()
    sources=authenticate_sources()
    compact=check_compact_tuple()
    check_circuits_and_rebuild()
    runs=[]
    for optimized in (False,True):
        suffix=' (-O)' if optimized else ''
        for label,path in [('P13 exact algebra','positive/check13.py'),
                           ('P12 exact algebra','positive/check12.py'),
                           ('integer eliminations','integer/build_reductions.py'),
                           ('integer coefficient/source dossier','integer/coefficients_source/verify_dossier.py')]:
            runs.append(run(label+suffix,path,optimized=optimized))
    # The preserved historical independent verifier explicitly requires debug mode.
    runs.append(run('independent integer-tuple decoder',
        'integer/coefficients_source/coefficients/verify_independent.py',
        ['--payloads',ROOT/'integer/coefficients_source/generated_payloads']))
    result={'status':'PASS','primary_upstream_git_blobs':sources,
            'compact_tuple':compact,'checks':runs,
            'seconds':round(time.monotonic()-started,3),
            'proof_boundary':'Finite algebra, degrees, circuit metrics, coefficient bytes and source identities. '
              'Ordinary mathematical reductions are in the paper; the native compiler and consistency calibration '
              'are inherited. No consistency search or new end-to-end proof-assistant certificate.'}
    (ROOT/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
