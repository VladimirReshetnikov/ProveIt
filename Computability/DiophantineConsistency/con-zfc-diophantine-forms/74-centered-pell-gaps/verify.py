#!/usr/bin/env python3
"""Reproduce finite algebra and bindings; does not decide consistency."""
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:raise ValueError(message)

def run(args,cwd):
    r=subprocess.run([sys.executable,*args],cwd=cwd,capture_output=True,text=True)
    if r.returncode:raise RuntimeError(r.stdout+'\n'+r.stderr)
    return r.stdout

def check_source_hashes():
    ledger=json.loads((ROOT/'upstream/FETCH_LEDGER.json').read_text())
    for e in ledger['files']:
        raw=(ROOT/e['file']).read_bytes()
        require(hashlib.sha256(raw).hexdigest()==e['sha256'],'source SHA256: '+e['file'])
        require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==e['git_blob_sha1'],'source Git blob: '+e['file'])
    return len(ledger['files'])

def domain_checks():
    from evaluate import coefficients,evaluate
    fixed=coefficients();parent=json.loads((ROOT/'circuits/positive12_product.json').read_text())
    count=0
    for kind in ['natural12','integer36']:
        p=json.loads((ROOT/'circuits'/(kind+'.json')).read_text())
        require(p['operations']==len(p['source']),'domain operation count')
        require(p['exact_degree']==(110 if kind=='natural12' else 220),'domain degree')
        # The actual graph consists of explicit input lifts followed by an exact
        # copy of the parent graph with only witness leaves renamed.
        prefix=p['source'][:-len(parent['source'])];suffix=p['source'][-len(parent['source']):]
        mapping={v:prefix[7*j+6][0] if kind=='integer36' else prefix[j][0]
                 for j,v in enumerate(parent['witnesses'])}
        expected=[[name,op,mapping.get(a,a),mapping.get(b,b)] for name,op,a,b in parent['source']]
        require(suffix==expected,'domain graph substitution')
        for seed in range(12):
            if kind=='natural12':
                values={v+'_nat':seed+j for j,v in enumerate(parent['witnesses'])}
                old={v:values[v+'_nat']+1 for v in parent['witnesses']}
            else:
                values={v+'_'+s:((seed+3*j+k)%11)-5 for j,v in enumerate(parent['witnesses']) for k,s in enumerate('abc')}
                old={v:1+values[v+'_a']**2+values[v+'_b']**2+values[v+'_c']*(values[v+'_c']+1) for v in parent['witnesses']}
            require(min(old.values())>=1,'positive lift')
            require(evaluate(p,values,fixed,1000003)==evaluate(parent,old,fixed,1000003),'domain numerical comparison')
            count+=1
    return {'exact_graph_substitutions':2,'modular_diagnostic_assignments':count,
            'mathematical_surjectivity':'Legendre three-square theorem; proof in report'}

def main():
    source_count=check_source_hashes()
    evidence={}
    with tempfile.TemporaryDirectory(prefix='centered-pell-replay-') as td:
        tmp=Path(td)
        # Regenerate new graphs from sources, isolated from the release.
        for name in ['build.py','build_domains.py']:
            shutil.copy2(ROOT/name,tmp/name)
        run(['build.py'],tmp);run(['build_domains.py'],tmp)
        for path in (tmp/'circuits').glob('*.json'):
            require(path.read_bytes()==(ROOT/'circuits'/path.name).read_bytes(),'circuit rebuild '+path.name)
        p13=tmp/'positive13';p13.mkdir()
        for name in ['build13.py','dag.py']:
            shutil.copy2(ROOT/'positive13'/name,p13/name)
        run(['build13.py'],p13)
        require((p13/'p13_degree30.json').read_bytes()==(ROOT/'positive13/p13_degree30.json').read_bytes(),'13 graph rebuild')
        # Reconstruct all four numerals from the literal machine/tile recipe.
        native=tmp/'native';native.mkdir()
        for name in ['build_coefficients.py','k215_transitions.json']:
            shutil.copy2(ROOT/'upstream'/name,native/name)
        run(['build_coefficients.py'],native)
        binding=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text())
        sizes=[]
        for ent in binding['materialization']['files']:
            name=Path(ent['file']).name
            fresh=gzip.decompress((native/'coefficients'/name).read_bytes())
            supplied=gzip.decompress((ROOT/'coefficients'/name).read_bytes())
            require(fresh==supplied,'reconstructed numeral '+name)
            sizes.append({'port':ent['port'],'raw_bytes':len(fresh),'sha256':hashlib.sha256(fresh).hexdigest()})
        evidence['reconstructed_fixed_numerals']=sizes
        evidence['regenerated_circuits']=5
    out=run(['checks/check12.py','--root',str(ROOT),'--output',str(ROOT/'checks/CHECK12.json')],ROOT)
    evidence['centered12']=json.loads(out)
    evidence['adaptive13']=json.loads(run(['positive13/check13.py'],ROOT))
    evidence['independent_norm_identities']=json.loads(run(['checks/check_centered_norm.py'],ROOT))
    evidence['domain_companions']=domain_checks()
    q,S,T=16,32,175;R=(q*q-S)*(q*q-1)+T
    require(T.bit_count()==6 and R==57295 and R.bit_count()==13 and S&T==32,'scale negative control')
    evidence['scale_negative_control']={'q':q,'S':S,'T':T,'R':R,'pc_R':R.bit_count(),'correct_threshold':14,'weakened_threshold':10,'scope':'local packing only'}
    result={'status':'PASS','snapshot':'a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49',
            'authenticated_upstream_files':source_count,'evidence':evidence,
            'scope':'Exact finite algebra/data/reconstruction checks; the unbounded ZFC equivalence is the written mathematical composition with named inherited calibration. No consistency search or new end-to-end proof-assistant check.'}
    (ROOT/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','upstream_files':source_count,'reconstructed_numerals':4,
                      'circuits_rebuilt':5,'primary':{'variables':12,'degree':110,'operations':100},
                      'companion':{'variables':13,'degree':30,'operations':93}}))

if __name__=='__main__':main()
