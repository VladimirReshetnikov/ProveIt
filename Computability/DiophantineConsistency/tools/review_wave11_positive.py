#!/usr/bin/env python3
"""Independent wave11 positive-literal audit; never executes archive code."""
import argparse,gzip,hashlib,json
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
OUTPUT=HERE.parent/'PROPOSAL_REVIEW_WAVE11_POSITIVE.json'
P=1000000007
def require(b,label):
    if not b:raise RuntimeError(label)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def plus(a,b,sgn=1):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]=x
    for i,x in enumerate(b):c[i]=(c[i]+sgn*x)%P
    while len(c)>1 and c[-1]==0:c.pop()
    return c
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%P
    while len(c)>1 and c[-1]==0:c.pop()
    return c
def coefficients(folder):
    b=json.loads((folder/'ACTIVE_BINDING.json').read_text());values={};rawhash={}
    for name,row in b['ports'].items():
        path=folder/(row.get('gzip_payload')or row['file'])
        zipped=path.read_bytes();raw=gzip.decompress(zipped)
        h=hashlib.sha256(raw).hexdigest()
        require(h==(row.get('sha256_raw')or row['sha256']),'raw coefficient hash')
        require(hashlib.sha256(zipped).hexdigest()==(row.get('sha256_gzip')or row['gzip_sha256']),'compressed coefficient hash')
        value=int.from_bytes(raw,'little');values[name]=value;rawhash[name]=h
        require(value.bit_length()==row['bits']and len(raw)==row['raw_bytes'],'coefficient size')
    require(set(values)=={'beta','K0','MC','MF'},'whole tuple')
    beta=values['beta'];require(beta==(1<<590069)-1,'actual beta')
    require(values['K0']>=1 and 0<values['MC']<beta and 0<values['MF']<2*beta,'actual mask bounds')
    return values,rawhash
def circuit(path,ports):
    p=json.loads(path.read_text());known=set(p['witnesses']+p['fixed_numerals']);parents={}
    for n,op,a,b in p['source']:
        require(n not in known and op in ['+','-','*'],'fresh arithmetic gate')
        require(all(type(x)is int or x in known for x in [a,b]),'topology')
        known.add(n);parents[n]=(a,b)
    live=set();todo=[p['output']]
    while todo:
        x=todo.pop()
        if type(x)is int or x in live:continue
        live.add(x);todo.extend(parents.get(x,()))
    require(known==live,'all gates and inputs live')
    require(len(p['source'])==p['operations'],'literal count')
    env={x:[0,i+1]for i,x in enumerate(p['witnesses'])}
    env.update({k:[v%P]for k,v in ports.items()})
    def val(x):return [x%P]if type(x)is int else env[x]
    for n,op,a,b in p['source']:
        aa,bb=val(a),val(b)
        env[n]=mul(aa,bb) if op=='*' else plus(aa,bb,1 if op=='+' else -1)
    result=env[p['output']]
    require(len(result)-1==p['exact_degree'],'independent actual-port degree lower bound')
    return dict(variables=len(p['witnesses']),operations=len(p['source']),
      operation_breakdown=dict(Counter(r[1]for r in p['source'])),
      stated_degree=p['exact_degree'],actual_port_univariate_degree=len(result)-1,
      leading_coefficient_mod_prime=result[-1],all_gates_and_inputs_live=True,
      circuit_sha256=digest(path),source_array_sha256=hashlib.sha256(json.dumps(p['source'],separators=(',',':')).encode()).hexdigest())
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--arrivals',type=Path,default=Path('/tmp/dioph-wave11-arrivals-9a33342a03'))
    ap.add_argument('--selected-replay',type=Path,default=Path('/tmp/proofs62ff-wave11-positive-replay/SELECTED_POSITIVE_REPLAY.json'))
    args=ap.parse_args();arr=json.loads((args.arrivals/'ARRIVALS.json').read_text())
    roots=[
      ('ConZFC_Structural_Reductions_Round11_2026-10-24','con-zfc-structural-reductions-round11','positive/native',['positive/p11_degree277.json','positive/p12_degree78.json']),
      ('con-zfc-budget-and-centering-2026-10-23','con-zfc-budget-and-centering-2026-10-23','positive/coefficients',['positive/eleven/p11_positive_degree277.json','positive/twelve/equation.json']),
      ('con-zfc-centered-pell-norms','con-zfc-centered-pell-norms','coefficients',['positive11/p11_positive_degree277.json','positive12/equation.json']),
      ('ZFC_Diophantine_Joint_Guards_2026-10-24','ZFC_Diophantine_Joint_Guards','pell/coefficients',['pell/p11_positive_degree277.json','pell/p11_positive_degree257.json'])]
    results=[];hashes=None
    for outer,inner,binding,paths in roots:
        root=args.arrivals/outer/inner;ports,rawhash=coefficients(root/binding)
        if hashes is None:hashes=rawhash
        require(hashes==rawhash,'all four whole tuples identical')
        for path in paths:results.append(dict(package=outer,path=path,**circuit(root/path,ports)))
    pins=[]
    selected={x[0]for x in roots}|{'report'}
    for a in arr:
        if Path(a['destination']).name not in selected:continue
        archive=REPO/a['archive'];require(archive.is_file()and digest(archive)==a['sha256'],'actual input archive SHA256')
        pins.append({k:a[k]for k in ['archive','sha256','files','raw_bytes']})
    replay=json.loads(args.selected_replay.read_text());require(replay['status']=='PASS','selected author-script replays')
    commands=[x for group in replay['results']for x in group]
    require(len(commands)==26 and all(x['returncode']==0 for x in commands),'all selected normal/optimized commands')
    report=args.arrivals/'report/report.tex'
    out=dict(status='PASS',scope='Independent finite literal/whole-tuple checks plus26 selected authored Python replays; no Lean or whole-native semantic proof.',
      archive_pins=pins,manuscript=dict(path='report/report.tex',sha256=digest(report),files_in_archive=1,literal_degree70_json_delivered=False),
      modulus=P,univariate_specialization='x_i=(i+1)t',whole_compact44_raw_hashes=hashes,
      literal_results=results,selected_replay=commands,
      exclusions=['No full multi-component release replay claimed','No nine-variable endpoint review here','No native/global calibration or encoded ZFC derivation'])
    OUTPUT.write_text(json.dumps(out,indent=2)+'\n');print('PASS eight incoming literal circuits, whole tuple, actual-port degree specializations and26 selected Python replays')
if __name__=='__main__':main()
