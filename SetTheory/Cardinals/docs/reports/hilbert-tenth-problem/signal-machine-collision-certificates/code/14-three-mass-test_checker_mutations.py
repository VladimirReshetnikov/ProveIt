#!/usr/bin/env python3
"""Independent adversarial serialized-certificate and checker CLI checks."""
import copy,hashlib,importlib.util,json,subprocess,sys,random
from collections import Counter
from pathlib import Path
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
args=parser.parse_args()
SOURCE=args.source_dir.resolve();R=args.output_dir.resolve();R.mkdir(parents=True,exist_ok=True)
def source(name):
    canonical={'certificate_snapshot.py':'certificate.py','checker_snapshot.py':'checker.py'}[name]
    path=SOURCE/name
    return path if path.exists() else SOURCE/canonical
s=importlib.util.spec_from_file_location('checker_snapshot',source('checker_snapshot.py'));K=importlib.util.module_from_spec(s);s.loader.exec_module(K)
s=importlib.util.spec_from_file_location('certificate_snapshot',source('certificate_snapshot.py'));C=importlib.util.module_from_spec(s);sys.modules[s.name]=C;s.loader.exec_module(C)
cert=json.loads((R/'literal-mixed-certificate.json').read_text());w=json.loads((R/'literal-mixed-witness.json').read_text())
counts=Counter();rejected=[];accepted=[]

def trial(label,c=cert,x=w,reject=True):
    try:K.check(c,x)
    except (ValueError,KeyError,IndexError,TypeError):
        if not reject:raise
        rejected.append(label);counts['rejected_mutations']+=1
    else:
        if reject:accepted.append(label)
        else:counts['valid_accepted']+=1
trial('original mixed',reject=False)
for col in ('squares','products','steps','variables','input_variables','output_variables','loader','initial_N','final_N','physical_time','ledger','branches'):
    c=copy.deepcopy(cert)
    if isinstance(c[col],list):
        if c[col]:c[col]=c[col][1:]
        else:c[col]=['injected']
    elif isinstance(c[col],dict):c[col]['injected']=1
    trial('structure '+col,c)
for i,row in enumerate(cert['squares']):
    c=copy.deepcopy(cert);keys=list(row['affine']);key=keys[0] if keys else '';c['squares'][i]['affine'][key]=row['affine'].get(key,0)+1
    trial('square coefficient '+str(i),c)
for i,row in enumerate(cert['products']):
    for side in ('left','right'):
        c=copy.deepcopy(cert);key=next(iter(row[side]),'');c['products'][i][side][key]=row[side].get(key,0)+1
        trial('product coefficient '+str(i)+' '+side,c)
for t,step in enumerate(cert['steps']):
    for j,row in enumerate(step):
        c=copy.deepcopy(cert);c['steps'][t][j]['ticks']['']=1
        trial('microtime coefficient '+str(t)+' '+str(j),c)
for k in cert['ledger']:
    c=copy.deepcopy(cert);c['ledger'][k]+=1;trial('ledger '+k,c)
for k,v in w.items():
    x=dict(w);x[k]+=1;trial('witness increment '+k,x=x)
    if v:x[k]=v-1;trial('witness decrement '+k,x=x)
for value in (True,-1,0.5):
    x=dict(w);x['e_0_0']=value;trial('witness type '+str(value),x=x)
for field,value in [('domain','nonnegative reals'),('format','invalid'),('horizon',True),('horizon',10),('initial_state','halt')]:
    c=copy.deepcopy(cert);c[field]=value;trial('header '+field,c)
for field in ('output_spec','time_spec'):
    c=copy.deepcopy(cert);c[field]={'mode':'fixed','value':0};trial('endpoint '+field,c)
# Full exporter/witness/checker subprocess path uses the frozen sources.
request={k:cert[k] for k in ('machine','initial_state','horizon','input_spec','output_spec','time_spec')}
(R/'cli-request.json').write_text(json.dumps(request))
subprocess.run([sys.executable,str(source('certificate_snapshot.py')),'export',str(R/'cli-request.json'),str(R/'cli-certificate.json'),'--expanded'],check=True)
subprocess.run([sys.executable,str(source('certificate_snapshot.py')),'witness',str(R/'cli-certificate.json'),str(R/'cli-witness.json')],check=True)
subprocess.run([sys.executable,str(source('checker_snapshot.py')),str(R/'cli-certificate.json'),str(R/'cli-witness.json'),'--receipt',str(R/'cli-receipt.json')],check=True)
cc=json.loads((R/'cli-certificate.json').read_text());ww=json.loads((R/'cli-witness.json').read_text());assert ww==w
assert {k:v for k,v in cc.items() if k!='expanded_polynomial'}==cert
trial('CLI expanded original',cc,ww,reject=False)
c=copy.deepcopy(cc);c['expanded_polynomial'][0]['coefficient']+=1;trial('expanded polynomial coefficient',c,ww)
c=copy.deepcopy(cc);c['expanded_polynomial']=[];trial('expanded polynomial removed terms',c,ww)
p=cc['expanded_polynomial'];coeffs=[abs(r['coefficient']) for r in p]
report={'status':'PASS' if not accepted else 'DEFECT_FOUND','checker_sha256':hashlib.sha256((source('checker_snapshot.py')).read_bytes()).hexdigest(),'counts':dict(counts),'unexpectedly_accepted_mutations':accepted,'literal_mixed_expanded_terms':len(p),'literal_mixed_max_abs_coefficient':max(coeffs),'literal_mixed_max_coefficient_bits':max(coeffs).bit_length(),'cli_check':'passed','rejected_mutations':rejected}
(R/'checker-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='rejected_mutations'},indent=2))
