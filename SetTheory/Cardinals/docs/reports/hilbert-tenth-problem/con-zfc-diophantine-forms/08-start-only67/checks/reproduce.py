#!/usr/bin/env python3
"""Bounded release checks. Never execute received upstream programs or enumerate the full alphabet."""
import argparse,hashlib,json,os,subprocess,sys,tempfile,shutil
from pathlib import Path
if not __debug__ or sys.flags.optimize:
    raise SystemExit('Use normal python3, not -O/-OO: some owned checks use assertions.')
ROOT=Path(__file__).resolve().parents[1]
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def verify_manifest():
    m=json.loads((ROOT/'MANIFEST.json').read_text())
    for r in m['files']:
        p=ROOT/r['path']; b=p.read_bytes()
        need(len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],'Manifest mismatch: '+r['path'])
    return len(m['files'])
def verify_pins():
    count=0
    for dirname,mname,key in [('diophantine_zfc_review','review_source_manifest.json','local_name'),('diophantine_zfc_core/sources','manifest.json','file')]:
        base=ROOT/'evidence'/dirname
        m=json.loads((base/mname).read_text())
        need(m['commit']=='cdd582bec13f908df3711fa9e05d1ddac368a5db','Unexpected source pin')
        for r in m['files']:
            b=(base/r[key]).read_bytes()
            need(hashlib.sha256(b).hexdigest()==r['sha256'],'Pinned SHA mismatch: '+r[key])
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            need(blob==r.get('git_blob_sha1',r.get('git_blob_sha')),'Pinned Git blob mismatch: '+r[key])
            count+=1
    return count

def packet_sanity():
    from collections import Counter
    out=[]
    for name in ['start_only_polynomial67.json','start_only_system61.json','fixed_input_system61.json']:
        p=json.loads((ROOT/'evidence/diophantine_zfc_review'/name).read_text())
        known=set(p['witnesses']+p['fixed_numerals']);c=Counter()
        for n,op,a,b in p['source']:
            need(n not in known and op in ('+','-','*'),'Invalid row')
            need(all(type(x) is int or (type(x) is str and x in known) for x in (a,b)),'Unbound operand')
            known.add(n);c[op]+=1
        need(len(p['source'])==p['ledger']['total'],'Wrong total')
        need(c['*']==p['ledger']['M'] and c['+']+c['-']==p['ledger']['A'],'Wrong ledger')
        out.append(dict(file=name,witnesses=len(p['witnesses']),rows=len(p['source'])))
    return out

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    result={'manifest_files':verify_manifest(),'pinned_source_files':verify_pins(),'literal_packets':packet_sanity(),'checks':[]}
    # Keep release receipts and manifest untouched. Helpers may write their own output.
    with tempfile.TemporaryDirectory(prefix='diophantine-zfc-replay-') as tmp:
        work=Path(tmp)/'evidence';shutil.copytree(ROOT/'evidence',work)
        jobs=[
          ('table_binding','diophantine_zfc_core/audit_table_binding.py',[]),
          ('compiler','diophantine_zfc_compiler/explicit_constants.py',[]),
          ('start_only_compiler','diophantine_zfc_compiler/start_only_constants.py',[]),
          ('independent_compiler','diophantine_zfc_compiler/independent_audit.py',[]),
          ('arithmetic','diophantine_zfc_review/verify_start_only_packets.py',[]),
          ('independent_arithmetic','diophantine_zfc_root/audit_inputless.py',[]),
          ('quadratic_eliminations','diophantine_zfc_review/verify_quadratic_reduction.py',[]),
          ('quartic34','diophantine_zfc_review/verify_quartic34.py',[]),
        ]
        env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env.pop('PYTHONOPTIMIZE',None)
        for label,path,extra in jobs:
            run=subprocess.run([sys.executable,str(work/path),*extra],cwd=tmp,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            need(run.returncode==0,label+' failed:\n'+run.stdout+'\n'+run.stderr)
            result['checks'].append({'name':label,'status':'PASS','stdout_sha256':hashlib.sha256(run.stdout.encode()).hexdigest()})
            print(label+': PASS',flush=True)
    result['scope']='Bounded data/source/circuit audits only. No full alphabet/numeral expansion, no solution search, and no Lean/Rocq rebuild.'
    result['status']='PASS'
    text=json.dumps(result,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
