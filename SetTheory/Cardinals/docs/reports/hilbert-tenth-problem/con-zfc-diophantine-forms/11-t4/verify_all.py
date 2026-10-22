"""Replay this packet's owned diagnostics in a temporary copy, without -O."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
if not __debug__:raise SystemExit('Run without -O: assertion-based audits must be enabled.')
def check_manifest():
 p=ROOT/'SHA256SUMS.json'
 if p.exists():
  for name,wanted in json.loads(p.read_text()).items():
   actual=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
   if actual!=wanted:raise ValueError('Hash mismatch: '+name)
def bind_machine(root):
 f=root/'bridge/sources/k215.tm'
 if hashlib.sha256(f.read_bytes()).hexdigest()!='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090':raise ValueError('Literal table hash mismatch')
 rows=[]
 for line in f.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,m,nq=line.split();rows.append([int(q),int(b),int(w),{'L':-1,'R':1}[m],int(nq)])
 data=json.loads((root/'bridge/sources/k215_transitions.json').read_text())['transitions']
 if rows!=data or len(rows)!=430:raise ValueError('Transition projection mismatch')
def main():
 check_manifest();bind_machine(ROOT)
 instance=json.loads((ROOT/'INSTANCE.json').read_text())
 for name in instance['main_files']:
  packet=json.loads((ROOT/name).read_text())
  binding=packet.get('selected_coefficient_recipe') or packet.get('coefficient_recipe') or packet.get('coefficient_binding',{}).get('selected_recipe')
  if binding!='../bridge/T4_CONSTANTS.json':raise ValueError('Wrong distributed coefficient binding: '+name)
 scripts=['comparison/build_hybrid.py','comparison/audit_packet_circuits.py','reduction/build_signed.py','reduction/build_odd_signed.py','quartic/audit_quartic33.py','quartic/audit_quartic33_ordinary.py','checks/independent_core_check.py','review/independent_review_checks.py','review/independent_quartic_checks.py','bridge/check_cross_counts.py','bridge/check_t4.py','review/independent_t4_checks.py']
 result={'status':'PASS','literal_transition_rows':430,'scripts':[],'scope':'Exact finite/symbolic checks, not unbounded equivalence or a proof-assistant build.'}
 with tempfile.TemporaryDirectory(prefix='zfc-combined-audit-') as temp:
  dest=Path(temp)/'packet';shutil.copytree(ROOT,dest,ignore=shutil.ignore_patterns('__pycache__'))
  for name in scripts:
   run=subprocess.run([sys.executable,'-B',str(dest/name)],cwd=dest,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
   if run.returncode:
    print(run.stdout);print(run.stderr,file=sys.stderr);raise RuntimeError('Failed: '+name)
   result['scripts'].append({'path':name,'exit_code':0,'stdout_sha256':hashlib.sha256(run.stdout.encode()).hexdigest()})
   print('PASS '+name,flush=True)
  instance=json.loads((dest/'INSTANCE.json').read_text())
  for name in instance['main_files']:
   p=json.loads((dest/name).read_text())
   binding=p.get('selected_coefficient_recipe') or p.get('coefficient_recipe') or p.get('coefficient_binding',{}).get('selected_recipe')
   if binding!='../bridge/T4_CONSTANTS.json':raise ValueError('Wrong main coefficient binding: '+name)
  geom=json.loads((dest/'bridge/t4_verification.json').read_text())['geometry']
  if geom['d']!=5**18 or geom['T2']!=6943861:raise ValueError('Old coefficient layout survived')
  result['primary_binding_checked']=instance['binding_id']
 print(json.dumps(result,indent=2))
 if '--write-receipt' in sys.argv:(ROOT/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
