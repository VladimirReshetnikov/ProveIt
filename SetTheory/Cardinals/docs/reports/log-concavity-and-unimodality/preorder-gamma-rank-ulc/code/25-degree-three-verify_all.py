#!/usr/bin/env python3
"""Reproduce the exact checks in an isolated temporary copy of the code/data.
Requires Python 3, SymPy, and g++ supporting C++17. No numerical solver is used.
Do not run Python with -O: these scientific checkers deliberately use assertions.
"""
from pathlib import Path
import csv, hashlib, json, os, platform, shutil, subprocess, sys, tempfile, time
import sympy
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'receipts';OUT.mkdir(exist_ok=True)
if not __debug__:raise RuntimeError('Run without -O so assertions remain enabled')
summary={'python':sys.version,'sympy':sympy.__version__,'platform':platform.platform(),'steps':[]}
start=time.monotonic()
with tempfile.TemporaryDirectory(prefix='preorder-gamma-verification-') as tmp:
 C=Path(tmp)/'code';shutil.copytree(ROOT/'code',C)
 def run(name,args,cwd=C,stdout_file=None):
  print(name,flush=True);t=time.monotonic()
  p=subprocess.run([str(a) for a in args],cwd=cwd,capture_output=True,text=True)
  (OUT/(name+'.log')).write_text('$ '+' '.join(map(str,args))+'\n'+p.stdout+'\n'+p.stderr)
  if p.returncode:raise RuntimeError(f'{name} failed; see receipts/{name}.log')
  if stdout_file:Path(stdout_file).write_text(p.stdout)
  summary['steps'].append({'name':name,'passed':True,'seconds':round(time.monotonic()-t,3)})
 def py(name,rel):run(name,[sys.executable,C/rel])
 def compile(name,folder,source,exe):run(name,['g++','-O3','-std=c++17',source,'-o',exe],C/folder)
 compile('compile-small','small-check','exhaust.cpp','exhaust')
 run('enumerate-small',[C/'small-check/exhaust',C/'small-check'])
 py('verify-small','small-check/independent_verify.py')
 compile('compile-one','one-attachment','certify.cpp','certify')
 run('enumerate-one',[C/'one-attachment/certify'],stdout_file=C/'one-attachment/pairs.csv')
 py('verify-one','one-attachment/verify.py')
 compile('compile-one-independent','one-attachment','audit_independent.cpp','audit_independent')
 run('audit-one',[C/'one-attachment/audit_independent'],stdout_file=C/'one-attachment/audit_pairs.csv')
 def csv_rows(f):return list(csv.DictReader(open(f)))
 # Compare every tuple multiplicity; independent representatives may differ.
 a=csv_rows(C/'one-attachment/pairs.csv');b=list(csv.reader(open(C/'one-attachment/audit_pairs.csv')))
 fields=['p1','p2','p3','q1','q2'];count=next(k for k in a[0] if k in ('multiplicity','count'))
 def keyed(rows):return {tuple(int(r[k])for k in fields):int(r[count])for r in rows}
 assert keyed(a)=={tuple(map(int,r[:5])):int(r[5])for r in b} and len(a)==2050
 py('audit-two','two-attachment/independent_audit.py')
 py('verify-two','two-attachment/verify_gap2_certificates.py')
 py('verify-two-hall','two-attachment/verify_independent.py')
 py('audit-cover-three','audit_cover3.py')
 py('verify-cover-compact','verify_cover3_compact.py')
 py('verify-cover-squares','verify_cover3_sos.py')
 py('verify-cover-general-squares','verify_cover3_sdp_complete.py')
 py('verify-ordinal-core','core_templates.py')
 py('verify-ordinal-layers','verify_layered.py')
 compile('compile-minimum-core','minimum','certify_min_size.cpp','certify_min_size')
 run('enumerate-minimum-core',[C/'minimum/certify_min_size'],stdout_file=C/'minimum/a1_min_size_pairs.csv')
 shutil.copy2(C/'minimum/a1_min_size_pairs.csv',C/'minimum/independent-audit/a1_pairs.csv')
 py('scan-minimum-one-three','minimum/scan_minimum.py')
 py('scan-minimum-two','minimum/scan_a2.py')
 py('audit-minimum-independent','minimum/independent-audit/audit.py')
 py('verify-fifteen-supports','minimum/verify_15_supports.py')
 summary['minimum_scan']=json.loads((C/'minimum/independent-audit/receipt.json').read_text())
 summary['two_attachment']=json.loads((C/'two-attachment/independent_audit.json').read_text())
summary['all_passed']=True;summary['seconds']=round(time.monotonic()-start,3)
(OUT/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('ALL CHECKS PASSED',summary['seconds'],'seconds',flush=True)
