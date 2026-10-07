#!/usr/bin/env python3
"""Explicit normal/-O input, provenance, output, and certificate rejection tests."""
from __future__ import annotations
import ast
import copy
from decimal import Decimal,InvalidOperation
from fractions import Fraction
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
from unittest import mock
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
import certificate_io as io
import certificate
import integrate_core
import check_exact
import reproduce
from interval_decimal import I,atan_small,bernoulli,gamma_fraction
from airy_interval import C,atan_point,atan_range,fundamental_point,airy_point
from jet_interval import J,CJ

class Checks:
 def __init__(self):self.good_count=0;self.bad_count=0
 def good(self,condition,message):
  io.need(condition,message);self.good_count+=1
 def bad(self,fn,message):
  try:fn()
  except (ValueError,TypeError,OSError,ZeroDivisionError,InvalidOperation):self.bad_count+=1
  else:raise ValueError('Unexpected acceptance: '+message)

def run_tests():
 c=Checks()
 for fn in [lambda:check_exact._row_polynomials(True),lambda:check_exact._row_polynomials(-1),
            lambda:check_exact._decode_depths((True,),2),lambda:check_exact._decode_depths((4,),2),
            lambda:check_exact._decode_depths([],1),lambda:check_exact._prufer_polynomial(0),
            lambda:check_exact._rational_tower(1,2,0.5),lambda:check_exact._rational_tower(-1,2,Fraction(1)),
            lambda:check_exact._formal_tower(1,2,0),lambda:check_exact._rational_coefficients(2,1,0),
            lambda:check_exact._multiply([True],[1]),lambda:check_exact._check_recurrence([[1],[0,2]]),
            lambda:check_exact.main([1])]:c.bad(fn,'exact checker input or recurrence guard')
 for value in [True,False,0.1,complex(1),None,[],(0,(1,),0),Decimal('NaN'),Decimal('sNaN'),Decimal('Infinity'),'-Infinity','NaN']:
  c.bad(lambda value=value:I(value),'non-exact or nonfinite constructor')
  c.bad(lambda value=value:I(0,value),'non-exact or nonfinite second endpoint')
 for first in [I(1),Fraction(1,3)]:
  for second in [None,0,I(2),Fraction(2,3)]:c.bad(lambda first=first,second=second:I(first,second),'copy/rational endpoint misuse')
 c.bad(lambda:I(2,1),'inverted interval')
 for n in [True,False,0.5,'2',Fraction(2),Decimal(2),complex(2),None]:
  for cls in [I,J,C,CJ]:c.bad(lambda cls=cls,n=n:cls(1)**n,'unsupported exponent')
 for cls in [J,C,CJ]:c.bad(lambda cls=cls:cls(cls(1),0),'copy constructor extra argument')
 c.bad(lambda:J(J(1),dd=0),'jet second derivative copy misuse')
 for cls in [I,J,C,CJ]:
  c.bad(lambda cls=cls:cls(0).inv(),'zero reciprocal')
 c.bad(lambda:1/I(-1,1),'zero-crossing reciprocal')
 c.bad(lambda:I(-1).sqrt(),'negative sqrt');c.bad(lambda:I(0).ln(),'zero log')
 c.good(I(0).sqrt().lo==0,'sqrt lower bound should retain nonnegativity')
 for arg in [I(-2,-1),I(-2),I('-.5'),I(-1,1)]:
  c.bad(lambda arg=arg:atan_point(arg),'negative atan point')
  c.bad(lambda arg=arg:atan_range(arg),'negative atan range')
 for n in [-1,0,True,0.5]:c.bad(lambda n=n:atan_small(Fraction(1,5),n),'atan series count')
 for q in [Fraction(-1),Fraction(1),Decimal('.2'),0.2]:c.bad(lambda q=q:atan_small(q),'atan rational domain')
 for n in [-1,True,0.5]:c.bad(lambda n=n:bernoulli(n),'Bernoulli index')
 for n in [-1,True,0.5]:c.bad(lambda n=n:gamma_fraction(Fraction(1),shift=n),'gamma shift')
 for n in [0,-1,True,0.5]:c.bad(lambda n=n:gamma_fraction(Fraction(1),terms=n),'gamma terms')
 for q in [Fraction(0),Fraction(-1),1,Decimal(1)]:c.bad(lambda q=q:gamma_fraction(q),'gamma rational domain')
 for off in [-1,2,True,0.5]:c.bad(lambda off=off:fundamental_point(1,off),'Airy offset')
 for steps in [0,-1,True,0.5]:c.bad(lambda steps=steps:fundamental_point(1,0,steps),'Airy series count')
 airy_point(Decimal('1'))
 for q in [-1,10,0.1,1.0,True,False,Decimal('NaN'),Decimal('Infinity')]:c.bad(lambda q=q:airy_point(q),'Airy point domain')
 for args in [(-1,1),(0,4),(1,1),(2,1),(0,0.1)]:c.bad(lambda args=args:integrate_core.panel(*args),'panel domain')
 for tol in ['0','-1','NaN','Infinity',0.1]:c.bad(lambda tol=tol:integrate_core.run(tol),'integration tolerance')
 for limit in [0,63,True,'100',100.5]:c.bad(lambda limit=limit:integrate_core.run(maxpanels=limit),'panel budget')
 for cls in [C,CJ]:
  for args in [(0,1),(-1,1),(1,-1)]:c.bad(lambda cls=cls,args=args:cls(*args).log_q1(),'complex log quadrant')
 for raw in ['{"x":1,"x":2}','{"x":NaN}','{"x":Infinity}','{"x":-Infinity}','{"x":1e9999}','{"x":0.1}']:c.bad(lambda raw=raw:io.load_json(raw),'strict JSON')
 for name in ['', '../x','/x','a/../x','a//b','a/./b','a\\b','a:b','__pycache__/x','a.pyc','a\x00b']:
  c.bad(lambda name=name:io.safe_name(name),'unsafe package path')
 with tempfile.TemporaryDirectory(prefix='report193-guards-') as temporary:
  root=Path(temporary);source=root/'source';source.mkdir()
  existing=root/'existing';existing.write_bytes(b'preserve')
  directory=root/'directory';directory.mkdir()
  link=root/'link';link.symlink_to(source,target_is_directory=True)
  dangling=root/'dangling';dangling.symlink_to(root/'missing')
  for path in [existing,directory,dangling,link/'new',source/'new',root/'missing'/'new',root/'unused'/'..'/'new']:
   c.bad(lambda path=path:io.checked_output(path,source),'unsafe output path')
  c.good(existing.read_bytes()==b'preserve','existing output untouched')
  c.bad(lambda:io.write_new(existing,b'bad'),'exclusive output write')
  c.good(io.checked_output(root/'fresh',source)==root/'fresh','fresh output accepted')
  c.bad(lambda:io.read_regular(dangling),'input link')
  input_link=root/'file-link';input_link.symlink_to(existing)
  c.bad(lambda:io.read_regular(input_link),'input link')
  c.bad(lambda:io.read_regular(existing,2),'read size limit')
  c.bad(lambda:io.read_regular(directory),'directory input')
  with mock.patch.object(certificate,'compute') as compute:
   c.bad(lambda:certificate.run_certificate(existing),'output rejected before computation')
   c.good(not compute.called,'invalid output triggered expensive computation')
  with mock.patch.object(check_exact,'run_checks') as exact:
   c.bad(lambda:check_exact.main(['--output',str(existing)]),'exact output rejected before computation')
   c.good(not exact.called,'invalid exact output triggered computation')
  with mock.patch.object(reproduce,'run_mode') as mode:
   c.bad(lambda:reproduce.run(existing),'replay output rejected before computation')
   c.good(not mode.called,'invalid replay output triggered computation')
  # Run strict source and fixture corruption checks on private copies only.
  cloned=root/'cloned';shutil.copytree(ROOT,cloned)
  c.good(io.verify_source(cloned)==io.snapshot(cloned),'closed source verification')
  for name in io.SOURCES:
   c.good(name in io.verify_source(cloned),'all source inventory entries verified')
  unexpected=cloned/'unexpected.txt';unexpected.write_text('x')
  c.bad(lambda:io.verify_source(cloned),'extra source file');unexpected.unlink()
  empty=cloned/'empty';empty.mkdir();c.bad(lambda:io.verify_source(cloned),'empty source directory');empty.rmdir()
  target=cloned/'README.md';original=target.read_bytes();target.write_bytes(original+b' ')
  c.bad(lambda:io.verify_source(cloned),'changed source bytes');target.write_bytes(original)
  provenance=cloned/io.MANIFEST;raw=provenance.read_bytes();doc=io.load_json(raw)
  mutations=[]
  changed=copy.deepcopy(doc);changed['report']=True;mutations.append(changed)
  changed=copy.deepcopy(doc);changed['files']['README.md']['bytes']=True;mutations.append(changed)
  changed=copy.deepcopy(doc);changed['files']['README.md']['sha256']='X'*64;mutations.append(changed)
  changed=copy.deepcopy(doc);changed['extra']=1;mutations.append(changed)
  for changed in mutations:
   provenance.write_bytes(io.canonical(changed));c.bad(lambda:io.verify_source(cloned),'malformed provenance')
  provenance.write_bytes(raw)
  for name in io.FIXTURE_SHA256:
   path=cloned/'fixtures'/name;data=path.read_bytes();path.write_bytes(data+b' ')
   c.bad(lambda name=name:io.fixture(name,cloned),'fixture checksum mismatch');path.write_bytes(data)
  c.bad(lambda:io.fixture('../README.md',cloned),'nonallowlisted fixture')
  generated={name:b'fixture\n' for name in reproduce.OUTPUTS}
  with mock.patch.object(reproduce,'run_mode',return_value=generated):
   receipt=reproduce.run(root/'valid-replay',cloned)
   c.good(receipt['normal_and_optimized_byte_identical'],'replay matching modes')
   c.good(io.verify_source(cloned)==io.snapshot(cloned),'replay preserves source')
  with mock.patch.object(reproduce,'run_mode',side_effect=[generated,{'wrong':b'bad'}]):
   c.bad(lambda:reproduce.run(root/'unequal-replay',cloned),'replay mode disagreement')
   c.good(not (root/'unequal-replay').exists(),'unequal replay must not publish')
  def mutating_mode(*args):
   target.write_bytes(original+b'changed');return generated
  with mock.patch.object(reproduce,'run_mode',side_effect=mutating_mode):
   c.bad(lambda:reproduce.run(root/'mutated-replay',cloned),'source mutation during replay')
   c.good(not (root/'mutated-replay').exists(),'mutated replay must not publish')
  target.write_bytes(original)
  racing=root/'racing-replay'
  def racing_mode(*args):
   if not racing.exists():racing.mkdir();(racing/'sentinel').write_bytes(b'keep')
   return generated
  with mock.patch.object(reproduce,'run_mode',side_effect=racing_mode):
   c.bad(lambda:reproduce.run(racing,cloned),'racing output creation')
   c.good((racing/'sentinel').read_bytes()==b'keep','racing output preserved')
  c.good(not list(root.glob('report193-replay-*')),'temporary replay cleanup')
 # Structural corruption is rejected even after parsing a valid fixture.
 core=io.fixture('core_reference.json');rows=io.fixture('panels_reference.json')
 for edit in ['count','domain','precision','extra','status','inversion']:
  bad=copy.deepcopy(core)
  if edit=='count':bad['panels']=True
  elif edit=='domain':bad['z_interval']=['0','3.1']
  elif edit=='precision':bad['precision']=70.0
  elif edit=='extra':bad['unexpected']=1
  elif edit=='status':bad['status']='FAIL'
  else:bad['enclosure'].reverse()
  c.bad(lambda bad=bad:certificate.verify_panels(bad,rows,False),'core schema/domain corruption')
 for edit in ['gap','overlap','endpoint','inversion','unsorted','count','nonfinite']:
  bad=copy.deepcopy(rows)
  if edit=='gap':bad[1][0]='0.1'
  elif edit=='overlap':bad[1][0]='0'
  elif edit=='endpoint':bad[-1][1]='3.1'
  elif edit=='inversion':bad[0][2],bad[0][3]=bad[0][3],bad[0][2]
  elif edit=='unsorted':bad[0],bad[1]=bad[1],bad[0]
  elif edit=='count':bad.pop()
  else:bad[0][2]='NaN'
  c.bad(lambda bad=bad:certificate.verify_panels(core,bad,False),'panel corruption')
 with mock.patch.object(certificate,'panel',return_value=I(0)):
  c.bad(lambda:certificate.verify_panels(core,rows),'recomputed-panel mismatch')
 # Check that mandatory code contains no assert and imports only the standard library/local modules.
 modules={Path(name).stem for name in io.SOURCES if name.endswith('.py')}
 for name in io.SOURCES:
  if not name.endswith('.py'):continue
  tree=ast.parse(io.read_regular(ROOT/name))
  c.good(not any(isinstance(node,ast.Assert) for node in ast.walk(tree)),'assert found in '+name)
  imports=set()
  for node in ast.walk(tree):
   if isinstance(node,ast.Import):imports.update(alias.name.split('.')[0] for alias in node.names)
   elif isinstance(node,ast.ImportFrom) and node.module:imports.add(node.module.split('.')[0])
  c.good(imports<=set(sys.stdlib_module_names)|modules,'nonstandard dependency in '+name)
 return {'status':'PASS','acceptance_tests':c.good_count,'rejection_tests':c.bad_count,
         'total_tests':c.good_count+c.bad_count,'network_required':False}

if __name__=='__main__':
 try:sys.stdout.buffer.write(io.canonical(run_tests()))
 except Exception as exc:
  sys.stderr.buffer.write(io.canonical({'status':'FAIL','error':str(exc)}));sys.exit(1)
