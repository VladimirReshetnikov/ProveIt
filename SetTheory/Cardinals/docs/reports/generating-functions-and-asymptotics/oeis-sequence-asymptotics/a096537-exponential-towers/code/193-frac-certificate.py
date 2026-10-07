#!/usr/bin/env python3
"""Recompute the finite interval certificate and verify every terminal panel."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from pathlib import Path
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
import certificate_io as io
from interval_decimal import I,D,PI
from integrate_core import run,panel

CORE_KEYS={'status','precision','z_interval','t_interval','enclosure','panels','quadrature'}
COEFFICIENT_KEYS={'status','core','absolute_tail_bound','integral_enclosure',
 'positive_prefactor_enclosure','coefficient_enclosure','coarse_coefficient_bracket',
 'panel_count','exact_rational_coverage_and_sum'}

def interval_strings(value):
 io.need(type(value) is list and len(value)==2 and all(type(v) is str for v in value),'Interval schema mismatch')
 box=I(*value)
 return box

def validate_core(core):
 io.need(type(core) is dict and set(core)==CORE_KEYS,'Core schema mismatch')
 io.need(core['status']=='PASS' and type(core['precision']) is int and core['precision']==70,'Core identity mismatch')
 io.need(core['z_interval']==['0','3.2'] and core['t_interval']==['0','10.24'],'Core domain mismatch')
 io.need(type(core['panels']) is int and core['panels']==562,'Expected 562 terminal panels')
 io.need(core['quadrature']=='midpoint with interval second derivative and width^3/24 remainder','Quadrature mismatch')
 return interval_strings(core['enclosure'])

def verify_panels(core,rows,recompute=True):
 io.need(type(recompute) is bool,'Recompute flag must be bool')
 box=validate_core(core)
 io.need(type(rows) is list and len(rows)==core['panels'],'Panel schema or count mismatch')
 position=F(0);lower=F(0);upper=F(0)
 for row in rows:
  io.need(type(row) is list and len(row)==4 and all(type(v) is str for v in row),'Panel row schema mismatch')
  endpoint=I(row[0],row[1]);value=I(row[2],row[3])
  left,right,lo,hi=map(F,row)
  io.need(left==position and right>left and right<=F(16,5),'Panel gap, overlap, ordering, or endpoint error')
  if recompute:
   result=panel(endpoint.lo,endpoint.hi)
   io.need([str(result.lo),str(result.hi)]==row[2:],'Recomputed panel differs')
  position=right;lower+=lo;upper+=hi
 io.need(position==F(16,5),'Panel coverage does not end at 16/5')
 io.need(F(box.lo)<=lower<=upper<=F(box.hi),'Exact panel sum is not inside running enclosure')
 return {'status':'PASS','panels_recomputed':len(rows) if recompute else 0,
         'coverage':['0','3.2'],'exact_rational_sum_contained':True,
         'exact_lower_sum':str(lower),'exact_upper_sum':str(upper),
         'lower_outward_excess':str(lower-F(box.lo)),
         'upper_outward_excess':str(F(box.hi)-upper)}

def assemble(core):
 box=validate_core(core);whole=box+I('-.141','.141')
 e=I(1).exp();alpha=e-1
 k=(I(2).ln()/6).exp()*(e/PI).sqrt()
 pref=(-alpha.ln()/6).exp()*k
 coefficient=whole*pref
 io.need(pref.lo>0 and coefficient.hi<0,'Strict negative sign not enclosed')
 io.need(coefficient.lo>=D('-.61') and coefficient.hi<=D('-.25'),'Coarse bracket not enclosed')
 pair=lambda v:[str(v.lo),str(v.hi)]
 return {'status':'conditional_on_the_report_real_integral_identity_and_analytic_tail',
  'core':core['enclosure'],'absolute_tail_bound':'0.141','integral_enclosure':pair(whole),
  'positive_prefactor_enclosure':pair(pref),'coefficient_enclosure':pair(coefficient),
  'coarse_coefficient_bracket':['-0.61','-0.25'],'panel_count':core['panels'],
  'exact_rational_coverage_and_sum':'PASS'}

def check_fixtures():
 core=io.fixture('core_reference.json');rows=io.fixture('panels_reference.json')
 ref=io.fixture('coefficient_reference.json')
 validate_core(core);verify_panels(core,rows,recompute=False)
 io.need(type(ref) is dict and set(ref)==COEFFICIENT_KEYS,'Coefficient fixture schema mismatch')
 io.need(assemble(core)==ref,'Coefficient fixture disagrees with recomputed arithmetic')
 return core,rows,ref

def compute():
 reference_core,reference_panels,reference_coefficient=check_fixtures()
 core,rows=run()
 io.need(core==reference_core,'Adaptive core differs from frozen regression reference')
 io.need(rows==reference_panels,'Adaptive panels differ from frozen regression reference')
 verified=verify_panels(core,rows)
 combined=assemble(core)
 io.need(combined==reference_coefficient,'Combined coefficient differs from frozen regression reference')
 return {'core.json':core,'panels.json':rows,'panel_verification.json':verified,
         'coefficient.json':combined}

def run_certificate(output):
 output=io.checked_output(output);before=io.verify_source()
 results=compute()
 io.need(io.snapshot()==before,'Source changed during certificate execution')
 output.mkdir(exist_ok=False)
 for name,data in sorted(results.items()):io.write_new(output/name,io.canonical(data))
 return {'status':'PASS','arithmetic':'directed Decimal and exact Fraction',
         'panel_count':562,'strict_negative_coefficient':True,
         'files':{name:{'bytes':len(io.canonical(data)),'sha256':io.sha(io.canonical(data))}
                  for name,data in sorted(results.items())}}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output-dir',required=True,type=Path)
 args=parser.parse_args()
 try:
  result=run_certificate(args.output_dir);sys.stdout.buffer.write(io.canonical(result));return 0
 except Exception as exc:
  sys.stderr.buffer.write(io.canonical({'status':'FAIL','error':str(exc)}));return 1

if __name__=='__main__':sys.exit(main())
