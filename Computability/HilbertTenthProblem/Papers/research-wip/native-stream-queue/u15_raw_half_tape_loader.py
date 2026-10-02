#!/usr/bin/env python3
"""Bounded source-and-input scout; no complete universal history predicate."""
from pathlib import Path
from collections import Counter
import argparse, hashlib, importlib.util, json, random
import sympy as sp
HERE=Path(__file__).resolve().parent
SOURCE_PINS={'affine_history_linear_forms.py': '387aa2f1296a10a1f2e2b1e3a03d1765104a683f183c870776fc72909eedbbc2', 'gpcp_complete_fixed_program.py': '4ea5b1072091f5b8a9ee8e3c5131ce7fde426ebae71e7abe9e3f0952a5f9906a', 'gpcp_complete_fixed_program_units.py': '07f12dbcb0e15ad3c38318fc10df306334f57f17dfae99c755272f1925fed0f4', 'gpcp_fixed_program_input_bridge.py': '0d5023b52a5ffe87f5c9e26b436048571e75ccbebfd18c62f9820729b10b74f0', 'gpcp_slope_class_compiler.py': '304f25b17e13eeb7871f78bbc580ca79bf4c51956a71557ce17dac91c7281699', 'group_linked_binary_geometry47.py': 'f3368a4676138275a5329a4f53b63e918fb3dab7a7a9e143ec8edb0a8216b58f', 'native_binary_input_dilation129.py': 'ec29db56b8e03e58d52022d8aefd0d9fbfb13549c210b8aad1c08f645198b0b5', 'native_binary_input_dilation130.py': '7e7ccb297083ffb799775d729b81ec0e403981f287af62513338c5d366fb9ac2', 'native_binary_input_dilation132.py': '4734230670ee87464fd6df4f884904a4351c51b257ae8d87d21d5c362d086df7', 'native_binary_input_dilation_unit179.py': 'f9e1ea743970ccac02f4625c0f2ac82cbbecc86575f256bacb94e3aa92fe12dd', 'native_binary_masked_selection63.py': 'fcff972928d234450901021b2fce5acf41e0c917ab8174ac67fee0b60df7c985', 'native_binary_masked_selection65.py': '3a2fe06641767be09f1e85a6b749480cd2b44b4c51caad30b9e095b654b2897c', 'native_binary_three_row_fifo58.py': 'c245a16893f62001f10dc734b949539835d5c43e6deb6cb3ef322872ef826800', 'native_controller_binary_selector56.py': 'd21de8fc373c5a55a30efdcf5a3171c06f80568a9edfdb98d5176fc2767494b1', 'native_controller_three_selector_53.py': '690790e946f50c039ff2b8c61f33c8545a859ebfb9b45de93fc3e152cc4aedb7', 'neary_woods_explicit_universal_tm.py': '0a0f970df8dcf4dca5f8d105908b06f82fefb3e1948198ca2692fcb97b5da0e5', 'pcp_affine_factored_transports.py': 'ffc11e21cf08e3659848f4c59912ff4cc2fe0dc0d171a09294735cf7a08e4e2f', 'pcp_affine_slope_class_history.py': '4343629ab42a416ec1ce77d55120baeab7730f5cea9ebec50a2e83fdd2599bd0', 'pcp_uniform_affine_pair_history.py': 'c6e07c5eb3a46dc995ae722607c894e43e4b7438adc9af05bcb04f98a8e80b40', 'pcp_uniform_affine_pair_units.py': '5bac5fc3e24781aefbca30273672fa9f9c5b19b3105b8498101e46e30a476d9d'}
DEPENDENCY_ROOT=Path(importlib.util.find_spec('gpcp_fixed_program_input_bridge').origin).resolve().parent
def source_guard():
 for name,expected in SOURCE_PINS.items():
  if hashlib.sha256((DEPENDENCY_ROOT/name).read_bytes()).hexdigest()!=expected:
   raise ValueError('source hash mismatch: '+name)
source_guard()
import gpcp_fixed_program_input_bridge as bridge
import neary_woods_explicit_universal_tm as nw

M=2**32-1
DIVISOR=257
DENOM=M//DIVISOR
low=lambda word:sum(int(c=='b')<<j for j,c in enumerate(word))
A1=nw.a_code(1);A2=nw.a_code(2)
C0=low(A1+A2);C1=low(A2+A1);DELTA=C1-C0
assert (C0,C1,DELTA,DENOM)==(3937053418,3941247658,4194240,16711935)

def build(scaled=False):
 if type(scaled) is not bool:raise TypeError('scaled must be an exact bool')
 source_guard()
 old=bridge.recoder(32)
 source=list(old['source'])+[
  ('raw_Q_term','*','program_A','Q'),
  ('raw_z_term','*','program_B','z'),
  ('raw_sum','+','raw_Q_term','raw_z_term')]
 if scaled:
  source+=[('raw_output','-','raw_sum','program_D')]
  pair=('R0','raw_output')
 else:
  source += [('raw_scaled_R','*',DENOM,'R0'),
             ('raw_shifted_R','+','raw_scaled_R','program_D')]
  pair=('raw_shifted_R','raw_sum')
 comparisons=list(old['comparisons'])+[('L0','program_L'),pair]
 params=['x','program_L','program_A','program_B','program_D','L0','R0']
 aux=['z']+list(old['auxiliaries'])
 known=set(params+aux)
 for name,op,a,b in source:
  assert name not in known and all(type(v) is int or v in known for v in (a,b))
  known.add(name)
 assert all(all(type(v) is int or v in known for v in pair) for pair in comparisons)
 out=dict(source=source,comparisons=comparisons,parameters=params,auxiliaries=aux)
 sos,last=bridge.raw.sos_source(out)
 counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
 sc=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
 assert len(aux)==50 and len(comparisons)==36
 assert (len(source),counts)==((137,{'M':72,'A':65}) if scaled else (138,{'M':73,'A':65}))
 assert (len(sos),sc)==((244,{'M':108,'A':136}) if scaled else (245,{'M':109,'A':136}))
 return dict(out,scaled=scaled,sos_source=sos,sos_output=last,
             ledger={'certificate':len(source),'M':counts['M'],'A':counts['A'],
                     'equations':36,'positive_witnesses':50,'SOS':len(sos),
                     'SOS_M':sc['M'],'SOS_A':sc['A']})

def parameters(q,h,productions,right,left,scaled=False):
 if type(scaled) is not bool:raise TypeError('scaled must be an exact bool')
 if any(type(v) is not int for v in (q,h,right,left)):
  raise TypeError('q,h and marker indices must be exact integers')
 if q<2 or h<2 or not 1<=right<=q or not 1<=left<=q:
  raise ValueError('invalid bi-tag alphabet/marker domain')
 if type(productions) is not dict or any(type(k) is not tuple or len(k)!=2 or
       any(type(v) is not int for v in k) for k in productions):
  raise TypeError('productions must have exact integer-pair keys')
 if set(productions)!={(j,i) for j in range(1,h) for i in range(1,q+1)}:
  raise ValueError('incomplete active production table')
 for output in productions.values():
  if type(output) is not tuple or len(output) not in (2,3) or any(type(v) is not int for v in output):
   raise TypeError('production outputs must be exact integer tuples of length2 or3')
  if not all(1<=v<=q for v in output[:-1]) or not 1<=output[-1]<=h:
   raise ValueError('production output index outside alphabet')
 source_guard()
 program=nw.bts_program(q,h,productions)
 kappa=1<<(16*q);rho=2*(kappa-1)//3
 tail=nw.a_code(right)+nw.a_code(left);sigma=low(tail)
 L=low((program+'b')[::-1])
 numerators=(kappa*(sigma*M+C0),M*kappa*DELTA,kappa*C0-M*rho)
 assert all(v%DIVISOR==0 for v in numerators)
 a,b,d=(v//DIVISOR for v in numerators)
 assert d==(1073741888*kappa+2863311530)//DIVISOR
 assert all(type(v) is int and v>0 for v in (L,a,b,d))
 return dict(program_L=DENOM*L if scaled else L,program_A=a,program_B=b,program_D=d)

def verify():
 records=[];offzero=0;orientation=0;outer=0
 packets=[build(scaled) for scaled in (False,True)]
 rng=random.Random(20261002)
 for packet in packets:
  for case in range(96):
   v={n:rng.randrange(1,8) if case<48 else rng.randrange(-4,5)
      for n in packet['parameters']+packet['auxiliaries']}
   e=bridge.execute(packet['sos_source'],v)
   parent=bridge.recoder(32)
   pe=bridge.execute(parent['source'],v)
   residuals=[pe[a]-pe[b] for a,b in parent['comparisons']]
   residuals += [v['L0']-v['program_L']]
   rhs=v['program_A']*v['q']**32+v['program_B']*v['z']
   residuals += [v['R0']-(rhs-v['program_D']) if packet['scaled']
                 else DENOM*v['R0']+v['program_D']-rhs]
   assert e[packet['sos_output']]==sum(r*r for r in residuals)
   offzero+=1
  # Literal univariate restriction proves degree66 is attained. The usual
  # formal degree propagation alone overestimates internal norm cancellations.
  t=sp.Symbol('t')
  v={n:sp.Poly((1+i%3)*t+i+1,t) for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
  env=bridge.execute(packet['source'],v)
  residuals=[env[a]-env[b] for a,b in packet['comparisons']]
  degree=max(p.degree() for p in residuals)
  top=sum(int(p.LC())**2 for p in residuals if p.degree()==degree)
  assert degree==33 and top>0
  records.append(dict(ledger=packet['ledger'],source=packet['source'],
                      comparisons=packet['comparisons'],parameters=packet['parameters'],
                      auxiliaries=packet['auxiliaries'],scaled=packet['scaled'],
                      SOS_source=packet['sos_source'],SOS_output=packet['sos_output'],
                      exact_degree=66,degree_scope='Upper bound inherited from generic-width recoder proof; attained by this exact univariate specialization.',
                      leading_restriction=str(top)))
 for q in (2,3,5):
  for h in (2,3):
   productions={(j,i):((i%q)+1,j+1) for j in range(1,h) for i in range(1,q+1)}
   right,left=q,q-1
   for x in range(1,128):
    for padding in range(3):
     n=max(2,x.bit_length()+padding)
     bits=[(x>>j)&1 for j in range(n)]
     data=[('e',1)]+[('a',i) for b in bits for i in ((1,2) if b==0 else (2,1))]+[('a',right),('a',left)]
     contents,head=nw.encoded_configuration(q,h,productions,data)
     assert contents[head]=='c'
     rawL=low(contents[:head][::-1]);rawR=low(contents[head+1:])
     zz=sum(b<<(32*j) for j,b in enumerate(bits));Q=1<<(32*n)
     for packet in packets:
      p=parameters(q,h,productions,right,left,packet['scaled'])
      lhs=DENOM*rawR if packet['scaled'] else rawR
      assert (p['program_A']*Q+p['program_B']*zz-p['program_D'])==DENOM*rawR
      assert p['program_L']==(DENOM*rawL if packet['scaled'] else rawL)
      vals={name:1 for name in packet['parameters']+packet['auxiliaries']}
      vals.update(bridge.outer_fixture(x,n,32));vals.update(p)
      vals.update(L0=p['program_L'],R0=lhs)
      e=bridge.execute(packet['source'],vals)
      assert [e[a]-e[b] for a,b in packet['comparisons'][:5]]==[0]*5
      assert [e[a]-e[b] for a,b in packet['comparisons'][-2:]]==[0,0]
      outer+=1
     orientation+=1
 return dict(status='PASS',source_pins=dict(SOURCE_PINS),block0=A1+A2,block1=A2+A1,
             c0=C0,c1=C1,difference=DELTA,original_denominator=M,common_divisor=DIVISOR,
             primitive_denominator=DENOM,forms=records,
             checks={'full_offzero_SOS_cases':offzero,'signed_offzero_cases':96,
                     'literal_encoded_configurations':orientation,'actual_outer_source_substitutions':outer},
             scope='Complete paid input relation inherited from existing recoder theorem, plus checked literal source. Native Pell witnesses not materialized. No unbounded-history or universal operation improvement.')

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--write-receipt',action='store_true')
 args=parser.parse_args()
 result=json.loads(json.dumps(verify()))
 path=HERE/(Path(__file__).stem+'.json')
 if args.write_receipt:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 elif result!=json.loads(path.read_text()):raise ValueError('receipt mismatch')
 print(json.dumps(dict(status=result['status'],checks=result['checks'],ledgers=[v['ledger'] for v in result['forms']]),indent=2))
