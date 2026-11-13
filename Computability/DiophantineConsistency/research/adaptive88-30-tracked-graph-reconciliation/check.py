#!/usr/bin/env python3
"""Bounded graph-census and literal-header search; no Lean or complete uniqueness claim."""
import collections,gzip,hashlib,json,re,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(45,45));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_bytes())
for f,h in pins.items():need(sha((r/f).read_bytes())==h,'pin '+f)
snapshot=json.loads((d/'snapshot.json').read_bytes());limit=snapshot['graph_file_max_bytes'];shapes=collections.Counter();hits=[];target='research/adaptive87-four-square-current88-30/graph.json'
for item in snapshot['tracked_exact_basenames']:
 f=r/item['path'];need(f.stat().st_size==item['bytes'],'size '+item['path'])
 if item['sha256'] is None:need(item['bytes']>limit,'oversize boundary');shapes['oversize']+=1;continue
 raw=f.read_bytes();need(sha(raw)==item['sha256'],'source '+item['path']);j=json.loads(raw)
 if not isinstance(j,dict):shapes['other_schema']+=1;continue
 w=j.get('witnesses');rows=j.get('source');ports=j.get('fixed_numerals')
 if not (isinstance(w,list) and isinstance(rows,list) and isinstance(ports,list) and all(isinstance(x,list) and len(x)==4 for x in rows)):shapes['other_schema']+=1;continue
 shapes['four_field_rows']+=1
 if len(w)==13 and len(ports)==4 and len(rows)==88:
  counts=dict(sorted(collections.Counter(x[1] for x in rows).items()));hits.append({'path':item['path'],'counts':counts})
matching=[x['path'] for x in hits if x['counts']=={'*':48,'+':22,'-':18}];need(matching==[target],'unexpected same-count candidate; inspect full graph')
# Parse the concrete, contiguous 13-variable/four-port literal header style.
lean=[]
for item in snapshot['lean_fin13_declaration_files']:
 raw=(r/item['path']).read_bytes();need(sha(raw)==item['sha256'],'Lean source '+item['path']);lines=raw.decode().splitlines()
 for i,line in enumerate(lines):
  if not re.search(r'let \w+ : Expr \(Fin 13\) := \.var 0\s*$',line):continue
  k=i+13
  if k+4>=len(lines) or not all(re.search(r'let \w+ : Expr \(Fin 13\) := \.var '+str(j)+r'\s*$',lines[i+j]) for j in range(13)):continue
  if not all(re.search(r'let \w+ : Expr \(Fin 13\) := \.constant \(\w+ '+str(j)+r'\)\s*$',lines[k+j]) for j in range(4)):continue
  n=k+4;ops=[]
  while n<len(lines) and (not lines[n].strip() or lines[n].lstrip().startswith('--')):n+=1
  while n<len(lines):
   m=re.fullmatch(r'\s*let (\w+) := (\w+) ([+*\-]) (\w+)\s*',lines[n])
   if not m:break
   ops.append(m.groups());n+=1
  if len(ops)==88:lean.append({'path':item['path'],'start_line':i+1,'counts':dict(sorted(collections.Counter(x[2] for x in ops).items()))})
need(len(lean)==3 and all(x['counts']=={'*':48,'+':23,'-':17} for x in lean),'Lean literal candidates changed')
# The compact and current graphs are different DAGs but have the same
# polynomial at the same symbolic ports, by the exact local identities below.
c=json.loads((r/'research/ordinary13-four-square88-30/candidate.json').read_bytes());t=json.loads((r/target).read_bytes());cr=c['source'];tr=t['source']
need(c['witnesses']==t['witnesses'] and c['fixed_numerals']==t['fixed_numerals'],'nearby graph leaves')
need(cr[:28]==tr[:28] and cr[35:76]==tr[35:76] and cr[78:80]==tr[78:80],'nearby shared gates')
need(cr[28:35]==[['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','M','folded_g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt']],'compact root cut')
need(tr[28:35]==[['root_skew','*','k','Bt'],['root_inner','-','g31','root_skew'],['root_scaled','*','M','root_inner'],['g33','*','Y','qm'],['root_btq3','*','Bt','q3'],['root_sum','+','root_scaled','g33'],['Z','-','root_sum','root_btq3']],'current root cut')
need(cr[76:78]==[['g80','+','g78','V'],['g81','*','u','g80']] and tr[76:78]==[['g80','*','V','V'],['g81','-','y2','g80']],'aux cut')
need(cr[80:]==[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam','-','Fa',1],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['sum01','+','A0sq','A1sq'],['sum23','+','Fam2','Fsm2'],['out','+','sum01','sum23']],'compact tail')
need(tr[80:]==[['fa_minus','-','Fa',1],['a0_sq','*','A0','A0'],['a1_sq','*','A1','A1'],['fa_sq','*','fa_minus','fa_minus'],['strong_sq','*','g72','g72'],['sum0','+','a0_sq','a1_sq'],['sum1','+','sum0','fa_sq'],['output','+','sum1','strong_sq']],'current tail')
# Sparse integer-polynomial verification of (V+u)^2-V^2=u*((V+u)+V).
def add(a,b,k=1):
 z=a.copy()
 for m,v in b.items():z[m]=z.get(m,0)+k*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for m,x in a.items():
  for n,y in b.items():
   k=tuple(i+j for i,j in zip(m,n));z[k]=z.get(k,0)+x*y
 return {m:v for m,v in z.items() if v}
V={(1,0):1};u={(0,1):1};y=add(V,u)
need(add(mul(y,y),mul(V,V),-1)==mul(u,add(y,V)),'exact auxiliary polynomial')
# Compare actual port numbers: compact44 uses little endian, 2011 big endian.
compact=r/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';cm=json.loads((compact/'ACTIVE_BINDING.json').read_bytes())['ports'];b=r/'candidates/one-page-padding-staircase-carrier65-2011';pm=json.loads((b/'polynomial.json').read_bytes())['coefficient_binding']['ports'];info={}
for n in ('beta','K0','MC','MF'):
 x=cm[n];y=pm[n];cz=(compact/x['path']).read_bytes();pz=(b/'coefficients'/y['file']).read_bytes();cr=gzip.decompress(cz);pr=gzip.decompress(pz)
 need(sha(cz)==x['sha256_gzip'] and sha(cr)==x['sha256_raw'] and len(cr)==x['raw_bytes'],'compact bytes '+n)
 need(sha(pz)==y['gzip_sha256'] and sha(pr)==y['raw_sha256'] and len(pr)==y['raw_bytes'],'2011 bytes '+n)
 ci=int.from_bytes(cr,'little');pi=int.from_bytes(pr,'big');need(ci!=pi,'port unexpectedly equal '+n)
 info[n]={'compact_bits':ci.bit_length(),'current2011_bits':pi.bit_length(),'numeric_equal':False}
print(json.dumps({'scope':'bounded pinned files/schema and exact literal-header style; excludes other JSON formats and Lean syntax','snapshot_sha256':sha((d/'snapshot.json').read_bytes()),'pinned_file_count':len(snapshot['tracked_exact_basenames']),'graph_shapes':dict(shapes),'13_input_4_port_88_row_hits':hits,'same_operation_census':matching,'fin13_lean_files':len(snapshot['lean_fin13_declaration_files']),'contiguous_lean_88_row_blocks':lean,'nearby_compact_symbolic_polynomial_identity':True,'compact44_vs_2011_ports':info},sort_keys=True,indent=2))
