#!/usr/bin/env python3
"""Emit and independently coefficient-check one bounded Report48 replacement.
The historical ZIP and its source are inert authenticated data, never executed.
"""
import argparse,collections,hashlib,io,json,pathlib,subprocess,zipfile
REV='c5612efa171fa62470285049ee45d1d06ee25578'
ARCHIVE='docs/incoming/Exact_Fusion_of_the_Ant_Background_Polynomials_Package.zip'
ARCHIVE_SHA='45f8dcf697012fc67cd9155f76980787fef8ff3cb4f4746ef54c4c3375c7bb65'
BLOB='5c17a62cb5519c85608b9c6a50184e2d95347bc4'
MEMBERS={
 'Research_Report48/README.md':'03a15a36c708e530e3cd644526bbdcc0e2e06370fd2903703f6a3899c9ef6ae4',
 'Research_Report48/science/PROOF.md':'0a140e526a8c7e7ee5076204e258fdddd431d8c02e49dd9a8eff9a673d195af8',
 'Research_Report48/independent_audit/GENERIC_PROOF.md':'6bf435b17c1653c6e684df47a191b5cd4343940e361f39f8a59237453763855b',
 'Research_Report48/science/fusion_source.py':'5e433001dcdb4a26f7dcb0419a41f124fae983aeb76088d55d4b603802232f60',
 'Research_Report48/science/fused-receipt.json':'8230ba6bed0e6209f814094168551282252c709681cc0b744cace678e4b703ee',
}
KINDS=('DUP','NAND','MOVE_LEFT','MOVE_RIGHT')
CUTS=(0,1,2,480,481,482,960)
def require(test,why):
 if not test:raise ValueError(why)
def digest(x):return hashlib.sha256(x).hexdigest()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def port(kind,s):return 'T_'+kind+'_'+str(s)
def inputs(repo):
 raw=subprocess.check_output(['git','-C',str(repo),'show',REV+':'+ARCHIVE])
 require(len(raw)==2162628 and digest(raw)==ARCHIVE_SHA,'archive size/hash')
 require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==BLOB,'Git blob hash')
 z=zipfile.ZipFile(io.BytesIO(raw))
 require(z.testzip() is None,'ZIP CRC')
 result={}
 for n,h in MEMBERS.items():
  b=z.read(n);require(digest(b)==h,'member pin: '+n);result[n]=b
 return result
class Emitter:
 def __init__(self):self.rows=[]
 def op(self,op,a,b):
  name='r'+str(len(self.rows));self.rows.append([name,op,a,b]);return name
 def power(self,n):
  x='Y'
  for bit in bin(n)[3:]:
   x=self.op('*',x,x)
   if bit=='1':x=self.op('*',x,'Y')
  return x
 def horner(self,coeff):
  x=coeff[-1]
  for c in reversed(coeff[:-1]):x=self.op('+',self.op('*',x,'Y'),c)
  return x

def compile_component():
 e=Emitter();powers={1:'Y',478:e.power(478)};out={};blocks=[]
 for kind in KINDS:
  base=[port(kind,(480-j)%960) if (480-j)%960<957 else 'paid_zero' for j in range(960)]
  wires=[]
  for a,b in zip(CUTS,CUTS[1:]):
   wires.append(e.horner(base[a:b]));blocks.append({'kind':kind,'start':a,'length':b-a,'output':wires[-1]})
  for phase in [0,288000]:
   for b in range(3):
    rotation=b+phase//600;first=CUTS.index(rotation)
    order=list(range(first,6))+list(range(first))
    x=wires[order[-1]]
    for j in reversed(order[:-1]):
     x=e.op('+',e.op('*',x,powers[CUTS[j+1]-CUTS[j]]),wires[j])
    out[f'{kind}:{b}:{phase}']=x
 ports={'Y':{'parent_expression':'Fusion.Y = W^600','new_cost':0},'paid_zero':{'parent_expression':"prepared.labels['0'] = 1-1",'new_cost':0}}
 for kind in KINDS:
  for s in range(957):ports[port(kind,s)]={'parent_expression':['prepared','occ',kind,s],'new_cost':0}
 return {'source':e.rows,'outputs':out,'input_bindings':ports,'block_outputs':blocks,'paid_Y478_output':powers[478]}

def add(a,b):
 z=dict(a)
 for k,v in b.items():z[k]=z.get(k,0)+v
 return {k:v for k,v in z.items() if v}
def multiply(a,b):
 # Independent generic sparse arithmetic on polynomials linear in all T ports.
 z={}
 for (i,x),u in a.items():
  for (j,y),v in b.items():
   require(x=='1' or y=='1','unexpected product of two coefficient variables')
   k=(i+j,y if x=='1' else x);z[k]=z.get(k,0)+u*v
 return {k:v for k,v in z.items() if v}
def encode_poly(p):return [[i,x,v] for (i,x),v in sorted(p.items())]
def audit_component(packet):
 values={'Y':{(1,'1'):1},'paid_zero':{}}
 for k in KINDS:
  for s in range(957):values[port(k,s)]={(0,port(k,s)):1}
 counts=collections.Counter(); refs={};numeric={};coeff_checks=0
 for i,(name,op,a,b) in enumerate(packet['source']):
  require(name=='r'+str(i) and name not in values,'row order/uniqueness')
  require(a in values and b in values,'closure')
  require(op in ['+','*'],'opcode')
  values[name]=add(values[a],values[b]) if op=='+' else multiply(values[a],values[b])
  refs[name]=[a,b];counts[op]+=1
 require(counts=={'+':3936,'*':3950},'component ledger')
 require(values[packet['paid_Y478_output']]=={(478,'1'):1},'power478')
 certificates=[]
 for k in KINDS:
  for phase in [0,288000]:
   for b in range(3):
    name=f'{k}:{b}:{phase}';expected={}
    for s in range(957):expected[((480-b-s-phase//600)%960,port(k,s))]=1
    actual=values[packet['outputs'][name]]
    require(actual==expected,'coefficient identity '+name)
    coeff_checks+=len(expected)
    certificates.append({'output':name,'coefficient_terms':len(actual),'coefficient_sha256':digest(canonical(encode_poly(actual)))})
 used=set();todo=list(packet['outputs'].values())
 while todo:
  n=todo.pop()
  if n in used:continue
  used.add(n);todo+=refs.get(n,[])
 require(set(refs)<=used,'dead computed row')
 require(set(packet['input_bindings'])<=used,'unused input binding')
 # Separate finite-field arithmetic regression at three boundary and two generic bases.
 for y in [0,1,-1,2,19]:
  prime=1000003;v={'Y':y%prime,'paid_zero':0}
  for ki,k in enumerate(KINDS):
   for s in range(957):v[port(k,s)]=(ki*997+(s+1)**2)%prime
  for name,op,a,b in packet['source']:v[name]=((v[a]+v[b]) if op=='+' else v[a]*v[b])%prime
  for k in KINDS:
   for phase in [0,288000]:
    for b in range(3):
     exp=sum(v[port(k,s)]*pow(y,(480-b-s-phase//600)%960,prime) for s in range(957))%prime
     require(v[packet['outputs'][f'{k}:{b}:{phase}']]==exp,'numeric regression')
 return {'M':counts['*'],'A':counts['+'],'total':sum(counts.values()),'all_computed_rows_live':len(refs),'used_parent_input_bindings':len(packet['input_bindings']),'exact_output_polynomials':len(certificates),'exact_occurrence_terms':coeff_checks,'output_certificates':certificates,'supplementary_numeric_output_checks':120}

def verify(repo):
 data=inputs(repo);parent=json.loads(data['Research_Report48/science/fused-receipt.json'])
 packet=compile_component();audit=audit_component(packet)
 require(parent['source_sha256']==MEMBERS['Research_Report48/science/fusion_source.py'],'parent source receipt pin')
 old_M=24*959;old_A=24*959;save_M=old_M-audit['M'];save_A=old_A-audit['A']
 require([save_M,save_A]==[19066,19080],'savings')
 totals={}
 for arity in ['2','1']:
  j=parent['joins'][arity]
  require(j['fusion']['stages']['rotated_occurrence_horners_and_products']=={'M':23040,'A':23038,'total':46078},'old replaced stage')
  require(j['retained_old_main_gates']==(3461 if arity=='2' else 3471),'retained-main metadata')
  require(j['bound_constant_labels']==598 and j['variable_degree_preserved']==2304000,'inherited interface')
  totals[arity]={'M':j['M']-save_M,'A':j['A']-save_A,'total':j['total']-save_M-save_A,'positive_witnesses':j['positive_witnesses'],'equations':j['final_equations'],'exact_degree_inherited_by_polynomial_identity':j['variable_degree_preserved'],'evidence':'Derived ledger for specified grammar splice; no complete stream generated/rehashed','with_independent_endpoint_nine_M_splice_total':j['total']-save_M-save_A-9}
 require([totals[a]['total'] for a in ['2','1']]==[14620788,14620798],'derived full totals')
 return {'status':'PASS_COMPLETE_COMPONENT_AND_EXACT_COEFFICIENT_IDENTITIES','scope':'Complete emitted replacement component only; inherited whole-source grammar and ledgers, no historical Python execution','revision':REV,'archive':{'path':ARCHIVE,'sha256':ARCHIVE_SHA,'git_blob':BLOB,'size':2162628},'member_pins':MEMBERS,'grammar':{'block_boundaries':list(CUTS),'block_lengths':[1,1,478,1,1,478],'rotations':[0,1,2,480,481,482],'output_count':24,'new_literals':0,'new_witnesses':0,'new_equations':0},'component':packet,'component_audit':audit,'component_source_sha256':digest(canonical(packet)),'old_horner_only':{'M':old_M,'A':old_A,'total':old_M+old_A},'saved':{'M':save_M,'A':save_A,'total':save_M+save_A},'new_rotated_stage_including_unchanged_products_and_phase_sums':{'M':3974,'A':3958,'total':7932},'inherited_complete_source_ledgers':totals,'full_stream_generated':False,'archived_code_executed':False}

def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',required=True,type=pathlib.Path);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=pathlib.Path);g.add_argument('--expect',type=pathlib.Path);a=p.parse_args()
 r=verify(a.repo.resolve());encoded=json.dumps(r,indent=2)+'\n'
 # A canonical text comparison also rejects bool/int or other type substitutions.
 require(json.dumps(json.loads(encoded),indent=2)+'\n'==encoded,'typed JSON roundtrip')
 if a.expect:require(a.expect.read_text()==encoded,'exact saved receipt')
 else:
  with a.output.open('x') as f:f.write(encoded)
 print(json.dumps({'status':r['status'],'component':{k:r['component_audit'][k] for k in ['M','A','total']},'saved':r['saved'],'full_stream_generated':False}))
if __name__=='__main__':main()
