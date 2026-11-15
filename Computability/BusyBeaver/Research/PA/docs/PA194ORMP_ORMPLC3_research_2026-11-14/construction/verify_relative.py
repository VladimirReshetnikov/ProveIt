#!/usr/bin/env python3
"""Bind the OR+MP construction directly to the exact revised AX11H parent.

This checks finite data for the accompanying written relative iPRA argument.
It does not replace arithmetic soundness of the symbolic event rules.
"""
from pathlib import Path
import json,hashlib,zipfile,argparse
import relative_inspector as r
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def no_early_halt(folder, replay=None):
 """Every recorded primitive edge and all expanded list lemmas avoid halt.

 Literal contracts record all literal and unary rows. List events are
 separately expanded into their checked one-block traces; list induction
 then supplies the same no-halt fact for an arbitrary finite tail.
 """
 native=r.table(folder/'machine.native.tm')
 mapping={int(k):v for k,v in read(HERE/'independent_vendor/legacy_mapping.json').items()}
 for q in {q for q,b in native}|{254}:mapping.setdefault(q,q+10000)
 symbolic={(mapping[q],b):(w,d,mapping[n])for(q,b),(w,d,n)in native.items()}
 evidence=replay or folder/'independent'
 blocks=read(evidence/'list_lemmas.json')
 for block in blocks:
  for event in block['trace']:
   assert event[0]in('literal','unary')
   q,b,w,d,n=event[1]
   assert symbolic[q,b]==(w,'R'if d==1 else'L',n)
   assert q!=254 and n!=254
 sites=read(folder/'sites.json');contracts=read(evidence/'contracts.json')
 normal=halt=0
 for contract in contracts:
  terminal=[(q,b)for q,b in contract['rows']if symbolic[q,b][2]==254]
  if sites[contract['site']][1]=='halt':
   assert len(terminal)==1 and contract['duration']==[3]+[0]*12
   halt+=1
  else:
   assert not terminal
   normal+=1
 assert (normal,halt)==(4777,1)
 return {'nonhalting_contracts_without_halt_edges':normal,'unique_halt_outcomes':halt,'one_block_traversals_without_halt_edges':len(blocks)}
def reader(rows,start,words):
 out=[]
 for word,target in words:
  q=start;trace=[]
  for symbol in word:
   b=int(symbol);w,d,n=rows[q,b]
   assert (w,d)==(b,'R')
   trace.append([q,b,n]);q=n
  assert q==target
  out.append({'word':word,'target':target,'trace':trace})
 depth=max(len(w) for w,t in words)
 assert sum(2**(depth-len(w))for w,t in words)==2**depth
 assert all(not b.startswith(a) for a,t in words for b,u in words if a!=b)
 return out
def main(candidate=None,parent_folder=None,parent_replay=None,output=None):
 assert __debug__
 parent=parent_folder or HERE/'parent';child=candidate or HERE/'machine';vendor=HERE/'independent_vendor'
 replay=parent_replay or HERE/'parent_replay'
 name=read(child/'receipt.json')['name']
 assert name in ('PA194ORMP','PA194ORMPLC3')
 expected={'PA194ORMP':('a0473681d6d5fb68e5fccfc473f35bc67aa48083d847e349ba3c52865f293629',154,58014),
           'PA194ORMPLC3':('6d8a8cf2f5578ccdc28dd7025bc41a7c279dfbc09c5d3893cb965d70292d10f4',449,58010)}[name]
 assert sha(child/'machine.tm')==expected[0]
 zpath=HERE/'calibration_AX11H.zip'
 assert sha(zpath)=='93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075'
 with zipfile.ZipFile(zpath)as z:
  prefix='pa194_ax11h_research_2026-11-14/machines/PA194AX11H/'
  for f in ['machine.tm','machine.native.tm','sites.json','instructions.json','labels.json','independent/contracts.json']:
   assert (parent/f).read_bytes()==z.read(prefix+f)
 ps,pi,pf=r.inspect(parent,vendor);cs,ci,cf=r.inspect(child,vendor)
 assert pi==ci
 op_changes=[i for i,(a,b)in enumerate(zip(ps,cs))if a[1:]!=b[1:]]
 assert len(op_changes)==(0 if name=='PA194ORMP' else 61)
 assert all(ps[i][1:]==['continueTo',2]and cs[i][1:]==['continueTo',3]for i in op_changes)
 assert ps[25]==cs[25]==['1000000','dec',8]
 assert cf['max_address_length']==37
 changed=[i for i,(a,b)in enumerate(zip(ps,cs))if a[0]!=b[0]]
 assert len(changed)==expected[1]
 if name=='PA194ORMP':assert changed==list(range(224,291))+list(range(3572,3659))
 replay_receipt=read(replay/'receipt.json')
 assert replay_receipt['status']=='PASS'
 assert replay_receipt['dense_sha256']==sha(parent/'machine.tm')
 assert replay_receipt['native_sha256']==sha(parent/'machine.native.tm')
 assert replay_receipt['contracts_sha256']==sha(replay/'contracts.json')
 inherited=read(parent/'independent/contracts.json');fresh=read(replay/'contracts.json')
 assert len(inherited)==len(fresh)==4778
 assert all({k:new[k]for k in old}==old for old,new in zip(inherited,fresh))
 old,new=r.table(parent/'machine.native.tm'),r.table(child/'machine.native.tm')
 history=[]
 for bit,length in [(0,3),(1,2)]:
  tape={-1:bit,0:0};a,ta=r.local_run(old,69,0,tape,length);b,tb=r.local_run(new,69,0,tape,length)
  assert a==b
  assert a==((104,1,tape)if bit==0 else(90,0,tape))
  assert all(row[1]in(-1,0)for row in ta+tb)
  history.append({'bit':bit,'steps':length,'old':ta,'new':tb,'endpoint':a})
 result={'status':'PASS','name':name,'calibrated_parent':'PA194AX11H','parent':pf,'candidate':cf,'source_instruction_arrays_identical':True,'changed_source_addresses':changed,'changed_source_address_count':len(changed),'control_retagged_sites':op_changes,'history_selector_cases':history,
 'old_operand_reader':reader(old,213,[('00',104),('010',107),('011',98),('1',90)]),
 'new_operand_reader':reader(new,213,[('0',104),('10',107),('110',98),('111',90)]),
 'old_MP_reader':reader(old,100,[('00',213),('01',28),('10',77),('11',114)]),
 'new_MP_reader':reader(new,100,[('0',213),('10',28),('110',77),('111',114)]),
 'calibration_archive_sha256':sha(zpath),'parent_replay_contracts_sha256':sha(replay/'contracts.json'),'parent_replay_matches_all_inherited_duration_fields':True,'parent_no_early_halt':no_early_halt(parent,replay),'candidate_no_early_halt':no_early_halt(child),'scope':'Exact source, literals, complete frame closure and polynomial witness bounds for written relative iPRA proof; no new Lean kernel theorem.'}
 assert pf['max_duration_coefficients']==cf['max_duration_coefficients']==[534,8,4,4,4,4,4,4,2,4,4,2,2]
 for info,start in [(pf,57922),(cf,expected[2])]:
  assert info['physical_time_bound']=={'startup':start,'alpha':698,'beta':18,'formula':'startup + alpha*k + beta*k*(k-1)/2'}
 output=output or HERE/('relative_receipt.json'if name=='PA194ORMP'else'accelerated_relative_receipt.json')
 output.parent.mkdir(exist_ok=True,parents=True);output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k]for k in ['status','name','calibrated_parent','changed_source_address_count']},indent=2))
 print(f'clock bound: parent 57922+9*k*k+689*k; child {expected[2]}+9*k*k+689*k')
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--candidate',type=Path);parser.add_argument('--parent',type=Path)
 parser.add_argument('--parent-replay',type=Path);parser.add_argument('--output',type=Path)
 args=parser.parse_args();main(args.candidate,args.parent,args.parent_replay,args.output)
