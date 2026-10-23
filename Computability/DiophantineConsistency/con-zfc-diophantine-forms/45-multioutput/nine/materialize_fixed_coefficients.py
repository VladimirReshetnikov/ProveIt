#!/usr/bin/env python3
"""Materialize every live fixed coefficient for the new nine-variable equation."""
from pathlib import Path
import json,gzip,hashlib
ROOT=Path(__file__).resolve().parent

def main():
 circuit=json.loads((ROOT/'generated/multitarget_nine_positive.json').read_text());ports=[];records=[]
 for name,fn in zip(['beta','K0','MC','MF'],['beta.bin.gz','K.bin.gz','MC.bin.gz','MF_source.bin.gz']):
  path=ROOT.parent/'sun/upstream/signed10/data'/fn;raw=gzip.decompress(path.read_bytes());x=int.from_bytes(raw,'little');ports.append(x)
  records.append({'name':name,'file':str(path.relative_to(ROOT.parent)),'encoding':'unsigned little endian, gzip','raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'raw_byte_length':len(raw),'bit_length':x.bit_length()})
 assert [x.bit_length() for x in ports]==circuit['port_bit_lengths']
 live={n['name'] for n in circuit['nodes'] if n['kind']=='fixed'};values={};recipes={r['name']:r['terms'] for r in circuit['coefficient_recipes']}
 for name in live:
  if name=='base_floor':values[name]=1<<circuit['base_floor_exponent'];continue
  value=0
  for t in recipes[name]:
   x=t['coefficient']
   for p,e in zip(ports,t['powers']):x*=p**e
   value+=x
  values[name]=value
 payloads=[];out=ROOT/'generated/fixed';out.mkdir(exist_ok=True)
 for name,x in sorted(values.items()):
  raw=bytes([int(x<0)])+abs(x).to_bytes(max(1,(abs(x).bit_length()+7)//8),'little');encoded=gzip.compress(raw,mtime=0);path=out/(name+'.bin.gz');path.write_bytes(encoded)
  payloads.append({'name':name,'file':str(path.relative_to(ROOT)),'encoding':'gzip of one sign byte (0 nonnegative,1 negative), followed by minimal unsigned little-endian magnitude','sign':-1 if x<0 else 1,'magnitude_bit_length':abs(x).bit_length(),'raw_byte_length':len(raw),'gzip_byte_length':len(encoded),'raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_sha256':hashlib.sha256(encoded).hexdigest(),'recipe':{'power_of_two':circuit['base_floor_exponent']} if name=='base_floor' else recipes[name]})
 cert=ROOT.parent/'quartic/QUADRATIC_TARGETS.json';parent=ROOT.parent/'review/sources/31-sun10/quartic31/quartic31_system60.json'
 result={'schema':'proveit-multitarget-nine-instance-v1','source_pin':'22e75dd6b87b1b199bb08c778d7cf075ae5aae08','scope':'New multi-target quadratic source and Jones numerical ratio bridge, not the legacy Sun index or old quartic polynomial','path_base':'round6_root for source/port paths; nine root for fixed payload paths','parent_file':str(parent.relative_to(ROOT.parent)),'parent_sha256':hashlib.sha256(parent.read_bytes()).hexdigest(),'quadratic_target_file':str(cert.relative_to(ROOT.parent)),'quadratic_target_sha256':hashlib.sha256(cert.read_bytes()).hexdigest(),'four_ports':records,'tuple':'complete package31 wang943-mixed-121x8801 tuple','base_floor_exponent':circuit['base_floor_exponent'],'coefficient_bound_exponent':circuit['coefficient_bound_power_of_two'],'all_live_fixed_leaves':sorted(live),'fixed_payloads':payloads,'fixed_payload_raw_bytes':sum(r['raw_byte_length'] for r in payloads),'fixed_payload_gzip_bytes':sum(r['gzip_byte_length'] for r in payloads),'domain':'nine strictly positive integers, or separately translated nine nonnegative integers','equivalence':'No zero iff Con(ZFC), provable in ZFC using stated arithmetic/compiler dependencies','proof':'MULTITARGET_NINE_PROOF.md','end_to_end_kernel_certificate':False}
 (ROOT/'MULTITARGET_INSTANCE.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['fixed_payload_raw_bytes','fixed_payload_gzip_bytes','all_live_fixed_leaves']}))
if __name__=='__main__':main()
