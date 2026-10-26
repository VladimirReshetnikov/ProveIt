#!/usr/bin/env python3
"""Replay the entire new2963 tuple, including zero-weight physical positions."""
from pathlib import Path
import gzip,hashlib,importlib.util,json,subprocess,sys
ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
def need(ok,msg):
    if not ok:raise ValueError(msg)
def main():
    native=ROOT/'native2963';pins=json.loads((ROOT/'NATIVE_SOURCE_PINS.json').read_text())
    for row in pins['files']:
        raw=(native/row['path']).read_bytes();need(len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],'native source pin '+row['path'])
    p=native/'research/low-padding-independent/certify.py'
    cp=subprocess.run([sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])+[str(p)],check=True,capture_output=True,text=True)
    need(not cp.stderr,'Pclp stderr');pcs=json.loads(cp.stdout);need(pcs['status']=='PASS','Pclp status')
    spec=importlib.util.spec_from_file_location('native2963_pinned_model',p);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    _,seed,actions,tiles,c,support=mod.model();whole,_=mod.constants(c,support)
    binding=json.loads((native/'candidates/one-page-low-padding2963/polynomial.json').read_text())['coefficient_binding'];total=0
    for port,key in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
        item=binding['ports'][port];packed=(native/'candidates/one-page-low-padding2963/coefficients'/item['file']).read_bytes();raw=gzip.decompress(packed)
        need(hashlib.sha256(packed).hexdigest()==item['gzip_sha256'],'gzip '+port);need(hashlib.sha256(raw).hexdigest()==item['raw_sha256'],'raw '+port)
        need(int.from_bytes(raw,'big')==whole[key],'fresh full tuple '+port);need(len(raw)==(whole[key].bit_length()+7)//8,'canonical encoding '+port);total+=len(raw)
    need(total==69685 and len(c)==3297 and len(support)==978 and sum(bool(v) for v in c)==976,'all physical and weighted positions')
    need(c[977]==c[1005]==0 and {977,1005}<=support and c[978]==1024,'zero-weight marker and dummy')
    dc=mod.dc_coefficients(c,mod.SPEC);need(dc[1005]==1 and sorted(e for e,v in dc.items() if v==1)==[18,1005],'physical Start-copy and temporal monomials')
    need(len(tiles)==942 and len(seed)==436 and len(actions)==430,'whole indexed language')
    print(json.dumps({'status':'PASS','source_files':len(pins['files']),'Pclp':pcs,'raw_bytes':total,'largest_bits':max(v.bit_length() for v in whole.values()),'physical_support':{'coefficient_slots':len(c),'physical_positions':len(support),'weighted_positions':sum(bool(v) for v in c),'zero_weight_dummy':977,'zero_weight_Start_marker':1005,'Start_copy_coefficient':dc[1005]},'seed_characters':len(seed),'actions':len(actions),'tiles':len(tiles)},indent=2))
if __name__=='__main__':main()
