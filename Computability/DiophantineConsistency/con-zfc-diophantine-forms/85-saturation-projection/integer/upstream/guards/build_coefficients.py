#!/usr/bin/env python3
"""Regenerate authentic native coefficients plus both new fixed guard scales."""
from pathlib import Path
import gzip, hashlib, importlib.util, json, sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent

def need(ok, msg):
    if not ok: raise ValueError(msg)

def build():
    path=ROOT/'upstream/source34/source34_builder.py'
    raw=path.read_bytes()
    need(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='b85e416b8a8b823c01c8ecacd85eebef7f5c69b5','source34 builder Git blob')
    spec=importlib.util.spec_from_file_location('source34',path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    ports,audit=mod.construct()
    native=json.loads((ROOT/'upstream/source34/source34_binding.json').read_text())
    for k,v in ports.items():
        raw=v.to_bytes((v.bit_length()+7)//8,'little')
        need(hashlib.sha256(raw).hexdigest()==native['payloads'][k]['sha256'],'actual native coefficient '+k)
    beta=ports['beta']; rho=1<<121
    T=ports['K']-beta*rho+1; A=1<<398816; H=1<<265716
    need(T>0 and 2*(T+1)*(A+H)<beta,'universal weighted-cone numeral inequality')
    c0=105534389824824194647382298625
    tile=json.loads((ROOT/'upstream/source34/wang943_tiles.json').read_text())[0]
    computed=1+sum(1<<(10+2*(10*t+j)) for t,lab in enumerate(tile) for j in range(10) if ((lab+512)>>j)&1)+sum(1<<(10+2*j) for j in range(40,44))
    need(computed==c0,'literal leading tile coefficient')
    need((1<<96)<=c0<c0+1<=3*(1<<95),'determinant leading block interval')
    need(121*8791+1113==1064921-97 and 121*3296+666104==1064921-1,'determinant scale exponent alignments')
    need(beta==(1<<1064921)-1 and beta%3==1,'authentic odd Mersenne exponent')
    values={'beta':beta,'K0':ports['K'],'MC':ports['MC'],'MF':ports['MF_source'],'cone_A':1<<1113,'cone_B':1<<666104,'Walpha':2*T*A,'WC':T*beta}
    need(0<values['MC']<beta<values['MF']<2*beta and values['K0']>=0,'source mask inequalities')
    records={}; out=ROOT/'coefficients';out.mkdir(exist_ok=True)
    for k,v in values.items():
        raw=v.to_bytes((v.bit_length()+7)//8,'little');packed=gzip.compress(raw,mtime=0)
        (out/(k+'.bin.gz')).write_bytes(packed)
        records[k]={'path':'coefficients/'+k+'.bin.gz','bits':v.bit_length(),'raw_bytes':len(raw),'raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_sha256':hashlib.sha256(packed).hexdigest()}
    result={'status':'PASS exact finite numeral reconstruction','backend':'mixed-parity-unrounded-1064921','format':'gzip of minimal unsigned little-endian integer bytes','path_base':'directory containing COEFFICIENT_BINDING.json','MF_convention':'MF is already shifted by beta; do not shift again','recipes':{'cone_A':'2^1113','cone_B':'2^666104','Walpha':'2*(K0-beta*2^121+1)*2^398816','WC':'(K0-beta*2^121+1)*beta'},'payloads':records,'determinant_total_raw_bytes':sum(records[k]['raw_bytes'] for k in ('beta','K0','MC','MF','cone_A','cone_B')),'cone_total_raw_bytes':sum(records[k]['raw_bytes'] for k in ('beta','K0','MC','MF','Walpha','WC')),'native_finite_audit':audit,'proof_scope':'Finite numeral and geometry checks do not prove unbounded native calibration or an internal ZFC consistency biconditional.'}
    (ROOT/'COEFFICIENT_BINDING.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','determinant_total_raw_bytes','cone_total_raw_bytes')},indent=2))
    return values
if __name__=='__main__':build()
