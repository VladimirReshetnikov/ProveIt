"""Regenerate all five stages from the supplied pinned integer polynomial."""
from pathlib import Path
import argparse,sys,json,hashlib
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import strict_horizon,build_basis,build_pools,shear_pell,linear_beta

def main(output):
 parent=ROOT/'inputs'/'parent245.json'
 digest=hashlib.sha256(parent.read_bytes()).hexdigest()
 if digest!='1a42dd3a148c3084cd95a367869d251ed92e2f9852397215e4909e70b03d278e':raise ValueError('pinned P245 bytes changed')
 strict_horizon.main(parent,output/'strict241')
 build_basis.build(output/'strict241'/'equation241.json',output/'basis238')
 build_pools.main(output/'basis238'/'equation.json',output/'pooled226')
 shear_pell.main(output/'pooled226'/'equation.json',output/'differences226')
 linear_beta.main(output/'differences226'/'equation.json',output/'principal225')
 print(json.dumps({'result':'reconstructed','final_equation':str(output/'principal225'/'equation.json')}))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'stages');a=ap.parse_args();main(a.output)
