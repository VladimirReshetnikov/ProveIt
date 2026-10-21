#!/usr/bin/env python3
"""Positive and negative local-block controls for the bounded fold search."""
from pathlib import Path
import argparse,hashlib,json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError('Run without -O; assertions are required.')
sys.dont_write_bytecode=True
from search import read,block

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 assert sha(a.baseline)=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
 T=read(a.baseline);assert 400 not in{q for q,b in T}
 assert T[69,0]==(0,-1,213)and T[69,1]==(1,1,31)and T[100,0]==(0,1,69)
 # Unfold the accepted marker construction into its two precursor states.
 T[69,0]=(0,1,105);T[400,0]=(0,1,104);T[400,1]=(1,1,31);T[100,0]=(0,1,400)
 keep=block(T,69,400,0,(0,-1,213),{-1:1})
 drop=block(T,400,69,0,(0,-1,213),{-1:0})
 corrupt=block(T,69,400,0,(0,1,254),{-1:1})
 assert keep==[3]and drop==[3]and corrupt is None
 B=read(a.baseline)
 cyclic_keep=block(B,8,127,1,(1,-1,110),{-1:1})
 cyclic_drop=block(B,127,8,1,(1,-1,110),{-1:0})
 assert cyclic_keep is None and cyclic_drop is None
 report={'status':'CONTROLS_PASS','baseline_sha256':sha(a.baseline),'known_69_400_fold':{'keep_duration':[3],'drop_duration':[3],'both_universal_local_blocks_accepted':True},'early_halt_corruption_rejected':True,'cyclic_8_127_provider_rejected_for_both_origins':True,'search_script_sha256':sha(Path(__file__).with_name('search.py')),'control_script_sha256':sha(Path(__file__)),'scope':'Finite controls of the local synthesis filter. They are not an exhaustive correctness proof for the search program or a state-count lower bound.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
