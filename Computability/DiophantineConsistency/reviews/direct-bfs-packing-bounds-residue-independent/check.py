#!/usr/bin/env python3
"""Inspect frozen author receipts and current direct object selection; no Lean replay."""
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2]; R=D/'research'
rows=[('direct-bfs-kernel-bound-prototype','DirectBFSKernelBound','directbfskernelbound-attempt04',['DirectBFSKernelBound.kernel_lt'],'fe44d4e7ca87794e9c2a24c906556ce7bbfc74544d941474322707c516c86766'),('direct-bfs-cell-product-prototype','DirectBFSCellProduct','directbfscellproduct-attempt03',['DirectBFSCellProduct.symbolic_kernel_lt','DirectBFSCellProduct.product_lt','DirectBFSCellProduct.normalized_cell_product_lt'],'de7be1d66656ef004648213f356b1c50cea49e6fc6e713e4cff23349630fa937'),('direct-bfs-kernel-block-size-prototype','DirectBFSKernelBlockSize','directbfskernelblock-attempt02',['DirectBFSKernelLowProduct.rho_pow_cast','DirectBFSKernelLowProduct.kernel_split_model','DirectBFSKernelLowProduct.lower_bound_model','DirectBFSKernelLowProduct.low_product_lt','DirectBFSKernelLowProduct.low_product_remainder','DirectBFSKernelBlockSize.high_product','DirectBFSKernelBlockSize.high_product_lt','DirectBFSKernelBlockSize.cell_sum_of_small'],'6daaf3f4001a6395c65387c3f406f9e4e4f59d52d75a74261db3e082fc25f866'),('direct-bfs-word-block-positive-prototype','DirectBFSWordBlockPositive','directbfsblockpositive-attempt01',['DirectBFSWordBlockPositive.packedCell_pos','DirectBFSWordBlockPositive.block_pos'],'a0717f51a636c98831113f6f9cea53aca4181bc88f59f063f21d6ace8e325cf1'),('direct-bfs-origin-block-residue-prototype','DirectBFSOriginBlockResidue','directbfsoriginblock-attempt01',['DirectBFSOriginBlockResidue.low_dvd_four','DirectBFSOriginBlockResidue.high_dvd_four','DirectBFSOriginBlockResidue.marked_origin_block_mod_four','DirectBFSOriginBlockResidue.normalized_high_fields'],'5c1df859f41c440ae1f47ddf30f64152f60d6de9ebc80046f70db614e299093a')]
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
for dirname,name,attempt,theorems,output in rows:
 p=R/dirname;s=p/(name+'.lean');run=p/({'DirectBFSKernelBound':'run-v4.py','DirectBFSCellProduct':'run-v3.py','DirectBFSKernelBlockSize':'run-v2.py'}.get(name,'run.py'));o=p/'observations'/attempt;rec=json.loads((o/'terminal.json').read_text())
 assert rec['exit']==0 and rec['reason'] is None and rec['pins']==rec['after'] and rec['direct_imports']==rec['direct_imports_after']
 assert sha(s)==sha(o/'source.txt')==rec['pins']['source'] and sha(run)==rec['pins']['runner']
 assert not re.search(r'\b(?:sorry|admit)\b',s.read_text())
 assert sha(o/'stdout')==rec['stdout_sha256'] and sha(o/'stderr')==rec['stderr_sha256']
 assert sha(Path(rec['output_root'])/(name+'.olean'))==rec['object_sha256']==output
 logs=(o/'stdout').read_text()+(o/'stderr').read_text()
 for th in theorems:assert f"'{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in logs
 assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',logs)
 imports=[m for line in s.read_text().splitlines() if line.startswith('import ') for m in line[7:].split()]
 assert imports==[x['module'] for x in rec['direct_imports']]
 print(name,'source',sha(s),'runner',sha(run),'object',output,'terminal',sha(o/'terminal.json'))
 for imp in rec['direct_imports']:
  sel=next(Path(x)/(imp['module'].replace('.','/')+'.olean') for x in rec['lean_path'].split(':') if (Path(x)/(imp['module'].replace('.','/')+'.olean')).is_file())
  assert str(sel.resolve())==imp['path'] and sha(sel)==imp['sha256'] and sha(sel) in rec['pins']['extra']
  assert imp['sha256'] in run.read_text()
  print(' ',imp['module'],imp['path'],imp['sha256'])
print('PASS: receipt and current first-direct-selection checks; no Lean replay')
