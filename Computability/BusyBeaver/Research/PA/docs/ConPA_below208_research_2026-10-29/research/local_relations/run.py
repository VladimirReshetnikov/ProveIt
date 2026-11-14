#!/usr/bin/env python3
"""Validate retained receipts, or reproduce a specified bounded search."""
import argparse,hashlib,json,re,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def require(c,m):
    if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse_headshift(path):
    text=path.read_text();match=re.search(r'^DONE pairs (\d+) actions (\d+) hits (\d+)$',text,re.M)
    require(match is not None,'Missing completion marker: '+str(path))
    require(not any(line.startswith('HIT ')for line in text.splitlines()),'Unexpected survivor: '+str(path))
    return tuple(map(int,match.groups()))
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--mode',choices=['verify','headshift','block'],default='verify');p.add_argument('--output',type=Path,default=ROOT/'replay');a=p.parse_args();m=json.loads((ROOT/'manifest.json').read_text())
    for n,h in m['inputs'].items():require(sha(ROOT/'inputs'/n)==h,'Input hash mismatch: '+n)
    for n,h in m['evidence_hashes'].items():require(sha(ROOT/n)==h,'Evidence hash mismatch: '+n)
    expected=(36639,60674184,0)
    receipts={tag:parse_headshift(ROOT/'evidence'/f'headshift_{tag}.log')for tag in('A','B')}
    require(all(v==expected for v in receipts.values()),'Headshift counts differ')
    b=json.loads((ROOT/'evidence/block_cluster_A.json').read_text())
    require((b['pairs'],b['trials'],b['survivors'],b['results'])==(1854,3070224,20,[]),'Block-cluster receipt differs')
    partial=json.loads((ROOT/'partial/208A_source_block_verified.json').read_text())
    require(partial['tested']==212 and partial['accepted']==[],'Partial refinement receipt differs')
    a.output.mkdir(parents=True,exist_ok=True)
    if a.mode=='headshift':
        with tempfile.TemporaryDirectory(prefix='local-relations-')as tmp:
            executable=Path(tmp)/'headshift'
            subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'shift_quotient_screen.cpp'),'-o',str(executable)],check=True)
            for tag in('A','B'):
                log=a.output/f'headshift_{tag}.log'
                with log.open('w')as stream:subprocess.run([str(executable),str(ROOT/'inputs'/f'u208_{tag}.native.tm'),str(ROOT/'inputs'/f'contexts12_{tag}.txt'),'71'],stdout=stream,stderr=subprocess.STDOUT,check=True)
                require(parse_headshift(log)==expected,'Reproduced headshift census differs')
    if a.mode=='block':
        output=a.output/'block_cluster_A.json'
        with(a.output/'block_cluster_A.log').open('w')as stream:subprocess.run([sys.executable,str(ROOT/'block_quotient208.py'),str(ROOT/'inputs/u208_A.native.tm'),'--depth','9','--limit','31','--cluster','163,211,217,215,157,184,67,148,186','--output',str(output)],stdout=stream,stderr=subprocess.STDOUT,check=True)
        reproduced=json.loads(output.read_text());require((reproduced['pairs'],reproduced['trials'],reproduced['survivors'],reproduced['results'])==(1854,3070224,20,[]),'Reproduced block-cluster census differs')
    report={'status':'RETAINED_INPUTS_AND_COMPLETED_RECEIPTS_VERIFIED','mode':a.mode,'headshift_counts_per_class':expected,'block_cluster_counts':[1854,3070224,20,0],'partial_extension_complete':False,'fresh_search_executed':a.mode!='verify'}
    (a.output/'verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
