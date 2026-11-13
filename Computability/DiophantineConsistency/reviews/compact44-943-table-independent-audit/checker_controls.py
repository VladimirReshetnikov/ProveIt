#!/usr/bin/env python3
"""Independently parse all 943 rows and exercise checker rejection controls."""
import ast,hashlib,json,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-943-table-prototype';SOURCE=PKG/'Compact943Data.lean';CHECKER=PKG/'check_rows.py';DATA=BASE/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json'
def need(b,m):
    if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    raw=SOURCE.read_text();begin='def rows : List (Nat × Nat × Nat × Nat) := [\n-- BEGIN PINNED ORDERED ROWS\n';end='\n-- END PINNED ORDERED ROWS\n]'
    need(raw.count(begin)==raw.count(end)==1,'list marker placement')
    block=raw.split(begin,1)[1].split(end,1)[0];parsed=ast.literal_eval('[\n'+block+'\n]');expected=json.loads(DATA.read_text())
    need(sha(DATA)=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f' and len(parsed)==len(expected)==943 and [list(row) for row in parsed]==expected,'ordered JSON rows')
    need(all(len(row)==4 and all(type(x) is int and 0<=x<bound for x,bound in zip(row,(256,512,256,512))) for row in parsed),'row bounds')
    results=[]
    def run(name,flags,src=None,expected_exit=1):
        cmd=[sys.executable,*flags,str(CHECKER)]
        if src is not None:cmd+=['--source',str(src)]
        p=subprocess.run(cmd,capture_output=True,text=True,timeout=30)
        need((p.returncode==0)==(expected_exit==0),'checker control '+name)
        results.append({'case':name,'exit':p.returncode})
    run('normal',['-I','-S'],expected_exit=0);run('optimized',['-O','-I','-S'])
    with tempfile.TemporaryDirectory(prefix='compact943-review-controls-') as d:
        path=Path(d)/'mutated.lean';lines=block.splitlines();swapped=lines.copy();swapped[0],swapped[1]=swapped[1],swapped[0]
        for name,new in [('swap_first_two','\n'.join(swapped)),('missing_comma','\n'.join([lines[0].removesuffix(','),*lines[1:]])),('changed_first','\n'.join([lines[0].replace('(2, 435, 3, 1)', '(2, 435, 3, 2)'),*lines[1:]]))]:
            path.write_text(raw.replace(block,new,1));run(name,['-I','-S'],path)
        path.write_text(raw+'\n-- BEGIN PINNED ORDERED ROWS\n');run('duplicate_marker',['-I','-S'],path)
    print(json.dumps({'status':'PASS_INDEPENDENT_EXACT_943_ORDER_AND_NEGATIVE_CONTROLS','rows':len(parsed),'json_sha256':sha(DATA),'source_sha256':sha(SOURCE),'maxima':[max(r[i] for r in parsed) for i in range(4)],'controls':results,'scope':'External parser and checker controls; no internal JSON semantics, K binding or machine simulation.'},indent=2))
if __name__=='__main__':main()
