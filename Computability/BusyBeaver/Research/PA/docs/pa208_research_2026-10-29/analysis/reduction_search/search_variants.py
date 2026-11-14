import subprocess,json,time,pathlib,concurrent.futures
base=pathlib.Path('analysis/comparison/rotations');out=pathlib.Path('analysis/reduction_search/variants');out.mkdir(exist_ok=True)
variants=['A_18-100-0','A_142-143-1','A_156-162-1','A_52-154-0','A_162-203-1','A_207-7-1','A_132-222-0','A_129-146-0','A_135-221-0','directional/candidate10004']
def run(name):
 d=out/name.replace('/','_');d.mkdir(exist_ok=True);table=base/name/'machine.tm';start=time.monotonic()
 with (d/'window.txt').open('w') as f:subprocess.run(['analysis/reduction_search/window',str(table),str(d/'window.bin'),'7','0'],stdout=f,check=True)
 with (d/'folds.txt').open('w') as f:r=subprocess.run(['analysis/reduction_search/variant_folds',str(table),str(d/'window.bin'),'7'],stdout=f,stderr=subprocess.PIPE,text=True,check=True)
 result={'name':name,'table':str(table),'folds':(d/'folds.txt').read_text(),'stats':r.stderr,'seconds':time.monotonic()-start}
 print(json.dumps(result),flush=True);(d/'result.json').write_text(json.dumps(result,indent=2)+'\n');return result
with concurrent.futures.ThreadPoolExecutor(max_workers=3)as ex:results=list(ex.map(run,variants))
(out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
