import concurrent.futures,json,os,pathlib,subprocess,sys,time
root=pathlib.Path('.').resolve(); out=root/'analysis/comparison'
names=['U208_ConPA_2026-10-29','U208_ConPA_Conditional_Context_2026-10-29','U208_ConPA_Entry_Context_2026-10-29','U208_ConPA_History_2026-10-29','u208_research_2026-10-29']
def run(n):
 p=next(x for x in (root/'upstream'/n).iterdir() if x.is_dir())
 if n=='u208_research_2026-10-29': args=['verify.py','--output',str(out/(n+'.json'))]
 elif n=='U208_ConPA_Conditional_Context_2026-10-29': args=['reproduce.py','--quick','--report',str(out/(n+'.json'))]
 elif n=='U208_ConPA_History_2026-10-29': args=['reproduce.py','--quick','--output',str(out/n)]
 else:args=['reproduce.py','--quick','--output',str(out/(n+'.json'))]
 started=time.monotonic()
 proc=subprocess.run([sys.executable,'-B',*args],cwd=p,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True)
 (out/(n+'.log')).write_text(proc.stdout+proc.stderr)
 result={'package':n,'returncode':proc.returncode,'seconds':time.monotonic()-started}
 print(json.dumps(result),flush=True)
 return result
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex: results=list(ex.map(run,names))
(out/'quick_results.json').write_text(json.dumps(results,indent=2)+'\n')
