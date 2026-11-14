from search_folds import *
import multiprocessing,sys,contextlib,io
folder=BASE/'sources/incoming208/layout_catalog'

def test(path):
 rows=read_table(path)
 if '--mp-h' in sys.argv:rows[115,1]=(1,1,108)
 reach=reachable(rows,4)
 log=io.StringIO()
 with contextlib.redirect_stdout(log):found=search(rows,reach,4)
 return str(path),found,log.getvalue()

if __name__=='__main__':
 paths=sorted(folder.glob('196_*.tm'))
 paths=[p for p in paths if json.loads(p.with_suffix('.json').read_text()).get('source_metrics',{}).get('max_consecutive_zeros',99)<=6]
 start=time.time()
 print('CATALOG',len(paths),flush=True)
 done=[]
 with multiprocessing.Pool(4) as pool:
  for i,(path,hits,log) in enumerate(pool.imap_unordered(test,paths),1):
   done.append({'path':path,'hits':hits})
   print('CHECKED',i,Path(path).name,'hits',len(hits),'seconds',time.time()-start,flush=True)
   if hits:
    print('SUCCESS',log,flush=True)
    (BASE/('research/catalog_success_mph.json' if '--mp-h' in sys.argv else 'research/catalog_success.json')).write_text(json.dumps({'path':path,'hits':hits},indent=2))
    pool.terminate();break
 (BASE/('research/catalog_results_mph.json' if '--mp-h' in sys.argv else 'research/catalog_results.json')).write_text(json.dumps(done,indent=2))
 print('DONE',len(done),time.time()-start,flush=True)
