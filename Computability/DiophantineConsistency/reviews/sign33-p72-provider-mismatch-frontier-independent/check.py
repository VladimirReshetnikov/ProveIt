import hashlib,json,os,subprocess,sys,tarfile
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];q=D/'research/sign33-p72-provider-mismatch';base=Path('/tmp/p72-current-base-extension-attempt02-20261105');arc=D/'research/p72-current-base-extension-build-attempt02/terminal/stage-evidence.tar.gz'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(q/'check.py')=='65699f5fe006953810b763f0d35e47e9bea02faa2e82d33e92895838b2af3462' and sha(q/'result.json')=='811dcad57d828cff5307aaafc9769dd7e017771e70ecee4278f0e762112729b9'
x=subprocess.check_output([sys.executable,'-I','-S','-B',str(q/'check.py')],timeout=120);assert hashlib.sha256(x).hexdigest()==sha(q/'result.json');o=json.loads(x);assert o['status']=='PASS_OVERLAY_COMPARISON' and o['direct_guard_slots_checked']==300 and o['overlap_count']==1007
assert sha(arc)=='884525ff2103d805cdb8b891fedaa9cf8b9be4bc5f1c67efbf8e95353b533541'
with tarfile.open(arc,'r:gz') as tar:
 for n in ('0618','0619','0620'):
  b=tar.extractfile('rows/'+n+'.json').read();assert hashlib.sha256(b).hexdigest()==sha(base/'rows'/f'{n}.json')
survey=json.loads((D/'research/nine-sharing-sign33-inner-v-ring-check/attempt01/survey-before.json').read_text());count=0;dif=[]
for rel,rec in survey['links'].items():
 v=base/'lib'/rel
 if not v.is_file():continue
 z=Path(rec['realpath']);assert z.is_file() and sha(z)==rec['sha256'];h=sha(v);count+=1
 if h!=rec['sha256']:dif.append((rel,rec['sha256'],h))
assert count==1007 and dif==[('DiophantineConsistency/ModelDifferenceRing.olean','cf2b32cb1e4777b7cff73c34ed7334a105f705912fa987e9f7f9a316fef192f0','e52ed546fa3f94d9c3b823ad19286c4c906359efa26c1d67543e9dbfc0f2ecf0')]
key='DiophantineConsistency/ArithmeticPellHalfIndex.olean';assert sha(base/'lib'/key)==survey['links'][key]['sha256']=='6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7'
print(json.dumps({'status':'PASS_POINT_IN_TIME_OVERLAY_COMPARISON','row_archive_matches':['0618','0619','0620'],'overlap_count':count,'mismatches':dif,'halfindex_matches':True,'scope':'Byte/hash comparison only; not a proof of semantic incompatibility, complete transitive load trace, or Lean replay.'},indent=2,sort_keys=True))
