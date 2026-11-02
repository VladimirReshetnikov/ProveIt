#!/usr/bin/env python3
import contextlib,hashlib,importlib.util,io,json,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[5];D=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-model-noextra-prototype/contextual-replay.py';assert hashlib.sha256(D.read_bytes()).hexdigest()=='b3263df2ae511f207f5598507253d9e9b8ecc6d885266101efe74ab482832fe4'
for mode in ('good','wrong_report','missing_axiom','extra_axiom','warning','sorry','wrong_deps','compiler_exit','stop_reason','sibling_mismatch','parent_drift','forbidden_order','missing_first_required','frozen_symlink','late_source','late_output','late_log','late_symlink','head_drift'):
 sp=importlib.util.spec_from_file_location('driver',D);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.pins=lambda:None;calls=[];audits=[];heads=[]
 def fake_audit(view):
  audits.append(1)
  if len(audits)>1 and mode=='late_source':
   src=out/'src/DiophantineConsistency/CompactForbidden.lean';src.write_text(src.read_text()+'\n-- late drift')
  if len(audits)>1 and mode=='late_symlink':
   src=out/'src/DiophantineConsistency/CompactForbidden.lean';backing=src.parent/'late-backing.lean';backing.write_bytes(src.read_bytes());src.unlink();src.symlink_to(backing)
  if len(audits)>1 and mode=='late_output':(out/'author/lib/DiophantineConsistency/CompactNoExtra.olean').write_bytes(b'drift')
  if len(audits)>1 and mode=='late_log':(out/'author/CompactNoExtra.log').write_text('drift')
  return [{'status':'changed'}] if mode=='parent_drift' and len(audits)>1 else [{'status':'a'},{'status':'b'}]
 m.audit=fake_audit
 def overlay(src,dest):
  d=dest/'DiophantineConsistency';d.mkdir(parents=True)
  for x in ('Compact943Data','CompactRowComplete'):
   srcfile=src/'DiophantineConsistency'/f'{x}.olean';assert srcfile.is_file();(d/f'{x}.olean').symlink_to(srcfile)
 m.overlay=overlay;tmp=Path(tempfile.mkdtemp(prefix='noextra-fake-monitor-',dir='/tmp'));mon=tmp/'monitor.py';reports={k:[(n,sorted(v)) for n,v in vals] for k,vals in m.REPORTS.items()}
 mon.write_text("from pathlib import Path\ndef monitored(cmd,env,log,timeout=600):\n"+
  (" src=Path(cmd[-3]);backing=src.parent/'backing.lean';backing.write_bytes(src.read_bytes());src.unlink();src.symlink_to(backing)\n" if mode=='frozen_symlink' else '')+
  " obj=Path(cmd[-1]);name=obj.stem;obj.write_bytes("+("b'PEER_DIFFERENT' if 'peer' in str(obj) else b'OBJ'" if mode=='sibling_mismatch' else "b'OBJ'")+")\n reports="+repr(reports)+"[name]\n"+
  (" reports[0]=('wrong.name',reports[0][1])\n" if mode=='wrong_report' else '')+
  (" reports[-1]=(reports[-1][0],[])\n" if mode=='missing_axiom' else '')+
  (" reports[-1]=(reports[-1][0],reports[-1][1]+['extra'])\n" if mode=='extra_axiom' else '')+
  " text=''.join(\"'\"+n+\"' \"+(\"depends on axioms: [\"+', '.join(ax)+\"]\" if ax else \"does not depend on any axioms\")+\"\\n\" for n,ax in reports)\n"+
  (" text+='warning: injected\\n'\n" if mode=='warning' else '')+(" text+='sorryAx\\n'\n" if mode=='sorry' else '')+
  " log.write_text(text);return "+('1' if mode=='compiler_exit' else '0')+",123,"+("'injected stop'" if mode=='stop_reason' else 'None')+"\n")
 m.MONITOR=mon
 def fake_run(cmd,env=None,**kw):
  if cmd[:2]==['git','rev-parse']:
   heads.append(1);return subprocess.CompletedProcess(cmd,0,stdout=('changed\n' if mode=='head_drift' and len(heads)>1 else 'fake-head\n'),stderr='')
  assert '--deps' in cmd;src=Path(cmd[-1]);lib,pkg=map(Path,env['LEAN_PATH'].split(':'));calls.append(src.stem)
  deps=[str(pkg/'Init.olean')]+[str(lib/'DiophantineConsistency'/f'{x}.olean') for x in (['Compact943Data'] if src.stem=='CompactForbidden' else ['CompactRowComplete','CompactForbidden'])]
  if mode=='missing_first_required' and src.stem=='CompactForbidden':(lib/'DiophantineConsistency/Compact943Data.olean').unlink()
  if mode=='wrong_deps':deps.append('/tmp/unexpected.olean')
  if mode=='forbidden_order' and src.stem=='CompactNoExtra':(lib/'DiophantineConsistency/CompactForbidden.olean').unlink()
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
 m.subprocess=type('Fake',(),{'run':staticmethod(fake_run)})
 out=Path(tempfile.mkdtemp(prefix='ipra-compact-noextra-contextual-pair-review-',dir='/tmp'));out.rmdir();sys.argv=[str(D),'--output',str(out),'--historical-view','/tmp/ipra-historical-audit-review-01','--expected-head','fake-head']
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();err=None
   except Exception as e:err=str(e)
  if mode=='good':assert err is None and len(calls)==4 and len(json.loads((out/'receipt.json').read_bytes())['rows'])==4,(mode,err)
  else:
   expected='frozen source drift' if mode in ('frozen_symlink','late_source','late_symlink') else 'final object or log drift' if mode in ('late_output','late_log') else 'HEAD drift' if mode=='head_drift' else 'dependency mismatch' if mode=='wrong_deps' else 'axiom report mismatch' if mode in ('wrong_report','missing_axiom','extra_axiom') else 'paired outputs differ' if mode=='sibling_mismatch' else 'parent audit reruns differ' if mode=='parent_drift' else 'compiler failure' if mode in ('warning','sorry','compiler_exit','stop_reason') else None
   if mode in ('forbidden_order','missing_first_required'):assert err is not None and 'missing required object' in err,(mode,err)
   else:assert err and expected in err,(mode,err)
  print(mode,'PASS',len(calls),'fake deps')
 finally:shutil.rmtree(out,ignore_errors=True);shutil.rmtree(tmp,ignore_errors=True)
