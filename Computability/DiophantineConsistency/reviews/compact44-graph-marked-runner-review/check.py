#!/usr/bin/env python3
"""Read-only review of the examined runner; isolated fake provider mutation only."""
import ast,hashlib,json,os,pathlib,re,sys,tempfile
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):
 raise RuntimeError('isolated, non-optimized Python required')
P=pathlib.Path;root=P.cwd();p=root/'Computability/DiophantineConsistency/reviews/compact44-graph-marked-runner-review'; ev=p/'evidence';H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest()
runner=ev/'runner.py.txt';survey=ev/'warning-survey.json'
assert H(runner)=='e864a94e10c8a9191e3bea062c011d08b28a0c4bd60266750d514ba620cb4337'
assert H(survey)=='6546baaf4f534dcd3f4d59605fda50edd2a73de7b5d8c58de7a81996ca47678c'
tree=ast.parse(runner.read_text());names={'need','H','record','slotstem','check','diagnostics_ok'}
nodes=[node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name in names];assert {x.name for x in nodes}==names
class RewriteSurvey(ast.NodeTransformer):
 def visit_Constant(self,node):
  if node.value=='/tmp/graph-marked-warning-survey-01.json':return ast.copy_location(ast.Constant(value=str(survey)),node)
  return node
nodes=[RewriteSurvey().visit(n) for n in nodes];m=ast.fix_missing_locations(ast.Module(body=nodes,type_ignores=[]))
ns={'Path':P,'os':os,'hashlib':hashlib,'json':json,'re':re,'ROOT':root,'SUF':('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')};exec(compile(m,str(runner),'exec'),ns)
with tempfile.TemporaryDirectory(prefix='graph-marked-guard-review-') as tmp:
 d=P(tmp);lib=d/'lib';pkg=d/'pkg';lib.mkdir();pkg.mkdir();(pkg/'Example.olean').write_bytes(b'package')
 providers=[lib/'Example.olean',pkg/'Example.olean'];chosen=next(x for x in providers if x.is_file());guards=ns['slotstem'](P(str(chosen)[:-6]));(lib/'Example.olean').write_bytes(b'shadow')
 ns['check'](guards);later=next(x for x in providers if x.is_file());assert chosen!=later and chosen==providers[1] and later==providers[0]
 guard={'original_provider':'package/Example.olean','later_provider':'lib/Example.olean','original_companion_guard_still_passes':True,'unrecorded_higher_priority_shadow_selected':True}
terminal=root/'Computability/DiophantineConsistency/reviews/ha87-full-source-build-author2/terminal-state.json';s=json.loads(survey.read_bytes());assert H(terminal)==s['history_terminal_sha256'];h=json.loads(terminal.read_bytes());hist={x['module']:x for x in h['records']};assert h['status']=='FAILED'
warnings={}
for name,log,count in [('BusyBeaver.ZFC.TarskiComplete','TarskiComplete-live.log',6),('BusyBeaver.ZFC.ArithmeticCantor','ArithmeticCantor-live.log',5)]:
 item=s['matched'][name];rec=hist[name];src=item['source_sha256'];live=(ev/log).read_text();old=root/item['historical_log']
 assert item['warning_count']==count and rec['exit']==0 and rec['verified'] is True and rec['source_sha256']==src and H(old)==rec['log_sha256']==item['historical_log_sha256']
 assert ns['diagnostics_ok'](name,live,src) and ns['diagnostics_ok'](name,'',src)
 assert not ns['diagnostics_ok'](name,live+'\nnew:1:1: warning: injected\n',src)
 warnings[name]={'count':count,'live_log_sha256':H(ev/log),'historical_log_sha256':H(old),'historical_record_exit':rec['exit'],'historical_record_verified':rec['verified'],'live_accepted':True,'all_warnings_absent_also_accepted':True,'added_warning_rejected':True}
assert len(s['matched'])==26 and len(s['unmatched'])==74
print(json.dumps({'status':'PASS_READ_ONLY_RUNNER_REVIEW_GUARD_GAP_CONFIRMED','runner_sha256':H(runner),'warning_survey_sha256':H(survey),'historical_build_status':h['status'],'survey_matched':len(s['matched']),'survey_unmatched':len(s['unmatched']),'provider_shadow_reproduction':guard,'warnings':warnings,'lean_launched':False,'live_tree_modified':False,'scope':'A controlled demonstration of a guard gap, not evidence of actual live-build compromise.'},indent=2,sort_keys=True))
