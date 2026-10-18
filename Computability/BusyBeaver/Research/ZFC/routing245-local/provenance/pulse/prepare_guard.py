"""Source-only adaptation of the existing checked pulse guard; never invokes it."""
import ast,difflib,hashlib,json,pathlib,re
B=pathlib.Path('/tmp/zfc-routing245-lean/pulse')
R=pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs')
oldp=pathlib.Path('/tmp/zfc-prefix246-lean/pulse/check.py')
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
old=oldp.read_text();s=old
s=s.replace('Bounded exact246 pulse proof','Bounded exact245 pulse proof')
s=s.replace('Prefix246Pulse','Routing245Pulse').replace('TablePrefix246','TableRouting245')
s=s.replace('8bf5e5d5d89909c7be458d6cf349d145941365eaae2f5cfd36bbb743988edcbd','57465a4b514feca33a1b1148a3bf51ae92462f97a6f965ad0e1b8dcb53ab2685')
s=s.replace('391a483d4d4cee0f733ee9c5c1c65c5b4b7b811408ec16b1f4c19b960807a45a','16e971615215c89d9810479d08e5ab8219b7754211eab05b64112d0bed39fdd0')
s=s.replace('70a9a9bfb1546a1c0c6f1503c6261d2d23637dd901e7debec220e7185137ed6d','bb53b70f1a775b915d9b335a4ce1378c8350f771aca6aa007c0227989fd87281')
s=s.replace('92c2bddc7390806e81b30daa15c2bcfe082dcae6555392a57fe6d1ae987df81b','a51632e7a25ba048d8a988a07546637a8937649aec48303d167886f6b16b69e1')
s=s.replace('MP_RECORD_SHA','PULSE_RECORD_SHA');s=re.sub(r'\bMP\b','PULSE',s);s=re.sub(r'\bmp\b','pulse',s)
s=s.replace('arithmetic-control-mp254-verification.json','prefix246-pulse-verification.json')
s=s.replace('/tmp/zfc-prefix246-lean/pulse/','/tmp/zfc-routing245-lean/pulse/')
needle="    assert [q['label'] for q in d['commands']] == ['source', 'audit']\n"
s=s.replace(needle,needle+"    assert d['before'] == d['after']\n    assert d['source_object_recorded_before_audit']\n")
needle="    assert q['object_sha256'] == object_sha == sha(obj)\n"
s=s.replace(needle,needle+"    historical = next(x for x in pulse['actual_first_providers'] if x['module'] == m)\n    assert historical['sha256'] == object_sha\n    assert Path(historical['actual_first']).resolve() == obj\n")
s=s.replace("table_source = Path(parent['source']['path']).resolve()", "table_original = Path(parent['source']['path']).resolve()\ntable_source = R / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TableRouting245.lean'")
s=s.replace("== sha(table_source) == sha(table_snapshot)","== sha(table_source) == sha(table_original) == sha(table_snapshot)")
needle="assert sha(table_object) == q['sha256']\n"
s=s.replace(needle,needle+"assert parent['source_pass_object']['sha256'] == q['sha256']\nassert parent['source_pass_object']['source_sha256'] == q['source_sha256']\nassert parent['fresh_first_provider_before_audit']['sha256'] == q['sha256']\nassert Path(parent['fresh_first_provider_before_audit']['actual_first']).resolve() == table_object\n")
needle="tools = []\n"
s=s.replace(needle,"assert tool_names == {'Init', 'Lean.Elab.Tactic.Omega'}\ntool_pins = {q['module']: q['object_sha256'] for q in pulse['toolchain_providers']}\n"+needle)
s=s.replace("    assert obj.resolve() == ref.resolve()\n", "    assert obj.resolve() == ref.resolve()\n    assert sha(obj) == tool_pins[m]\n")
s=s.replace('C, table_snapshot, ss, aa]','C, table_original, table_snapshot, ss, aa]')
# Existing proof process, audit policy, failure capture and timing bodies remain exact.
a=old[old.index('deadline = time.monotonic() + TIMEOUT'):]
b=s[s.index('deadline = time.monotonic() + TIMEOUT'):]
assert a==b
ast.parse(s)
p=B/'check.py';assert not p.exists();p.write_text(s)
diff=B/'guard-from246.diff';diff.write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile=str(oldp),tofile=str(p))))
meta=dict(status='SOURCE_ONLY_GUARD_NOT_EXECUTED',guard=desc(p),template=desc(oldp),delta=desc(diff),source=desc(B/'Routing245Pulse.lean'),audit=desc(B/'Audit.lean'),boundary=desc(B/'boundary.json'),emitter=desc(pathlib.Path(__file__)),source_and_audit_execution_body_unchanged=True,shared_seconds=120,flags=['-j1','-M4096'],default_limits=True,project_providers=4,tool_boundaries=['Init','Lean.Elab.Tactic.Omega'],named_probes=3,typed_callers=4,compiler_execution=False,guard_execution=False,prepare_only_execution=False,changes=['Names, source/audit/table pins and source/audit defaults','Three generic providers selected from exact successful246 pulse record','Current maintained table source bound to original source and snapshot, fresh object and pre-audit provider','Explicit Init/Omega parent hashes, parent before/after equality and selected historical first providers'])
(B/'guard-inventory.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta,indent=2))
