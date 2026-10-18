"""Emit the scoped distance-64 frame port; source/metadata only, no proof calls."""
import difflib, hashlib, json, pathlib, re
R = pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs')
B = pathlib.Path('/tmp/zfc-routing245-lean/frame')
L = R / 'Computability/BusyBeaver/Lean'
Q = R / 'Computability/BusyBeaver/Research/ZFC'
sha = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
desc = lambda p: dict(path=str(p), sha256=sha(p), bytes=pathlib.Path(p).stat().st_size)
sp0 = L / 'BusyBeaver/ZFC/Prefix246Simulation.lean'
ap0 = Q / 'prefix246_frame_audit.lean'
assert sha(sp0) == '249c6c95d6550a8078f1b3462439fe7e7c4804a748e549b6b3aaf8aab6c2786a'
assert sha(ap0) == '095f8ec9495882fe2a27bc95859a280735b2ebea06cfc0e575a982d43c01e24c'
s0, a0 = sp0.read_text(), ap0.read_text()
def rename(t):
    for a,b in [('Prefix246Simulation','Routing245Simulation'), ('SitePrefix246','SiteRouting245'), ('SymbolicPrefix246','SymbolicRouting245'), ('DispatchFrame','DispatchFrame64')]:
        t = t.replace(a,b)
    t = re.sub(r'\b246\b', '245', t)
    return re.sub(r'\b40\b', '64', t)
s, a = rename(s0), rename(a0)
doc = '''/-!
Whole-tape frame adapters for the literal routing245 machine.

Port of the checked Prefix246Simulation contracts, with a scoped header
budget of 64 cells for the new decoder. The physical-register permutation
and generic dispatch zipper remain unchanged. The historical distance-40
DispatchFrame predicate is retained in its original module; this module
introduces DispatchFrame64 and uses it throughout its new frame contracts.

The framework derives from Mira-Cult and Jeff's original machine verification
and Wade's path semantics at upstream 297ab8df7e5de329605c3875b4934643b371a5e3.
The symbolic file has no artificial final false cell. Increment appends a
value-one spare; positive decrement preserves the suffix and contributes
one extra cell to the header distance. Branch validity explicitly requires
a nonempty spare suffix, ensuring at least ten physical blocks.

The adapters quantify over arbitrary register values, gaps and spare values,
and retain the entire infinite tape. Their symbolic execution premises are
explicit. Actual site coverage, the blank bootstrap and the PA comparison
remain separate obligations.
-/'''
s = re.sub(r'/\-![\s\S]*?\-/', lambda _: doc, s, count=1)
frame = '''/-- The routing decoder's whole-tape dispatch frame. Its margin is 64,
while padding, all register values and the complete spare suffix remain free. -/
def DispatchFrame64 {states : Nat} (dispatch : Fin states) (binary : Config states)
    (logical : Configuration) (gap : Nat) (spares : List Nat) : Prop :=
  64 ≤ logical.path.length + gap ∧ LogicalTailZero logical.registers ∧
    ∃ leftPadding rightPadding : Nat,
      ZipRep binary (dispatchZip dispatch binary.head leftPadding rightPadding logical gap spares)

'''
anchor = 'open RegisterPath FiniteZipper Permutation252Frame SymbolicRouting245\n\n'
assert s.count(anchor) == 1
s = s.replace(anchor, anchor + frame)
# The only new caller makes the scoped frame's exact generic layout explicit.
a += '''
example {states : Nat} (dispatch : Fin states) (binary : Config states)
    (logical : Configuration) (gap : Nat) (spares : List Nat) :
    DispatchFrame64 dispatch binary logical gap spares ↔
      64 ≤ logical.path.length + gap ∧ LogicalTailZero logical.registers ∧
        ∃ leftPadding rightPadding : Nat,
          ZipRep binary
            (dispatchZip dispatch binary.head leftPadding rightPadding logical gap spares) :=
  Iff.rfl
'''
strip = lambda t: re.sub(r'/\-[\s\S]*?\-/', '', re.sub(r'--[^\n]*', '', t))
assert strip(s.replace(frame,'')) == strip(rename(s0))
assert strip(a[:a.index('\nexample {states : Nat}')]) == strip(rename(a0))
assert len(re.findall(r'\b40\b', strip(s))) == 0
assert len(re.findall(r'\bDispatchFrame\b', strip(s))) == 0
assert a.count('#print axioms ') == 14 and a.count('\nexample ') == 15
assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)', strip(s))
sp, ap = B/'Routing245Simulation.lean', B/'Audit.lean'
assert not sp.exists() and not ap.exists()
sp.write_text(s); ap.write_text(a)
for name, old, new, src, dst in [('source',s0,s,sp0,sp), ('audit',a0,a,ap0,ap)]:
    (B/f'{name}-from246.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=str(src),tofile=str(dst))))
site_inventory = pathlib.Path('/tmp/zfc-routing245-lean/site/boundary-plan.json')
bd = json.loads(site_inventory.read_text())
providers = bd['providers'].copy()
# This is a prospective source inventory. New units' actual successful objects
# will be selected by a later guard; none are guessed from their existence.
new_sources = {
    'BusyBeaver.ZFC.Routing245Pulse': '/tmp/zfc-routing245-lean/pulse/Routing245Pulse.lean',
    'BusyBeaver.ZFC.Routing245Boxes': '/tmp/zfc-routing245-lean/boxes/source-v2/Routing245Boxes.lean',
    'BusyBeaver.ZFC.RegisterMarkRouting245': '/tmp/zfc-routing245-lean/mark/RegisterMarkRouting245.lean',
    'BusyBeaver.ZFC.SymbolicRouting245': '/tmp/zfc-routing245-lean/symbolic/SymbolicRouting245.lean',
    'BusyBeaver.ZFC.SiteRouting245': '/tmp/zfc-routing245-lean/site/SiteRouting245.lean',
}
for module, path in new_sources.items():
    providers = [x for x in providers if x['module'] != module]
    providers.append(dict(module=module, source=path, source_sha256=sha(path), object=None,
                          object_sha256=None, evidence=None, status='OBJECT_NOT_SELECTED_IN_SOURCE_PLAN'))
old_record = Q/'results/prefix246-frame-verification.json'
d = json.loads(old_record.read_text()); assert d['status']=='PASS'
for name in ['BusyBeaver.ZFC.RMDag', 'BusyBeaver.ZFC.RMEquiv', 'BusyBeaver.ZFC.RegisterPathClean']:
    x = next(x for x in d['reused_modules'] if x['module']==name)
    source = L/pathlib.Path(name.replace('.','/')).with_suffix('.lean')
    assert sha(source)==x['source_sha256'] and sha(x['object'])==x['object_sha256']
    p = next(x for x in d['actual_first_providers'] if x['module']==name)
    assert p['sha256']==x['object_sha256'] and pathlib.Path(p['actual_first']).resolve()==pathlib.Path(x['object']).resolve()
    providers.append(dict(x,source=str(source),selected_parent_record=desc(old_record)))
for x in providers:
    assert sha(x['source'])==x['source_sha256']
    if x['object'] is not None: assert sha(x['object'])==x['object_sha256']
seen=set(); external={'Init'}
def visit(name):
    if not name.startswith('BusyBeaver.'):
        external.add(name); return
    if name in seen: return
    seen.add(name)
    x=next(x for x in providers if x['module']==name)
    for dep in re.findall(r'^import ([A-Za-z0-9_.]+)$', pathlib.Path(x['source']).read_text(), re.M): visit(dep)
direct = re.findall(r'^import ([A-Za-z0-9_.]+)$', s, re.M)
for name in direct: visit(name)
assert len(seen)==21 and seen=={x['module'] for x in providers}
assert sum(x['object'] is not None for x in providers)==16
boundary=dict(status='SOURCE_ONLY_PROSPECTIVE_PROVIDER_PLAN',source=desc(sp),audit=desc(ap),direct_imports=direct,
              expected_project_module_count=21,current_bound_provider_count=16,providers=providers,
              external_boundaries=sorted(external),toolchain_providers=d['toolchain_providers'],compiler=d['compiler'],
              named_probes=14,typed_callers=15,compiler_execution=False,guard_execution=False,
              unselected_new_provider_policy='Null object fields mean not yet selected for this source plan; they do not assert no actual PASS exists elsewhere.')
(B/'boundary-plan.json').write_text(json.dumps(boundary,indent=2)+'\n')
inv=dict(status='SOURCE_ONLY_NOT_COMPILED',source=desc(sp),audit=desc(ap),boundary=desc(B/'boundary-plan.json'),emitter=desc(pathlib.Path(__file__)),
         template_source=desc(sp0),template_audit=desc(ap0),template_record=desc(old_record),
         semantic_changes=['Scoped generic DispatchFrame64 predicate with the same whole-tape zipper layout','Every source/target margin, consumed-path parameter and output gap changes coherently from40 to64','Actual245 executor/site names and state types'],
         normalized_proof_bodies_equal=True,positive_decrement_extra_unchanged=True,increment_appends_one_spare=True,
         decrement_retains_all_spares=True,nonempty_spares_only_in_validity=True,arbitrary_registers_gaps_spares_whole_tape=True,
         named_probes=14,typed_callers=15,expected_projects=21,current_bound_projects=16,
         unselected_modules=list(new_sources),default_proof_limits=True,compiler_execution=False,guard_execution=False)
(B/'source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
print(json.dumps({k:inv[k] for k in ['status','source','audit','boundary','named_probes','typed_callers','expected_projects','current_bound_projects']},indent=2))
