#!/usr/bin/env python3
"""Bounded author-side check of model-halt chosen rank without high-mask premises."""
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'CompactAuxOrdinateOrder.lean'
HIGHFIELDS = Path('/tmp/compact44-halt-rank-high-fields-author-8_baa5d1')
ALLHIGH = Path('/tmp/compact44-marked-all-high-author-ha7bw2gm')
HORIGIN = Path('/tmp/compact44-high-origin-marked-author-l1tgqob0')
OBLOCK = Path('/tmp/compact44-origin-block-residue-author-wg6jbjjz')
HRES = Path('/tmp/compact44-high-origin-residue-author-6qeiervt')
HTRANSFER = Path('/tmp/compact44-high-origin-transfer-author-u1d8_36d')
PRED = Path('/tmp/compact44-origin-predecessor-author-vgyleo1l')
FIELDHIGH = Path('/tmp/compact44-word-field-high-author-l_81oipf')
VERT = Path('/tmp/compact44-word-field-parity-author-py6aj_wq')
HORIZ = Path('/tmp/compact44-word-horizontal-parity-author-hsahp7zf')
TARGETHIGH = Path('/tmp/compact44-marked-target-high-nocarry-author-mr6jeauz')
TARGET = Path('/tmp/compact44-marked-target-column-author-w1mjy32i')
TARGETNO = Path('/tmp/compact44-target-nocarry-author-epmjpn1i')
BAND = Path('/tmp/compact44-selected-band-author-f2_s7req')
ANCHORHIGH = Path('/tmp/compact44-word-anchor-high-author-urme90m2')
PHASE0 = Path('/tmp/compact44-word-phase-zero-high-author-legvynkf')
DIV = Path('/tmp/compact44-kernel-div-four-author-jmrhb58d')
PHASE = Path('/tmp/compact44-high-phase-reduction-author-85ogpei6')
MARKEDPADDING = Path('/tmp/compact44-marked-high-padding-author-636x0hcr')
PADDING = Path('/tmp/compact44-high-padding-size-author-kxldejpf')
MASS = Path('/tmp/compact44-lower-kernel-mass-author-woy20b32')
SHARP = Path('/tmp/compact44-cell-sharp-size-author-zbfuxr9m')
ANCHORPARITY = Path('/tmp/compact44-word-anchor-parity-author-p264j6r8')
MARKER = Path('/tmp/compact44-word-marker-parity-author-0jkobfv1')
CLEANSUPPORT = Path('/tmp/compact44-word-clean-support-author-kty_zftf')
ANCHOR = Path('/tmp/compact44-word-anchor-bits-author-6lx38c4m')
PHYS = Path('/tmp/compact44-marked-physical-column-author-dmhimtju')
SLOT = Path('/tmp/compact44-word-low-slot-author-0luotfco')
CYCFIELD = Path('/tmp/compact44-word-field-cyclic-author-4lql7riz')
FIELDS = Path('/tmp/compact44-word-field-digits-author-2vtqgrmz')
COLOR = Path('/tmp/compact44-word-color-bits-author-2au67ed1')
PARTIAL = Path('/tmp/compact44-partial-packing-transport-author-9gb59y0i')
ALIGNEDSTENCIL = Path('/tmp/compact44-aligned-stencil-zero-carry-author-9j4jpv1q')
STENCIL = Path('/tmp/compact44-stencil-zero-carry-author-s6ijw6sz')
BOOLEAN = Path('/tmp/compact44-boolean-zero-carry-author-jrn4bz76')
ALIGNED = Path('/tmp/compact44-aligned-temporal-boolean-author-run1e_rp')
TEMPORAL = Path('/tmp/compact44-temporal-carry-rebuild-author-dimbsqnu')
CARRY = Path('/tmp/compact44-carry-replay-author-rroam1dc')
WORDPULSE = Path('/tmp/compact44-word-pulse-equality-author-k0l4ae1o')
CELLPULSE = Path('/tmp/compact44-cell-pulse-equality-author-03j8tbcr')
THREE = Path('/tmp/compact44-halt-rank-three-fields-author-qfz_cpk2')
MARKED = Path('/tmp/compact44-marked-cell-sum-author-_x9v7ths')
BLOCKSIZE = Path('/tmp/compact44-kernel-block-size-author-6d0hzf9g')
LOW = Path('/tmp/compact44-kernel-low-product-author-xl6f_qx5')
SPLIT = Path('/tmp/compact44-kernel-split-author-3dcckdqi')
HALTRANK = Path('/tmp/compact44-halt-rank-static-fields-author-cwqnhkb3')
POSITIVE = Path('/tmp/compact44-word-block-positivity-author-cj9zbngh')
RANKSTATIC = Path('/tmp/compact44-word-rank-static-fields-author-q48u_ean')
HALTWORD = Path('/tmp/compact44-halt-packed-word-author-6np41oc1')
WORDPROPS = Path('/tmp/compact44-word-properties-author-23je1u05')
WORD = Path('/tmp/compact44-constructed-word-author-x8sm5tgf')
HALTPROVIDER = Path('/tmp/ipra-halt-dimensions-explore-02/lib')
WORDRANK = Path('/tmp/compact44-word-rank-overlay-o4nua886')
RANK4 = Path('/tmp/compact44-word-rank-four-fields-author-t11w65n0')
STATIC = Path('/tmp/ipra-compact44-static-mask-mixed02/lib')
RANK = Path('/tmp/compact44-word-chosen-rank-author-v12mumpj')
PRODUCT = Path('/tmp/compact44-cell-product-bound-author-6eq960r0')
SIZE = Path('/tmp/compact44-cell-size-bound-author-d72l3hkb')
TOP = Path('/tmp/compact44-k-top-digit-explore/lib')
BYTE = Path('/tmp/ipra-byte-k-specialization-01/lib')
SPARSE = Path('/tmp/ipra-sparse-k-family-01/lib')
RADIX = Path('/tmp/compact44-k-radix-cert-01/lib')
PACKFIELDS = Path('/tmp/compact44-word-packing-fields-author-rmla494o')
LOWFIELDS = Path('/tmp/compact44-word-low-fields-author-73efsca_')
ORIGIN = Path('/tmp/compact44-origin-low-nocarry-author-7ki8y7e9')
PULSE = Path('/tmp/compact44-pulse-packed-cell-author-j8srdneh')
PULSEBIT = Path('/tmp/compact44-pulse-bit-author-kcf5puza')
UNIFORMPACK = Path('/tmp/compact44-uniform-packed-cell-author-576k0hda')
BLOCKS = Path('/tmp/compact44-uniform-blocks-author-x9_2dexw')
UNIFORM = Path('/tmp/compact44-cell-digit-uniform-author-x99hircy')
BASE = Path('/tmp/compact44-base-low-nocarry-author-18mja7xw')
DIGITSUPPORT = Path('/tmp/compact44-cell-digit-supported-author-qrjh3x0o')
PACKED = Path('/tmp/compact44-packed-cell-author-6k4g0ptt')
SUPPORT = Path('/tmp/compact44-cell-support-author-owsc91mv')
DEF = Path('/tmp/compact44-cell-digit-def-author-zrvgi8n3')
DIGIT = Path('/tmp/compact44-cell-digit-author-5ocsnwk4')
COPY = Path('/tmp/compact44-cell-copy-author-xh37hl8r')
WORD_PROVIDER = Path('/tmp/ipra-compact-word-cell-author-01/lib')
PACKING_PROVIDER = Path('/tmp/ipra-compact44-symbolic-unit-join/lib')
PROVIDER = Path('/tmp/compact44-halt-rank-overlay-vp7w2rjg')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OBS = HERE / 'observations/attempt04'
TRANSPORT = Path('/tmp/compact44-calibrated-transport-author-zh3yxtuc')
STRIDE = Path('/tmp/compact44-generic-stride-author-kzeu_onl')
POSITIVE_TRANSPORT = Path('/tmp/compact44-positive-transport-author-0wa9eqmk')
HALTPELL = Path('/tmp/compact44-halt-pell-seed-author-ahv6x7h4')
PELL = Path('/tmp/compact44-outer-pell-seed-author-ovtcp61y')
NOHIGH = Path('/tmp/compact44-halt-rank-no-high-author-swbhlgir')
RANKJOIN = Path('/tmp/compact44-rank-residue-join-author-6k2xhews')
REBUILD = Path('/tmp/compact44-outer-pell-rebuild-author-67cozz9f')
RANKAUTHOR = Path('/tmp/compact44-constructed-rank-author-g2doc30c')
RESIDUE = Path('/tmp/compact44-packing-origin-mod-four-author-b3v6f92j')
LOW4 = Path('/tmp/compact44-low-mod-four-author-o28oleni')
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    if not path.is_file():
        raise RuntimeError(f'dangling dependency: {path}')
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}


if OBS.exists():
    raise RuntimeError('refusing to overwrite prior attempt')
if shutil.disk_usage('/tmp').free < 4 * 1024**3:
    raise RuntimeError('less than 4 GiB free')
OBS.mkdir(parents=True)
word_dir = WORD_PROVIDER / 'DiophantineConsistency'
packing_dir = PACKING_PROVIDER / 'DiophantineConsistency'
overlay_dir = PROVIDER / 'DiophantineConsistency'
overlap = sorted(p.relative_to(WORD_PROVIDER).as_posix() for p in WORD_PROVIDER.rglob('*')
                 if p.is_file() and (PACKING_PROVIDER / p.relative_to(WORD_PROVIDER)).is_file())
overlap_records = {name: {'word_sha256': digest(WORD_PROVIDER / name),
                          'packing_sha256': digest(PACKING_PROVIDER / name)} for name in overlap}
if any(v['word_sha256'] != v['packing_sha256'] for v in overlap_records.values()):
    raise RuntimeError('word and packing provider overlap conflict')
expected = {p.name for p in word_dir.iterdir() if p.is_file()} | \
           {p.name for p in packing_dir.iterdir() if p.is_file()} | \
           {p.name for p in (HALTPROVIDER / 'DiophantineConsistency').iterdir() if p.is_file()}
actual = {p.name for p in overlay_dir.iterdir()}
if actual != expected:
    raise RuntimeError('overlay filenames do not match selected inputs')
radix_dir = RADIX / 'DiophantineConsistency'
radix_overlap = sorted(p.name for p in radix_dir.iterdir() if p.is_file() and (overlay_dir / p.name).is_file())
radix_records = {name: {'radix_sha256': digest(radix_dir / name), 'overlay_sha256': digest(overlay_dir / name)} for name in radix_overlap}
if any(v['radix_sha256'] != v['overlay_sha256'] for v in radix_records.values()):
    raise RuntimeError('radix and selected overlay overlap conflict')
if any(p.is_file() and not (overlay_dir / p.name).is_file() for p in radix_dir.iterdir()):
    raise RuntimeError('radix project module absent from selected overlay')
halt_dir = HALTPROVIDER / 'DiophantineConsistency'
wordrank_dir = WORDRANK / 'DiophantineConsistency'
halt_overlap = sorted(p.name for p in halt_dir.iterdir() if p.is_file() and (wordrank_dir / p.name).is_file())
halt_records = {name: {'halt_sha256': digest(halt_dir / name), 'wordrank_sha256': digest(wordrank_dir / name)} for name in halt_overlap}
if any(v['halt_sha256'] != v['wordrank_sha256'] for v in halt_records.values()):
    raise RuntimeError('halt and word-rank project overlap conflict')
halt_shared = {}
for sub in ('BusyBeaver', 'FirstOrder'):
    left, right = WORD_PROVIDER / sub, HALTPROVIDER / sub
    for p in left.rglob('*'):
        if p.is_file() and (right / p.relative_to(left)).is_file():
            name = sub + '/' + p.relative_to(left).as_posix()
            halt_shared[name] = {'word_sha256': digest(p), 'halt_sha256': digest(right / p.relative_to(left))}
if any(v['word_sha256'] != v['halt_sha256'] for v in halt_shared.values()):
    raise RuntimeError('halt and word shared-root overlap conflict')
static_dir = STATIC / 'DiophantineConsistency'
static_overlap = sorted(p.name for p in static_dir.iterdir() if p.is_file() and (overlay_dir / p.name).is_file())
static_records = {name: {'static_sha256': digest(static_dir / name), 'overlay_sha256': digest(overlay_dir / name)} for name in static_overlap}
if any(v['static_sha256'] != v['overlay_sha256'] for v in static_records.values()):
    raise RuntimeError('static and selected overlay overlap conflict')
if any(p.is_file() and not (overlay_dir / p.name).is_file() for p in static_dir.iterdir()):
    raise RuntimeError('static project module absent from selected overlay')
static_root_overlap = sorted(p.name for p in STATIC.iterdir() if p.is_file() and (PACKING_PROVIDER / p.name).is_file())
static_root_records = {name: {'static_sha256': digest(STATIC / name), 'packing_sha256': digest(PACKING_PROVIDER / name)} for name in static_root_overlap}
if any(v['static_sha256'] != v['packing_sha256'] for v in static_root_records.values()):
    raise RuntimeError('static and packing root overlap conflict')
overlay_before = {str(p): record(p) for p in overlay_dir.iterdir()}
static_before = {str(p): record(p) for p in STATIC.iterdir() if p.is_file()}
extra_before = {str(p): record(p) for root in (TOP, BYTE, SPARSE) for p in root.iterdir() if p.is_file()}
root_before = {str(p): record(p) for p in PACKING_PROVIDER.iterdir() if p.is_file()}
(OBS / 'overlay-preflight.json').write_text(json.dumps({
    'overlap_count': len(overlap), 'overlap': overlap_records,
    'radix_overlap_count': len(radix_overlap), 'radix_overlap': radix_records,
    'static_overlap_count': len(static_overlap), 'static_overlap': static_records,
    'halt_overlap_count': len(halt_overlap), 'halt_overlap': halt_records,
    'halt_shared_count': len(halt_shared), 'halt_shared': halt_shared,
    'static_root_overlap_count': len(static_root_overlap), 'static_root_overlap': static_root_records,
    'static_root_count': len(static_before), 'static_root_before': static_before,
    'extra_roots_count': len(extra_before), 'extra_roots_before': extra_before,
    'overlay_count': len(overlay_before), 'overlay_before': overlay_before,
    'packing_root_count': len(root_before), 'packing_root_before': root_before,
}, indent=2, sort_keys=True) + '\n')
new_project = REBUILD / 'DiophantineConsistency'
new_overlap = sorted(p.name for p in new_project.iterdir() if p.is_file() and (overlay_dir / p.name).is_file())
new_comparison = {name: {'seed_sha256': digest(new_project / name), 'halt_sha256': digest(overlay_dir / name)} for name in new_overlap}
if any(v['seed_sha256'] != v['halt_sha256'] for v in new_comparison.values()):
    raise RuntimeError('seed/halt project overlap conflict')
new_before = {str(p): record(p) for p in new_project.iterdir()}
(OBS / 'seed-halt-overlap.json').write_text(json.dumps({'overlap': new_comparison, 'count': len(new_overlap), 'seed_project': new_before}, indent=2, sort_keys=True) + '\n')
run = Path(tempfile.mkdtemp(prefix='compact44-aux-ordinate-order-author-'))
source = run / SOURCE.name
shutil.copyfile(SOURCE, source)
source_hash = digest(source)
shutil.copyfile(source, OBS / 'client-source.lean')
env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': f'{TRANSPORT}:{STRIDE}:{POSITIVE_TRANSPORT}:{HALTPELL}:{PELL}:{NOHIGH}:{RANKJOIN}:{REBUILD}:{RANKAUTHOR}:{RESIDUE}:{LOW4}:{HIGHFIELDS}:{ALLHIGH}:{HORIGIN}:{OBLOCK}:{HRES}:{HTRANSFER}:{PRED}:{FIELDHIGH}:{VERT}:{HORIZ}:{TARGETHIGH}:{TARGET}:{TARGETNO}:{BAND}:{ANCHORHIGH}:{PHASE0}:{DIV}:{PHASE}:{MARKEDPADDING}:{PADDING}:{MASS}:{SHARP}:{ANCHORPARITY}:{MARKER}:{CLEANSUPPORT}:{ANCHOR}:{PHYS}:{SLOT}:{CYCFIELD}:{FIELDS}:{COLOR}:{PARTIAL}:{ALIGNEDSTENCIL}:{STENCIL}:{BOOLEAN}:{ALIGNED}:{TEMPORAL}:{CARRY}:{WORDPULSE}:{CELLPULSE}:{THREE}:{MARKED}:{BLOCKSIZE}:{LOW}:{SPLIT}:{HALTRANK}:{POSITIVE}:{RANKSTATIC}:{HALTWORD}:{WORDPROPS}:{WORD}:{RANK4}:{RANK}:{PRODUCT}:{SIZE}:{TOP}:{BYTE}:{SPARSE}:{PACKFIELDS}:{LOWFIELDS}:{ORIGIN}:{PULSE}:{PULSEBIT}:{UNIFORMPACK}:{BLOCKS}:{UNIFORM}:{BASE}:{DIGITSUPPORT}:{PACKED}:{SUPPORT}:{DEF}:{DIGIT}:{COPY}:{PROVIDER}:{WORD_PROVIDER}:{PACKING_PROVIDER}:{STATIC}:{HALTPROVIDER}:{PACKAGE}', 'LEAN_NUM_THREADS': '1'}
deps = subprocess.run([str(LEAN), '--deps', str(source)], env=env,
                      capture_output=True, text=True, timeout=120)
(OBS / 'deps').write_text(deps.stdout)
(OBS / 'deps.stderr').write_text(deps.stderr)
if deps.returncode != 0 or deps.stderr:
    raise RuntimeError('dependency scan failed')
guards = {}
for line in deps.stdout.splitlines():
    path = Path(line)
    if not path.is_absolute() or not path.is_file() or path.suffix != '.olean':
        raise RuntimeError(f'bad dependency: {line}')
    stem = str(path)[:-len('.olean')]
    for suffix in SUFFIXES:
        guards[stem + suffix] = record(stem + suffix)
command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={run}',
           str(source), '-o', str(run / 'CompactAuxOrdinateOrder.olean')]
start = time.monotonic()
try:
    proc = subprocess.run(command, env=env, capture_output=True, text=True, timeout=180)
    code, output = proc.returncode, proc.stdout + proc.stderr
except subprocess.TimeoutExpired as exc:
    code, output = None, str(exc.stdout or '') + str(exc.stderr or '')
(OBS / 'compile.log').write_text(output)
after = {path: record(path) for path in guards}
overlay_after = {str(p): record(p) for p in overlay_dir.iterdir()}
root_after = {str(p): record(p) for p in PACKING_PROVIDER.iterdir() if p.is_file()}
extra_after = {str(p): record(p) for root in (TOP, BYTE, SPARSE) for p in root.iterdir() if p.is_file()}
static_after = {str(p): record(p) for p in STATIC.iterdir() if p.is_file()}
object_path = run / 'CompactAuxOrdinateOrder.olean'
result = {'command': command, 'run': str(run), 'exit_code': code,
          'duration_seconds': round(time.monotonic() - start, 3),
          'source_sha256': source_hash, 'workspace_source_sha256_after': digest(SOURCE),
          'log_sha256': digest(OBS / 'compile.log'), 'guards_before': guards,
          'guards_unchanged': guards == after,
          'overlay_unchanged': overlay_before == overlay_after,
          'seed_project_unchanged': new_before == {str(p): record(p) for p in new_project.iterdir()},
          'packing_root_unchanged': root_before == root_after,
          'extra_roots_unchanged': extra_before == extra_after,
          'static_root_unchanged': static_before == static_after,
          'object_sha256': digest(object_path) if object_path.is_file() else None,
          'scope': 'Single-author exploratory compile; inherited provider ancestry.'}
(OBS / 'terminal.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({key: result[key] for key in ('run', 'exit_code', 'duration_seconds',
                                                'guards_unchanged', 'object_sha256')}, sort_keys=True))
if code != 0 or not object_path.is_file() or guards != after or overlay_before != overlay_after or new_before != {str(p): record(p) for p in new_project.iterdir()} or root_before != root_after or extra_before != extra_after or static_before != static_after or digest(SOURCE) != source_hash or \
        any(word in output for word in ('error:', 'warning:', 'sorryAx')):
    raise SystemExit(1)
