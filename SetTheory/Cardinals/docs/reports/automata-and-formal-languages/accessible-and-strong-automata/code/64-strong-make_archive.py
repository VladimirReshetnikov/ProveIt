"""Build a safe, deterministic reproducibility ZIP from an explicit allowlist."""
from pathlib import Path
import stat
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED
from verify_manifest import verify

ROOT = Path(__file__).resolve().parent
FILES = '''README.md SOURCES.md REPLAY.md requirements.txt build.sh replay.sh
strong-automata.pdf strong-automata.tex cyclic-lift-proof.tex
generate_coefficients.py coefficients_k2.json coefficients_k3.json coefficients_k4.json
verify_precision.py precision_validation.json
verify_exact_sectors.py exact_sector_validation.json
verify_inverses.py inverse_validation.json
verify_all_model_inverses.py all_model_inverse_validation.json
verify_cyclic_lifts.py cyclic_lift_validation.json
verify_replay.py verify_manifest.py make_archive.py
independent_checks/README.md independent_checks/derive_low_orders.py
independent_checks/check_small_models.py independent_checks/verify_exact_counts.py
independent_checks/low_orders.json independent_checks/small_models.json
independent_checks/exact_k2.json independent_checks/exact_k3.json independent_checks/exact_k4.json'''.split()

if __name__ == '__main__':
    assert set(verify()) == set(FILES), 'Manifest differs from the documented allowlist'
    output = ROOT.parent/'strong-automata-reproducibility.zip'
    prefix = 'strong-automata-report/'
    with ZipFile(output,'w',compression=ZIP_DEFLATED,compresslevel=9) as archive:
        for name in sorted(FILES+['MANIFEST.sha256']):
            p = ROOT/name
            assert p.is_file() and not p.is_symlink()
            info = ZipInfo(prefix+name,date_time=(2026,10,2,0,0,0))
            info.create_system = 3
            mode = 0o755 if name.endswith('.sh') else 0o644
            info.external_attr = (stat.S_IFREG | mode) << 16
            info.compress_type = ZIP_DEFLATED
            archive.writestr(info,p.read_bytes())
    with ZipFile(output) as archive:
        assert archive.testzip() is None
        assert len(archive.namelist()) == len(FILES)+1
        assert all(n.startswith(prefix) and '..' not in n.split('/') for n in archive.namelist())
    print(f'Created {output.name} with {len(FILES)+1} safe relative-path entries.')
