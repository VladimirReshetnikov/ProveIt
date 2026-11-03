#!/usr/bin/env python3
"""Bounded, guarded author rebuild of the expanded selected-project cone."""
import fcntl
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
FIRST_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild'
FIRST_RUNNER_SHA = 'c268533ca55c6eeba33066d591f0b5eff5bd6dd52e107350d924420bfe2350e6'
SECOND_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch02'
SECOND_RUNNER_SHA = '49c6edd8afc3dbd377b112c270b782f299f827e78417a03717e033168b29215c'
THIRD_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch03'
THIRD_RUNNER_SHA = '429502951c2bc723dd68e71ca919df0209d69b1b6976cfe5d24ed6c31a87ab11'
FOURTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch04'
FOURTH_RUNNER_SHA = 'b4864212922631685841d278c30540c14cecf26d00cc1314ee35594d7cca1e87'
FIFTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch05'
FIFTH_RUNNER_SHA = 'b50b03308e14fc46ace9e33e89c3d0d57ddcad8cf70280fa0138b5b555d13e9e'
SIXTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch06'
SIXTH_RUNNER_SHA = '7c4799559684e61532af8909b899ab943a6f4bedded1e7e959b83929d05a9a55'
SEVENTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch07'
SEVENTH_RUNNER_SHA = '168325b02ae463e861f41aafee37ff0e532b98bbe25abb288d35d6de8bbd7636'
EIGHTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch08'
EIGHTH_RUNNER_SHA = '11cfdb9eeb11d97fc8e1b1345125e2a6e542d63eb7d2a640e051133035546a4d'
NINTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch09'
NINTH_RUNNER_SHA = '4048ea046785b8e5605ac1cb08d031b5b5c2ee618238d02b08f7c78f710b9a0d'
TENTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch10'
TENTH_RUNNER_SHA = 'a37cd629ddb5c4b3bfa648298c3ccec7ea365d6591c270714f72c5b59b0a7f01'
ELEVENTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch11'
ELEVENTH_RUNNER_SHA = '6542b81b75d5462262410f1547f78743e029cfc153432eeb3ce3b2d2c51e6df6'
TWELFTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch12'
TWELFTH_RUNNER_SHA = '015087abf9cebf5b323654d3484c1600fbb44d8f4b5829f51f01a681dd54e16d'
STAGE57_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage57'
STAGE57_RUNNER_SHA = 'bed7793b0ec0d16e11a9ff5a8f82dccba6a1a6593325d76ca941f737d6344646'
STAGE58_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage58'
STAGE58_RUNNER_SHA = 'bfba83662216ed841bff8a1cccb0ab8a05c4087bc304f76417e1e303c39f1063'
STAGE59_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage59'
STAGE59_RUNNER_SHA = '093a526f20ba8a5e0d2fc14cacf571f5f7887f22528bfd24f3f32ec9316ab427'
STAGE60_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch-stage60'
STAGE60_RUNNER_SHA = '29d4553136d6ea37822c075fb3770deed9de618825eef00df8d209b6ec6a0786'
STAGE61_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage61'
STAGE61_RUNNER_SHA = 'c21e2b9784b6a67db9f3b50b5dc2d748f85f77d24b205a1c698702e1153e6443'
STAGE62_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage62'
STAGE62_RUNNER_SHA = 'b933ab40fb473cd26a57c103ac02e3e0df3ff2e5ef3f6e3a94d5527a91d6bcc3'
STAGE63_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage63'
STAGE63_RUNNER_SHA = '7390142e3df6f076c75a65322494c012f4bacca470aa00b2c08966d99992aee3'
STAGE64_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage64-retry'
STAGE64_RUNNER_SHA = '2e58ed63b3947506bc7576fdeccd66d22b3c6f8ba611136a60f875b0db3abb80'
STAGE65_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage65'
STAGE65_RUNNER_SHA = '72ef5736a651e852ad4a077b4462a537326cad2e199ababd3076a29d48ab2833'
STAGE66_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage66'
STAGE66_RUNNER_SHA = 'b27a20fb98bfc91fa332f15734fc6f78abec91b68b03962924c64a23bcc00ad3'
STAGE67_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage67'
STAGE67_RUNNER_SHA = '0b246d22c6d26f1f267fffbea18edcb351e1b9dbe5641e7f9cef79698e8d0f47'
STAGE72_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage72'
STAGE72_RUNNER_SHA = '5abf137a74f932735f52d021458130eebb59c6b6d50102043b2bfa15f0a7d98e'
STAGE77_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage77'
STAGE77_RUNNER_SHA = 'aa1dda158d31d81669a6dd766b7a402b9fdd9d1803e2fb9596c1d9f0a6d2f4fa'
STAGE79_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage79-warning-retry'
STAGE79_RUNNER_SHA = 'f749308aa658453e4ace9bb35a7aed47a4eb822e17cf0077cb3e1c92a39a38d9'
STAGE80_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage80'
STAGE80_RUNNER_SHA = 'b0920ef9ee49036368ce79cd948f5136c9ec9808f64dde445068e28b593ff0d8'
STAGE81_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage81-warning-retry'
STAGE81_RUNNER_SHA = '47fcc5e077e12bfefe324f3a20c44792fcb9437dd1902b5853c65bb72e0ceb48'
STAGE82_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage82'
STAGE82_RUNNER_SHA = '971405d78d1a8869533e1adffcfb97ec2009edacef5c2364905bba8119521731'
STAGE84_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage84-warning-retry'
STAGE84_RUNNER_SHA = 'afe5cce022d23567a573b83570e08a4b6c64dac664b77f50bbd7f0cea9b18843'
STAGE85_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage85'
STAGE85_RUNNER_SHA = '83b33b77293779df6530ef69ded48b42912bd7adf4dea36c05a706cbcf89b8c6'
STAGE90_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage90'
STAGE90_RUNNER_SHA = 'cc48775715939835b0529338d1a5fb5348d7902bfb6f197dac430062df2f470b'
STAGE95_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage95'
STAGE95_FAILED_RUNNER_SHA = 'c3c11a6e5f29fa79bf70d6d1c05d1b914b5933c49b765f5370fbcbba011e4846'
STAGE95_RETRY_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage95-long-retry'
STAGE95_RETRY_RUNNER_SHA = '946b1cb9afdb6e53f9530459f4be7561e078340a198eab21ee1dcd16a1152711'
STAGE96_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage96'
STAGE96_RUNNER_SHA = 'd8bc7c3f981595528b92f175cedeccdad402dec3b1b6849a1d64c554bf047b5e'
STAGE101_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage101'
STAGE101_RUNNER_SHA = '4519e5b66e3fc8f1134dcae3926c9de2acf607470e7400916e3a91000f7b4a3d'
STAGE106_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage106'
STAGE106_RUNNER_SHA = '442bea0843ed614166bc00e9ae8daf95930022e763764fb48ceeae2ed5a1fcaf'
STAGE111_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage111'
STAGE111_RUNNER_SHA = '4c88c9d352d251478ba007c483767bd06ca9f9d6a6b1f444030d992f778e5e94'
STAGE116_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage116'
STAGE116_RUNNER_SHA = 'da39b0f0479e2b6ee60e43550f17e163bdc87b5f47c925fbd1180c1db0a6721f'
STAGE121_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage121'
STAGE121_RUNNER_SHA = 'a97de1ec2aa770cede25f2c4cf73a223214c82a4e82a6541298507bfc87212bd'
STAGE126_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage126'
STAGE126_RUNNER_SHA = '60a6d42394910d3ce5e3430d6d806464b7a9be050ff374b0ca5e1d399b6b994d'
STAGE131_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage131'
STAGE131_RUNNER_SHA = 'e9e61e7e89f956025ac09573a2e4cbf88a0c949ffe7a29a68a4911cf5a7d2737'
STAGE136_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage136'
STAGE136_RUNNER_SHA = '22349e4165491b9861c8135761d3859ee3b17735ba73c8433071642c54f62a22'
STAGE141_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage141'
STAGE141_RUNNER_SHA = '5eb2e5bf63d3e738307f5bed0ec8f0af55b15a71f6085925ab812390243128f3'
STAGE146_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage146'
STAGE146_RUNNER_SHA = '583e05f9d4ddea607df3f3b429ee3fd2b39cfa2743ad5639cbe9f66296ab72cb'
STAGE151_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage151'
STAGE151_RUNNER_SHA = 'b3f7a80f3dab1a4b724564ce2a24876178bffa658db323a9e6f2d28e981b051d'
STAGE156_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage156'
STAGE156_RUNNER_SHA = '846026a513dc994527beb78ea81962a6c1011802a8d454385fdc1c68a2e350eb'
STAGE161_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage161'
STAGE161_RUNNER_SHA = '9a796815750b5c24d806faf1a30aaa95d8cd853e20204f4a888392c2e7f89ec6'
STAGE166_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage166'
STAGE166_RUNNER_SHA = 'a255e5a7111d82cf83646551662dd85b88f44c2a69a4caa366cfed58e4e21ecb'
STAGE171_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage171'
STAGE171_RUNNER_SHA = 'f9cd1aca4fa7b13bc7376f1441102f9aec8f0b2ec5a912e5a5102f6690cafd7b'
STAGE176_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage176'
STAGE176_RUNNER_SHA = '07f9149536f2ee41eecd9d215c55b2a224098bde0bfbcfbd787972040cccf173'
STAGE181_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage181'
STAGE181_RUNNER_SHA = '42ceedf84a6b395ac4c95e59204151f4da530d1ea9662392bb079995c69d5ed5'
STAGE186_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage186'
STAGE186_RUNNER_SHA = 'bc0beedd944cbc7bc8936c805c4356f5cde029a7ad664ef61df9fc0e447879b5'
STAGE191_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage191'
STAGE191_RUNNER_SHA = '8e191a7cb9cc003965e7c2008e6ca18f919af9dae06873ccb8451c666bff4ef8'
STAGE196_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage196'
STAGE196_RUNNER_SHA = 'dec186238774609f31e73c1dd338d14d8ef1d3fb1c4e729252890cca84f30dbc'
STAGE197_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage197-warning-retry'
STAGE197_RUNNER_SHA = '43ed40f592406e902d36be404a3adc4f8ab492a5c80522e5e1d52bbed2e50105'
STAGE198_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage198'
STAGE198_RUNNER_SHA = '5e1d52e715eab8436a192b01d7ea3c790b99050510cdf70d1f6a34bc0fbce258'
STAGE203_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage203'
STAGE203_RUNNER_SHA = '19210479c7951ab61b08f861bbff275ea2f70a2e197becc0e1bac021a76c52cd'
STAGE208_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage208'
STAGE208_RUNNER_SHA = 'fd52d98b6e6daee71d9b769a278bdc8d509359ab7aa0dbdd05c7a8558bd0ba68'
WARNING_VERIFY_SHA = '7330742b4934efe8a35fd68f55d6e7e2aa329092a2881cfeba755939dba48c9c'
WARNING_EXPECTED_SHA = '99e2bfd537967357a084cd466ee67eaad26a8892b135d9b66dd1c591e0a81f00'
WARNING81_VERIFY_SHA = 'd05bd282b32a40eb97d72e9dbb05eb904b6d674fa0e9eecf1e9f04650848fada'
WARNING81_EXPECTED_SHA = 'c8876f4a91179aaf43af11f90ca9d67d00491f874c2ded22706c2c4545e9bdfd'
WARNING84_VERIFY_SHA = 'c525d03a80ea7b8b66a82a090f6ca9020bf89507722d9b2d5f861b7de2bffe02'
WARNING84_EXPECTED_SHA = 'ce41a6fcc3c0116286d878add6ddb33c1f9d39970c3d4285d71e77dcf08b9ddb'
WARNING197_VERIFY_SHA = '21c335e90ae8247f5f47638a46d8b6550e3d01a9a27e043a151474cbda7f74fa'
WARNING197_EXPECTED_SHA = '7c0c01e0b041b48ea83b9e4fe5cad46ddbe2c03c542b34ce6107a5aa3c630145'
REPO = HERE.parents[4]
MANIFEST = HERE.parent / 'compact12-ipra-integration-build/observations/attempt01/manifest.json'
FULL_SCAN = HERE.parent / 'compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
CONE = STAGE64_PACKET / 'cone-repinned.json'
EXPECT = {
    MANIFEST: '36ee7a0c7b881cefffafebd7d3a3ff678aec8010ca2019fe71dc8ff8ed29486e',
    FULL_SCAN: 'bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2',
    CONE: 'c9f4190a0d8807e5643f245a59ca53b23e52ca6c1dc1c1b74a5028651da049ec',
}
OVERLAY = Path('/tmp/compact12-ipra-integrated-20261102/lib')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PROJECT = Path('/tmp/compact12-ipra-expanded-coherent-20261102')
LIB = PROJECT / 'lib'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def check_resources():
    available = next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines()
                     if line.startswith('MemAvailable:'))
    if available < 8 * 1024 * 1024:
        raise RuntimeError('less than 8 GiB MemAvailable before a new stage')
    ps = subprocess.run(['ps', '-eo', 'args='], capture_output=True, text=True, check=True)
    live = [line for line in ps.stdout.splitlines() if '/bin/lean ' in line]
    if len(live) >= 2:
        raise RuntimeError('two Lean children already live before a new stage')

def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    if not path.is_file():
        raise RuntimeError(f'not a regular file or dangling dependency: {path}')
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}

def check_pins():
    for path, value in EXPECT.items():
        if digest(path) != value:
            raise RuntimeError(f'prerequisite drift: {path}')

def check_sources(cone):
    for m, row in cone['candidate_sources'].items():
        if len(row['canonical_candidates']) != 1 or not row['selected_imports_match']:
            raise RuntimeError(f'unsupported source: {m}')
        if digest(REPO / row['canonical_candidates'][0]) != row['source_sha256']:
            raise RuntimeError(f'source drift: {m}')

def verify_overlay(manifest):
    selected = manifest['overlay']
    actual = {p.relative_to(OVERLAY).as_posix() for p in OVERLAY.rglob('*') if p.is_file()}
    if actual != set(selected):
        raise RuntimeError('original overlay file set changed')
    for rel, row in selected.items():
        p = OVERLAY / rel
        if digest(p) != row['sha256'] or str(p.resolve(strict=True)) != row['resolved']:
            raise RuntimeError(f'original overlay drift: {rel}')

def receipt_dir(index):
    batch = (index - 1) // 5 + 1
    base = (FIRST_PACKET if index <= 5 else SECOND_PACKET if index <= 10 else
            THIRD_PACKET if index <= 15 else FOURTH_PACKET if index <= 20 else
            FIFTH_PACKET if index <= 25 else SIXTH_PACKET if index <= 30 else
            SEVENTH_PACKET if index <= 35 else EIGHTH_PACKET if index <= 40 else
            NINTH_PACKET if index <= 45 else TENTH_PACKET if index <= 50 else
            ELEVENTH_PACKET if index <= 55 else TWELFTH_PACKET if index <= 56 else
            STAGE57_PACKET if index <= 57 else STAGE58_PACKET if index <= 58 else
            STAGE59_PACKET if index <= 59 else STAGE60_PACKET if index <= 60 else
            STAGE61_PACKET if index <= 61 else STAGE62_PACKET if index <= 62 else
            STAGE63_PACKET if index <= 63 else STAGE64_PACKET if index <= 64 else
            STAGE65_PACKET if index <= 65 else STAGE66_PACKET if index <= 66 else
            STAGE67_PACKET if index <= 71 else STAGE72_PACKET if index <= 76 else
            STAGE77_PACKET if index <= 78 else STAGE79_PACKET if index <= 79 else
            STAGE80_PACKET if index <= 80 else STAGE81_PACKET if index <= 81 else
            STAGE82_PACKET if index <= 83 else STAGE84_PACKET if index <= 84 else
            STAGE85_PACKET if index <= 89 else STAGE90_PACKET if index <= 94 else
            STAGE95_RETRY_PACKET if index <= 95 else STAGE96_PACKET if index <= 100 else
            STAGE101_PACKET if index <= 105 else STAGE106_PACKET if index <= 110 else
            STAGE111_PACKET if index <= 115 else STAGE116_PACKET if index <= 120 else
            STAGE121_PACKET if index <= 125 else STAGE126_PACKET if index <= 130 else
            STAGE131_PACKET if index <= 135 else STAGE136_PACKET if index <= 140 else
            STAGE141_PACKET if index <= 145 else STAGE146_PACKET if index <= 150 else
            STAGE151_PACKET if index <= 155 else STAGE156_PACKET if index <= 160 else
            STAGE161_PACKET if index <= 165 else STAGE166_PACKET if index <= 170 else
            STAGE171_PACKET if index <= 175 else STAGE176_PACKET if index <= 180 else
            STAGE181_PACKET if index <= 185 else STAGE186_PACKET if index <= 190 else
            STAGE191_PACKET if index <= 195 else STAGE196_PACKET if index <= 196 else
            STAGE197_PACKET if index <= 197 else STAGE198_PACKET if index <= 202 else
            STAGE203_PACKET if index <= 207 else STAGE208_PACKET if index <= 212 else HERE)
    return base / 'observations' / f'batch-{batch:03d}' / f'stage-{index:04d}'

def check_prior(order, base):
    previous, gap = [], False
    for index, module in enumerate(order, 1):
        obs = receipt_dir(index)
        terminal = obs / 'terminal.json'
        if not terminal.exists():
            if obs.exists():
                raise RuntimeError(f'incomplete previous stage: {obs}')
            gap = True
            continue
        if gap:
            raise RuntimeError(f'noncontiguous stage: {obs}')
        row = json.loads(terminal.read_text())
        output = LIB / (module.replace('.', '/') + '.olean')
        if (row.get('module') != module or not row.get('success') or row.get('exit_code') != 0 or
            not output.is_file() or output.is_symlink() or digest(output) != row.get('object_sha256') or
            digest(obs / 'compile.log') != row.get('log_sha256') or
            row.get('guards') != {p: record(p) for p in row.get('guards', {})}):
            raise RuntimeError(f'prior stage validation failed: {obs}')
        if index == 79:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE79_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 79 warning baseline no longer validates')
        if index == 81:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE81_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 81 warning baseline no longer validates')
        if index == 84:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE84_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 84 warning baseline no longer validates')
        if index == 197:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE197_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 197 warning baseline no longer validates')
        previous.append(row)
    expected = set(base) | {m.replace('.', '/') + '.olean' for m in order[:len(previous)]}
    actual = {p.relative_to(LIB).as_posix() for p in LIB.rglob('*') if p.is_file()}
    if actual != expected:
        raise RuntimeError('merged build file set mismatch')
    for rel, row in base.items():
        p = LIB / rel
        if not p.is_symlink() or digest(p) != row['sha256'] or str(p.resolve(strict=True)) != row['resolved']:
            raise RuntimeError(f'merged selected input drift: {rel}')
    return previous

def main():
    count = int(sys.argv[1]) if len(sys.argv) == 2 else 1
    if not 1 <= count <= 5:
        raise ValueError('pass a stage count from 1 through 5')
    if shutil.disk_usage('/tmp').free < 4 * 1024**3:
        raise RuntimeError('less than 4 GiB free')
    if digest(FIRST_PACKET / 'run.py') != FIRST_RUNNER_SHA:
        raise RuntimeError('first batch runner drift')
    if digest(SECOND_PACKET / 'run.py') != SECOND_RUNNER_SHA:
        raise RuntimeError('second batch runner drift')
    if digest(THIRD_PACKET / 'run.py') != THIRD_RUNNER_SHA:
        raise RuntimeError('third batch runner drift')
    if digest(FOURTH_PACKET / 'run.py') != FOURTH_RUNNER_SHA:
        raise RuntimeError('fourth batch runner drift')
    if digest(FIFTH_PACKET / 'run.py') != FIFTH_RUNNER_SHA:
        raise RuntimeError('fifth batch runner drift')
    if digest(SIXTH_PACKET / 'run.py') != SIXTH_RUNNER_SHA:
        raise RuntimeError('sixth batch runner drift')
    if digest(SEVENTH_PACKET / 'run.py') != SEVENTH_RUNNER_SHA:
        raise RuntimeError('seventh batch runner drift')
    if digest(EIGHTH_PACKET / 'run.py') != EIGHTH_RUNNER_SHA:
        raise RuntimeError('eighth batch runner drift')
    if digest(NINTH_PACKET / 'run.py') != NINTH_RUNNER_SHA:
        raise RuntimeError('ninth batch runner drift')
    if digest(TENTH_PACKET / 'run.py') != TENTH_RUNNER_SHA:
        raise RuntimeError('tenth batch runner drift')
    if digest(ELEVENTH_PACKET / 'run.py') != ELEVENTH_RUNNER_SHA:
        raise RuntimeError('eleventh batch runner drift')
    if digest(TWELFTH_PACKET / 'run.py') != TWELFTH_RUNNER_SHA:
        raise RuntimeError('twelfth batch runner drift')
    if digest(STAGE57_PACKET / 'run.py') != STAGE57_RUNNER_SHA:
        raise RuntimeError('stage 57 runner drift')
    if digest(STAGE58_PACKET / 'run.py') != STAGE58_RUNNER_SHA:
        raise RuntimeError('stage 58 runner drift')
    if digest(STAGE59_PACKET / 'run.py') != STAGE59_RUNNER_SHA:
        raise RuntimeError('stage 59 runner drift')
    if digest(STAGE60_PACKET / 'run.py') != STAGE60_RUNNER_SHA:
        raise RuntimeError('stage 60 runner drift')
    if digest(STAGE61_PACKET / 'run.py') != STAGE61_RUNNER_SHA:
        raise RuntimeError('stage 61 runner drift')
    if digest(STAGE62_PACKET / 'run.py') != STAGE62_RUNNER_SHA:
        raise RuntimeError('stage 62 runner drift')
    if digest(STAGE63_PACKET / 'run.py') != STAGE63_RUNNER_SHA:
        raise RuntimeError('stage 63 runner drift')
    if digest(STAGE64_PACKET / 'run.py') != STAGE64_RUNNER_SHA:
        raise RuntimeError('stage 64 retry runner drift')
    if digest(STAGE65_PACKET / 'run.py') != STAGE65_RUNNER_SHA:
        raise RuntimeError('stage 65 runner drift')
    if digest(STAGE66_PACKET / 'run.py') != STAGE66_RUNNER_SHA:
        raise RuntimeError('stage 66 runner drift')
    if digest(STAGE67_PACKET / 'run.py') != STAGE67_RUNNER_SHA:
        raise RuntimeError('stages 67–71 runner drift')
    if digest(STAGE72_PACKET / 'run.py') != STAGE72_RUNNER_SHA:
        raise RuntimeError('stages 72–76 runner drift')
    if digest(STAGE77_PACKET / 'run.py') != STAGE77_RUNNER_SHA:
        raise RuntimeError('stages 77–78 runner drift')
    if digest(STAGE79_PACKET / 'run.py') != STAGE79_RUNNER_SHA:
        raise RuntimeError('stage 79 retry runner drift')
    if digest(STAGE80_PACKET / 'run.py') != STAGE80_RUNNER_SHA:
        raise RuntimeError('stage 80 runner drift')
    if digest(STAGE81_PACKET / 'run.py') != STAGE81_RUNNER_SHA:
        raise RuntimeError('stage 81 retry runner drift')
    if digest(STAGE82_PACKET / 'run.py') != STAGE82_RUNNER_SHA:
        raise RuntimeError('stages 82–83 runner drift')
    if digest(STAGE84_PACKET / 'run.py') != STAGE84_RUNNER_SHA:
        raise RuntimeError('stage 84 retry runner drift')
    if digest(STAGE85_PACKET / 'run.py') != STAGE85_RUNNER_SHA:
        raise RuntimeError('stages 85–89 runner drift')
    if digest(STAGE90_PACKET / 'run.py') != STAGE90_RUNNER_SHA:
        raise RuntimeError('stages 90–94 runner drift')
    if digest(STAGE95_FAILED_PACKET / 'run.py') != STAGE95_FAILED_RUNNER_SHA:
        raise RuntimeError('failed stage 95 runner drift')
    if digest(STAGE95_RETRY_PACKET / 'run.py') != STAGE95_RETRY_RUNNER_SHA:
        raise RuntimeError('stage 95 retry runner drift')
    if digest(STAGE96_PACKET / 'run.py') != STAGE96_RUNNER_SHA:
        raise RuntimeError('stages 96–100 runner drift')
    if digest(STAGE101_PACKET / 'run.py') != STAGE101_RUNNER_SHA:
        raise RuntimeError('stages 101–105 runner drift')
    if digest(STAGE106_PACKET / 'run.py') != STAGE106_RUNNER_SHA:
        raise RuntimeError('stages 106–110 runner drift')
    if digest(STAGE111_PACKET / 'run.py') != STAGE111_RUNNER_SHA:
        raise RuntimeError('stages 111–115 runner drift')
    if digest(STAGE116_PACKET / 'run.py') != STAGE116_RUNNER_SHA:
        raise RuntimeError('stages 116–120 runner drift')
    if digest(STAGE121_PACKET / 'run.py') != STAGE121_RUNNER_SHA:
        raise RuntimeError('stages 121–125 runner drift')
    if digest(STAGE126_PACKET / 'run.py') != STAGE126_RUNNER_SHA:
        raise RuntimeError('stages 126–130 runner drift')
    if digest(STAGE131_PACKET / 'run.py') != STAGE131_RUNNER_SHA:
        raise RuntimeError('stages 131–135 runner drift')
    if digest(STAGE136_PACKET / 'run.py') != STAGE136_RUNNER_SHA:
        raise RuntimeError('stages 136–140 runner drift')
    if digest(STAGE141_PACKET / 'run.py') != STAGE141_RUNNER_SHA:
        raise RuntimeError('stages 141–145 runner drift')
    if digest(STAGE146_PACKET / 'run.py') != STAGE146_RUNNER_SHA:
        raise RuntimeError('stages 146–150 runner drift')
    if digest(STAGE151_PACKET / 'run.py') != STAGE151_RUNNER_SHA:
        raise RuntimeError('stages 151–155 runner drift')
    if digest(STAGE156_PACKET / 'run.py') != STAGE156_RUNNER_SHA:
        raise RuntimeError('stages 156–160 runner drift')
    if digest(STAGE161_PACKET / 'run.py') != STAGE161_RUNNER_SHA:
        raise RuntimeError('stages 161–165 runner drift')
    if digest(STAGE166_PACKET / 'run.py') != STAGE166_RUNNER_SHA:
        raise RuntimeError('stages 166–170 runner drift')
    if digest(STAGE171_PACKET / 'run.py') != STAGE171_RUNNER_SHA:
        raise RuntimeError('stages 171–175 runner drift')
    if digest(STAGE176_PACKET / 'run.py') != STAGE176_RUNNER_SHA:
        raise RuntimeError('stages 176–180 runner drift')
    if digest(STAGE181_PACKET / 'run.py') != STAGE181_RUNNER_SHA:
        raise RuntimeError('stages 181–185 runner drift')
    if digest(STAGE186_PACKET / 'run.py') != STAGE186_RUNNER_SHA:
        raise RuntimeError('stages 186–190 runner drift')
    if digest(STAGE191_PACKET / 'run.py') != STAGE191_RUNNER_SHA:
        raise RuntimeError('stages 191–195 runner drift')
    if digest(STAGE196_PACKET / 'run.py') != STAGE196_RUNNER_SHA:
        raise RuntimeError('stage 196 runner drift')
    if digest(STAGE197_PACKET / 'run.py') != STAGE197_RUNNER_SHA:
        raise RuntimeError('stage 197 retry runner drift')
    if digest(STAGE198_PACKET / 'run.py') != STAGE198_RUNNER_SHA:
        raise RuntimeError('stages 198–202 runner drift')
    if digest(STAGE203_PACKET / 'run.py') != STAGE203_RUNNER_SHA:
        raise RuntimeError('stages 203–207 runner drift')
    if digest(STAGE208_PACKET / 'run.py') != STAGE208_RUNNER_SHA:
        raise RuntimeError('stages 208–212 runner drift')
    if digest(STAGE79_PACKET / 'verify_warning.py') != WARNING_VERIFY_SHA or digest(STAGE79_PACKET / 'expected-warning.txt') != WARNING_EXPECTED_SHA:
        raise RuntimeError('warning verifier or baseline drift')
    if digest(STAGE81_PACKET / 'verify_warning.py') != WARNING81_VERIFY_SHA or digest(STAGE81_PACKET / 'expected-warning.txt') != WARNING81_EXPECTED_SHA:
        raise RuntimeError('stage 81 warning verifier or baseline drift')
    if digest(STAGE84_PACKET / 'verify_warning.py') != WARNING84_VERIFY_SHA or digest(STAGE84_PACKET / 'expected-warning.txt') != WARNING84_EXPECTED_SHA:
        raise RuntimeError('stage 84 warning verifier or baseline drift')
    if digest(STAGE197_PACKET / 'verify_warning.py') != WARNING197_VERIFY_SHA or digest(STAGE197_PACKET / 'expected-warning.txt') != WARNING197_EXPECTED_SHA:
        raise RuntimeError('stage 197 warning verifier or baseline drift')
    PROJECT.mkdir(exist_ok=True)
    lock = (PROJECT / 'build.lock').open('a+')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    check_pins()
    manifest = json.loads(MANIFEST.read_text())
    full = json.loads(FULL_SCAN.read_text())
    cone = json.loads(CONE.read_text())
    if (not full['complete'] or not full['overlay_unchanged'] or not full['omitted_unchanged'] or
        full['unresolved_direct_imports'] or cone['scan_sha256'] != EXPECT[FULL_SCAN]):
        raise RuntimeError('selected-object scan did not pass')
    order = cone['topological_candidate']
    if len(order) != 425 or len(set(order)) != 425:
        raise RuntimeError('unexpected candidate cone')
    check_sources(cone)
    verify_overlay(manifest)
    omitted_families = {m.replace('.', '/') + '.olean' for m in order}
    base = {rel: row for rel, row in manifest['overlay'].items() if rel not in omitted_families}
    if len(base) != len(manifest['overlay']) - 366:
        raise RuntimeError('unexpected removed selected object count')
    baseline = {'scope': 'selected project object rebuild preflight; package and dynamic ancestry remain open',
                'input_sha256': {str(p): h for p, h in EXPECT.items()},
                'lean_sha256': digest(LEAN), 'runner_sha256': FIRST_RUNNER_SHA,
                'retained_selected_objects': base,
                'removed_object_families': sorted(omitted_families), 'topological_order': order,
                'source_sha256': {m: cone['candidate_sources'][m]['source_sha256'] for m in order}}
    original_baseline = FIRST_PACKET / 'observations' / 'baseline.json'
    if digest(original_baseline) != 'f89d5466637be18ca5e95492df05e329a8ccc1be6d9fb150602fc975089b1aea':
        raise RuntimeError('original baseline drift')
    original = json.loads(original_baseline.read_text())
    if (original['retained_selected_objects'] != base or original['topological_order'] != order or
        original['source_sha256']['BusyBeaver.ZFC.L2Root254'] != '20b2ef7733a0d85c5248ee598b5386f42ad46319a003488fb63bfacb7f737e9f'):
        raise RuntimeError('re-pin changes baseline beyond the intended source')
    original_sources = dict(original['source_sha256'])
    original_sources['BusyBeaver.ZFC.L2Root254'] = 'fee84717177d6575f576ae3e09a3a034071f02422b7a5ef8d9d68e7822864d10'
    if original_sources != baseline['source_sha256']:
        raise RuntimeError('other source pins changed')
    baseline['supersedes_baseline_sha256'] = digest(original_baseline)
    baseline_text = json.dumps(baseline, indent=2, sort_keys=True) + '\n'
    baseline_path = STAGE64_PACKET / 'observations' / 'baseline-repinned.json'
    if baseline_path.exists():
        if baseline_path.read_text() != baseline_text:
            raise RuntimeError('rebuild baseline changed on resume')
    else:
        raise RuntimeError('re-pinned baseline is missing')
    if not LIB.exists():
        LIB.mkdir()
        for rel, row in base.items():
            p = LIB / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.symlink_to(row['resolved'])
    # The rejected attempt's newly emitted object must never be imported.
    # Move only the exact recorded rejected bytes to a fresh quarantine path.
    rejected = LIB / 'BusyBeaver/ZFC/L2Root254.olean'
    quarantine = PROJECT / 'quarantine/stage-0064-rejected.olean'
    expected_rejected = '16e2ea23478f0720e51544e6ff25c51f061b2513d2f0871ec079b00a4eb63202'
    if not quarantine.is_file() or digest(quarantine) != expected_rejected:
        raise RuntimeError('missing rejected-object quarantine')
    rejected79 = LIB / 'BusyBeaver/ZFC/KLowerRaw.olean'
    quarantine79 = PROJECT / 'quarantine/stage-0079-rejected.olean'
    rejected79_sha = 'ca70aa5d67e2fdc4efef374b6071d4e5801046b2bc1cb863ebb43e5440dcca1c'
    failed_obs = STAGE77_PACKET / 'observations/batch-016/stage-0079'
    if digest(failed_obs / 'terminal.json') != '3caf2da10031812c42037dc9c03adfe253c7f1c8d2c1ee19a8a099cd4988d94a':
        raise RuntimeError('rejected stage 79 receipt drift')
    failed = json.loads((failed_obs / 'terminal.json').read_text())
    if failed['guards'] != {p: record(p) for p in failed['guards']}:
        raise RuntimeError('rejected stage 79 dependency drift')
    own79 = receipt_dir(79) / 'terminal.json'
    if not own79.exists():
        if rejected79.exists():
            if rejected79.is_symlink() or digest(rejected79) != rejected79_sha or quarantine79.exists():
                raise RuntimeError('unexpected rejected stage 79 object state')
            quarantine79.parent.mkdir(parents=True, exist_ok=True)
            rejected79.rename(quarantine79)
        if not quarantine79.is_file() or digest(quarantine79) != rejected79_sha:
            raise RuntimeError('missing stage 79 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected79), 'quarantine_path': str(quarantine79),
                             'sha256': rejected79_sha, 'reason': 'rejected unbaselined linter warning'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage79.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine79.is_file() or digest(quarantine79) != rejected79_sha:
        raise RuntimeError('stage 79 rejected-object quarantine drift')
    rejected81 = LIB / 'BusyBeaver/ZFC/KLowerTag.olean'
    quarantine81 = PROJECT / 'quarantine/stage-0081-rejected.olean'
    rejected81_sha = '48cf2bbd2d623aa105568704dc61b0ec1c073531e85d133a5df46e603d796829'
    failed81_obs = STAGE80_PACKET / 'observations/batch-017/stage-0081'
    if digest(failed81_obs / 'terminal.json') != '3867e52e153de570e8042e78d5b3ec4ce9a982bbb5fe16a04f81ecdccbb5030f':
        raise RuntimeError('rejected stage 81 receipt drift')
    failed81 = json.loads((failed81_obs / 'terminal.json').read_text())
    if failed81['guards'] != {p: record(p) for p in failed81['guards']}:
        raise RuntimeError('rejected stage 81 dependency drift')
    own81 = receipt_dir(81) / 'terminal.json'
    if not own81.exists():
        if rejected81.exists():
            if rejected81.is_symlink() or digest(rejected81) != rejected81_sha or quarantine81.exists():
                raise RuntimeError('unexpected rejected stage 81 object state')
            quarantine81.parent.mkdir(parents=True, exist_ok=True)
            rejected81.rename(quarantine81)
        if not quarantine81.is_file() or digest(quarantine81) != rejected81_sha:
            raise RuntimeError('missing stage 81 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected81), 'quarantine_path': str(quarantine81),
                             'sha256': rejected81_sha, 'reason': 'rejected unbaselined linter warning'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage81.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine81.is_file() or digest(quarantine81) != rejected81_sha:
        raise RuntimeError('stage 81 rejected-object quarantine drift')
    rejected84 = LIB / 'BusyBeaver/ZFC/KQ1Model.olean'
    quarantine84 = PROJECT / 'quarantine/stage-0084-rejected.olean'
    rejected84_sha = 'e52477f9a7fc2b6aae82a387281beb829246270cf7b3fbf6d3bdadb052077729'
    failed84_obs = STAGE82_PACKET / 'observations/batch-017/stage-0084'
    if digest(failed84_obs / 'terminal.json') != '371aac007260fc9b65875c5e57c9ac279f63ca3dc509227dcbbc9ed426f78539':
        raise RuntimeError('rejected stage 84 receipt drift')
    failed84 = json.loads((failed84_obs / 'terminal.json').read_text())
    if failed84['guards'] != {p: record(p) for p in failed84['guards']}:
        raise RuntimeError('rejected stage 84 dependency drift')
    own84 = receipt_dir(84) / 'terminal.json'
    if not own84.exists():
        if rejected84.exists():
            if rejected84.is_symlink() or digest(rejected84) != rejected84_sha or quarantine84.exists():
                raise RuntimeError('unexpected rejected stage 84 object state')
            quarantine84.parent.mkdir(parents=True, exist_ok=True)
            rejected84.rename(quarantine84)
        if not quarantine84.is_file() or digest(quarantine84) != rejected84_sha:
            raise RuntimeError('missing stage 84 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected84), 'quarantine_path': str(quarantine84),
                             'sha256': rejected84_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage84.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine84.is_file() or digest(quarantine84) != rejected84_sha:
        raise RuntimeError('stage 84 rejected-object quarantine drift')
    rejected197 = LIB / 'BusyBeaver/ZFC/KQ1Basic.olean'
    quarantine197 = PROJECT / 'quarantine/stage-0197-rejected.olean'
    rejected197_sha = 'fd61d67e686d620b818bb53cca8d9e2eb2fa49c6cd70731bfdffea92c078c171'
    failed197_obs = STAGE196_PACKET / 'observations/batch-040/stage-0197'
    if digest(failed197_obs / 'terminal.json') != 'f45cbcae8451ef8800ffdd028b2e962f6fc6a81ebf68b3b742e5f4d4643f4662':
        raise RuntimeError('rejected stage 197 receipt drift')
    failed197 = json.loads((failed197_obs / 'terminal.json').read_text())
    if failed197['guards'] != {p: record(p) for p in failed197['guards']}:
        raise RuntimeError('rejected stage 197 dependency drift')
    own197 = receipt_dir(197) / 'terminal.json'
    if not own197.exists():
        if rejected197.exists():
            if rejected197.is_symlink() or digest(rejected197) != rejected197_sha or quarantine197.exists():
                raise RuntimeError('unexpected rejected stage 197 object state')
            quarantine197.parent.mkdir(parents=True, exist_ok=True)
            rejected197.rename(quarantine197)
        if not quarantine197.is_file() or digest(quarantine197) != rejected197_sha:
            raise RuntimeError('missing stage 197 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected197), 'quarantine_path': str(quarantine197),
                             'sha256': rejected197_sha, 'reason': 'rejected unbaselined linter warning'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage197.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine197.is_file() or digest(quarantine197) != rejected197_sha:
        raise RuntimeError('stage 197 rejected-object quarantine drift')
    failed95_obs = STAGE95_FAILED_PACKET / 'observations/batch-019/stage-0095'
    if digest(failed95_obs / 'terminal.json') != '80ab9eeb822e89f2664b7b2c3884ffaf3ae96dd718c3fb54ba85c3e86f95bb1e':
        raise RuntimeError('failed stage 95 receipt drift')
    failed95 = json.loads((failed95_obs / 'terminal.json').read_text())
    if (failed95['exit_code'] is not None or failed95['object_sha256'] is not None or
        not failed95['source_unchanged'] or not failed95['guards_unchanged'] or
        failed95['guards'] != {p: record(p) for p in failed95['guards']}):
        raise RuntimeError('failed stage 95 guards or outcome changed')
    previous = check_prior(order, base)
    env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': f'{LIB}:{PACKAGE}', 'LEAN_NUM_THREADS': '1'}
    for position in range(len(previous), min(len(previous) + count, len(order))):
        check_resources()
        if shutil.disk_usage('/tmp').free < 4 * 1024**3:
            raise RuntimeError('less than 4 GiB free')
        module = order[position]
        index = position + 1
        row = cone['candidate_sources'][module]
        source = REPO / row['canonical_candidates'][0]
        suffix = module.replace('.', '/') + '.lean'
        root = str(source)[:-len(suffix)].rstrip('/')
        if str(source) != root + '/' + suffix:
            raise RuntimeError(f'source root mismatch: {module}')
        output = LIB / (module.replace('.', '/') + '.olean')
        if os.path.lexists(output):
            raise RuntimeError(f'output already exists: {output}')
        output.parent.mkdir(parents=True, exist_ok=True)
        obs = receipt_dir(index)
        obs.mkdir(parents=True, exist_ok=False)
        (obs / 'source.lean').write_bytes(source.read_bytes())
        deps = subprocess.run([str(LEAN), '--deps', str(source)], env=env,
                              capture_output=True, text=True, timeout=120)
        (obs / 'deps').write_text(deps.stdout)
        (obs / 'deps.stderr').write_text(deps.stderr)
        if deps.returncode != 0 or deps.stderr:
            raise RuntimeError(f'dependency scan failed: {module}')
        guards = {}
        for line in deps.stdout.splitlines():
            path = Path(line)
            if not path.is_absolute() or not path.is_file() or path.suffix != '.olean':
                raise RuntimeError(f'missing or invalid dependency for {module}: {line}')
            stem = str(path)[:-len('.olean')]
            for ending in SUFFIXES:
                guards[stem + ending] = record(stem + ending)
        command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={root}',
                   str(source), '-o', str(output)]
        start = time.monotonic()
        try:
            proc = subprocess.run(command, env=env, capture_output=True, text=True,
                                  timeout=600 if index == 95 else 180)
            code, log = proc.returncode, proc.stdout + proc.stderr
        except subprocess.TimeoutExpired as exc:
            code = None
            log = ((exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout, bytes) else (exc.stdout or ''))
            log += ((exc.stderr or b'').decode(errors='replace') if isinstance(exc.stderr, bytes) else (exc.stderr or ''))
        (obs / 'compile.log').write_text(log)
        guards_ok = guards == {path: record(path) for path in guards}
        source_ok = digest(source) == row['source_sha256']
        accepted_warning = False
        if index in (79, 81, 84, 197):
            verifier = (STAGE79_PACKET / 'verify_warning.py' if index == 79 else
                        STAGE81_PACKET / 'verify_warning.py' if index == 81 else
                        STAGE84_PACKET / 'verify_warning.py' if index == 84 else STAGE197_PACKET / 'verify_warning.py')
            verified = subprocess.run([sys.executable, '-I', '-B', str(verifier),
                                       str(obs / 'compile.log')], capture_output=True, text=True)
            (obs / 'warning-verifier.stdout').write_text(verified.stdout)
            (obs / 'warning-verifier.stderr').write_text(verified.stderr)
            accepted_warning = (verified.returncode == 0 and not verified.stderr)
        clean = not any(x in log for x in ('error:', 'warning:', 'sorryAx'))
        success = (code == 0 and output.is_file() and not output.is_symlink() and guards_ok and source_ok and
                   (accepted_warning if index in (79, 81, 84, 197) else clean))
        terminal = {'index': index, 'module': module, 'command': command, 'exit_code': code,
                    'duration_seconds': round(time.monotonic() - start, 3),
                    'wall_timeout_seconds': 600 if index == 95 else 180,
                    'runner_sha256': digest(Path(__file__)), 'lean_sha256': digest(LEAN),
                    'source_sha256': digest(source), 'source_unchanged': source_ok,
                    'guards': guards, 'guards_unchanged': guards_ok,
                    'object_sha256': digest(output) if output.is_file() else None,
                    'log_sha256': digest(obs / 'compile.log'), 'success': success,
                    'accepted_exact_warning': accepted_warning,
                    'scope': 'author prefix; dynamic, package and original provider ancestry not authenticated'}
        (obs / 'terminal.json').write_text(json.dumps(terminal, indent=2, sort_keys=True) + '\n')
        print(json.dumps({k: terminal[k] for k in ('index', 'module', 'exit_code', 'duration_seconds', 'success')},
                         sort_keys=True), flush=True)
        if not success:
            raise RuntimeError(f'stage failed: {module}; inspect before retry')
    check_pins()
    check_sources(cone)
    verify_overlay(manifest)
    done = check_prior(order, base)
    print(json.dumps({'completed': len(done), 'total': len(order), 'overlay_unchanged': True}, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
