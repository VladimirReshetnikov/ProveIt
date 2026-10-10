#!/usr/bin/env python3
"""Local integration guards and generated-chapter consistency tests.
Uses synthetic files to test guards, not an unperformed full repository merge.
"""
from __future__ import annotations
from pathlib import Path
import runpy
import re
import tempfile
import unittest

ROOT=Path(__file__).resolve().parent.parent
API=runpy.run_path(str(ROOT/'integration/apply_integration.py'))

class IntegrationTests(unittest.TestCase):
    def test_chapter_consistency(self):
        article=(ROOT/'article.tex').read_text()
        body=article[article.index(r'\section{Scope, provenance'):article.index(r'\begin{thebibliography}')]
        body=re.sub(r'\\F(?![A-Za-z])',r'\\LBf',body)
        for command in ['label','ref','eqref']:
            body=re.sub(r'\\'+command+r'\{([^}]+)\}',lambda m:'\\'+command+'{lerchbd:'+m[1]+'}',body)
        body=re.sub(r'\\cite\{([^}]+)\}',lambda m:r'\cite{'+','.join('lerchbd:'+k for k in m[1].split(','))+'}',body)
        body=body.replace('at the commit displayed on the title page',r'at commit \src{6ec0b2c11ba3932107aa1e8bdf20627e3ced86fc}')
        body=body.replace('the included \\src{INTEGRATION.md}',"the accompanying report's \\src{INTEGRATION.md}")
        chapter=(ROOT/'integration/09-lerch-boundary.tex').read_text()
        self.assertEqual(chapter[chapter.index(r'\section{Scope, provenance'):],body)
        labels=re.findall(r'\\label\{([^}]+)\}',chapter)
        refs=re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',chapter)
        self.assertEqual(len(labels),len(set(labels)))
        self.assertTrue(set(refs)<=set(labels))
        citations=set()
        for group in re.findall(r'\\cite\{([^}]+)\}',chapter):citations.update(group.split(','))
        bibliography=(ROOT/'integration/lerch-boundary-bibliography.tex').read_text()
        keys=set(re.findall(r'\\bibitem\{([^}]+)\}',bibliography))
        self.assertTrue(citations<=keys)

    def test_snapshot_guard_and_no_writes(self):
        with tempfile.TemporaryDirectory() as d:
            repo=Path(d);base=repo/'manuscript';base.mkdir()
            file=base/'test.tex';original=b'old anchor\n';file.write_bytes(original)
            manifest={'base_directory':'manuscript','edits':[
                {'path':'test.tex','expected_blob':API['blob_sha'](original),
                 'replacements':[{'old':'old anchor','new':'new anchor'}]}], 'new_files':[]}
            changes=API['prepare'](repo,manifest)
            self.assertEqual(len(changes),1)
            self.assertEqual(changes[0][2],b'new anchor\n')
            self.assertEqual(file.read_bytes(),original) # prepare never writes
            manifest['edits'][0]['expected_blob']='0'*40
            with self.assertRaises(ValueError):API['prepare'](repo,manifest)
            self.assertEqual(file.read_bytes(),original)

    def test_path_confinement(self):
        with tempfile.TemporaryDirectory() as d:
            base=Path(d)
            with self.assertRaises(ValueError):API['confined'](base,'../../escape')
            self.assertEqual(API['confined'](base,'ok.tex'),base/'ok.tex')

if __name__=='__main__':unittest.main(verbosity=2)
