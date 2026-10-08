"""Cross-platform test entrypoint: python run_tests.py."""
import pathlib,sys,unittest
ROOT=pathlib.Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT/'src'),str(ROOT)]
result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.discover(str(ROOT/'tests')))
raise SystemExit(not result.wasSuccessful())
