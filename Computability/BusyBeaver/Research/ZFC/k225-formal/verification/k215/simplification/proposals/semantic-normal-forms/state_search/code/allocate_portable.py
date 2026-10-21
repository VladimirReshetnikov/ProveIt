#!/usr/bin/env python3
"""Portable entry point for the exact adapted allocator used in this packet.

--zfc-root must contain candidate-k215/{k215.native.tm,sites215.json}.
This overrides only the snapshot's historical local default path. The hashed
allocator and its pinned input requirements remain unchanged.
"""
import argparse,sys
from pathlib import Path
import allocate_ax9 as allocator
p=argparse.ArgumentParser(add_help=False)
p.add_argument('--zfc-root',type=Path,required=True)
a,remaining=p.parse_known_args()
allocator.K=a.zfc_root.resolve()
allocator.ENGINE=Path(__file__).resolve().parent/'frozen_engine_rows219.json'
sys.argv=[sys.argv[0],*remaining]
allocator.main()
