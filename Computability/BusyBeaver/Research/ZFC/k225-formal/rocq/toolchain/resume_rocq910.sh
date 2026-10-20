#!/bin/bash
# Resume the Rocq 9.1.0 build in R:\b\r: build the three packages together (dune reuses the cached
# rocq-runtime / coq-core objects), install them, then build and install rocq-stdlib 9.0.0.
set -e
SW=/cygdrive/c/Users/vresh/AppData/Local/opam/rocq-9.2
B=/cygdrive/r/build
P=/cygdrive/r/rocq910
PW='R:\rocq910'
export PATH="$SW/bin:/usr/bin:/usr/x86_64-w64-mingw32/sys-root/mingw/bin:/cygdrive/c/WINDOWS/system32:/cygdrive/c/WINDOWS"
export OPAMSWITCH=rocq-9.2
export OPAM_SWITCH_PREFIX='C:\Users\vresh\AppData\Local\opam\rocq-9.2'
export CAML_LD_LIBRARY_PATH='C:\Users\vresh\AppData\Local\opam\rocq-9.2\lib\stublibs;C:\Users\vresh\AppData\Local\opam\rocq-9.2\lib\ocaml\stublibs;C:\Users\vresh\AppData\Local\opam\rocq-9.2\lib\ocaml'
export OCAMLTOP_INCLUDE_PATH='C:\Users\vresh\AppData\Local\opam\rocq-9.2\lib\toplevel'
cd /cygdrive/r/b/r
echo "== all three packages"; dune build -p rocq-runtime,coq-core,rocq-core -j 2 @install
echo "== install"; dune install --prefix "$PW" --libdir 'R:\rocq910\lib' rocq-runtime coq-core rocq-core
export PATH="$P/bin:$PATH"
echo "== installed"; which coqc; coqc --version; coqc -where
cd /cygdrive/r/b
rm -rf stdlib-9.0.0
tar xzf $B/stdlib-9.0.0.tar.gz
cd stdlib-9.0.0
echo "== stdlib build"; make -j 2
echo "== stdlib install"; make install
echo "== probe"; printf 'From Stdlib Require Import FinFun.\nCheck FinFun.Injective.\n' > /cygdrive/r/b/Probe.v; coqc /cygdrive/r/b/Probe.v
echo ROCQ910_DONE
