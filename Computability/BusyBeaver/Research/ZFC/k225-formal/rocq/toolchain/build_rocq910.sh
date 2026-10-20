#!/bin/bash
# Build Rocq 9.1.0 + rocq-stdlib 9.0.0 into a private prefix, using the OCaml 4.14.2 toolchain of
# the existing opam switch rocq-9.2 (left untouched). Run with opam's Cygwin bash.
# All paths go through the subst drive R: (= scratchpad/rocq225), to stay under MAX_PATH.
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
echo "== tools"; which ocaml dune ocamlfind make x86_64-w64-mingw32-gcc; ocaml -version; dune --version
mkdir -p /cygdrive/r/b
cd /cygdrive/r/b
rm -rf r stdlib-9.0.0
mkdir r && tar xzf $B/rocq-9.1.0.tar.gz -C r --strip-components=1
cd r
echo "== configure"; ./configure -release -prefix "$PW" -libdir 'R:\rocq910\lib\coq'
echo "== runtime + coq-core"; dune build -p rocq-runtime,coq-core -j 2 @install
echo "== dunestrap"; make dunestrap COQ_SPLIT=1 DUNESTRAPOPT="-p rocq-core"
echo "== rocq-core"; dune build -p rocq-core -j 2 @install
echo "== install"; dune install --prefix "$PW" --libdir 'R:\rocq910\lib' rocq-runtime coq-core rocq-core
export PATH="$P/bin:$PATH"
echo "== installed"; which coqc; coqc --version
cd /cygdrive/r/b
tar xzf $B/stdlib-9.0.0.tar.gz
cd stdlib-9.0.0
echo "== stdlib build"; make -j 2
echo "== stdlib install"; make install
echo "== probe"; printf 'From Stdlib Require Import FinFun.\nCheck FinFun.Injective.\n' > /cygdrive/r/b/Probe.v; coqc /cygdrive/r/b/Probe.v
echo ROCQ910_DONE
