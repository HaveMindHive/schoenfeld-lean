#!/bin/sh
# Compile one S1 module (e.g. B, A) to build/SchoenfeldS1/<M>.olean, against the port's oleans and the RH repo.
# Delivered files are S1<M>_v1.0_11-27-2026.lean; src/SchoenfeldS1/<M>.lean are copies (made here) giving the module names SchoenfeldS1.<M>.
D=$(cd "$(dirname "$0")/.." && pwd)
P=${PORT_DIR:?set PORT_DIR to the built S2 port}
R=${RH_REPO:?set RH_REPO to a built riemann-hypothesis clone}
LP="$D/build:$P/build:$R/.lake/build/lib/lean"
for p in $R/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
LP="$LP:$HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1/lib/lean"
M="$1"
cp "$D/S1${M}_v1.0_11-27-2026.lean" "$D/src/SchoenfeldS1/$M.lean"
cd "$R" && LEAN_PATH="$LP" $HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1/bin/lean -j2 --tstack=400000 \
  --root="$D/src" -o "$D/build/SchoenfeldS1/$M.olean" -i "$D/build/SchoenfeldS1/$M.ilean" "$D/src/SchoenfeldS1/$M.lean"
