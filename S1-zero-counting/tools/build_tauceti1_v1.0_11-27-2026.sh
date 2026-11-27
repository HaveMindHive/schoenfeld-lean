#!/bin/sh
# Compile one Tau Ceti module that the RH repo's build does not include (e.g. Argument.lean's closure)
# from the read-only Tau Ceti source into our local build/ (nothing is written to the RH repo).
D=$(cd "$(dirname "$0")/.." && pwd)
P=${PORT_DIR:?set PORT_DIR to the built S2 port}
R=${RH_REPO:?set RH_REPO to a built riemann-hypothesis clone}
T=$R/.lake/packages/TauCeti
LP="$D/build:$P/build:$R/.lake/build/lib/lean"
for p in $R/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
LP="$LP:$HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1/lib/lean"
M="$1"; REL=$(echo "$M" | tr . /)
mkdir -p "$D/build/$(dirname $REL)"
cd "$R" && LEAN_PATH="$LP" $HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1/bin/lean -j2 --tstack=400000 \
  --root="$T" -o "$D/build/$REL.olean" -i "$D/build/$REL.ilean" "$T/$REL.lean"
