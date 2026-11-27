#!/bin/sh
# Check one Lean file against build/ (S1 oleans), the port's oleans and the built RH repo.
D=$(cd "$(dirname "$0")/.." && pwd)
P=${PORT_DIR:?set PORT_DIR to the built S2 port}
R=${RH_REPO:?set RH_REPO to a built riemann-hypothesis clone}
LP="$D/build:$P/build:$R/.lake/build/lib/lean"
for p in $R/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
LP="$LP:$HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1/lib/lean"
LEAN_PATH="$LP" exec $HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1/bin/lean -j2 --tstack=400000 "$@"
