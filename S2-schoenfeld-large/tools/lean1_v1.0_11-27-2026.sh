#!/bin/sh
# Check one Lean file against the ported oleans in build/ and a built clone of
# leanprover-community/riemann-hypothesis (Lean v4.37.0-rc1).
# Usage: RH_REPO=/path/to/riemann-hypothesis sh tools/lean1_v1.0_11-27-2026.sh File.lean
HERE="$(cd "$(dirname "$0")/.." && pwd)"
RH="${RH_REPO:?set RH_REPO to a built riemann-hypothesis clone}"
TOOLCHAIN="${LEAN_TOOLCHAIN_DIR:-$HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1}"
LP="$HERE/build:$RH/.lake/build/lib/lean"
for p in "$RH"/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
LP="$LP:$TOOLCHAIN/lib/lean"
LEAN_PATH="$LP" exec "$TOOLCHAIN/bin/lean" -j2 --tstack=400000 "$@"
