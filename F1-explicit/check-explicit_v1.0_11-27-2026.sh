#!/bin/sh
# Kernel-check ExplicitRH against the built RH repo (uses its oleans; writes nothing there).
# Step 1: compile the VonKoch file (module name WallsMeetRHVonKoch) to an olean in ./build.
# Step 2: check the explicit file with that olean on the LEAN_PATH.
W="$HOME/HaveMindHive/walls-meet-rh_v1.0_11-27-2026"
B="$W/build"
cd "$HOME/Library/CloudStorage/OneDrive-rkfleming/HaveMindHive/riemann-hypothesis-community_v1.0_11-27-2026/repo" || exit 1
mkdir -p "$B"
cp "$W/WallsMeetRHVonKoch_v1.0_11-27-2026.lean" "$B/WallsMeetRHVonKoch.lean"
lake env lean --root="$B" -o "$B/WallsMeetRHVonKoch.olean" -i "$B/WallsMeetRHVonKoch.ilean" "$B/WallsMeetRHVonKoch.lean" > "$B/vonkoch-check.txt" 2>&1 || { echo "VonKoch failed"; cat "$B/vonkoch-check.txt"; exit 1; }
LEAN_PATH="$B:$(lake env printenv LEAN_PATH)" lake env lean "$W/ExplicitRH_v1.0_11-27-2026.lean"
