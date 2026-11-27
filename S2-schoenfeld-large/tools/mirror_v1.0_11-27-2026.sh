#!/bin/sh
# Mirror the port folder (without build/ and scratch/) to OneDrive.
rsync -a --delete --exclude build/ --exclude scratch/ "$HOME/HaveMindHive/schoenfeld-port_v1.0_11-27-2026/" \
  "$HOME/Library/CloudStorage/OneDrive-rkfleming/HaveMindHive/schoenfeld-port_v1.0_11-27-2026/"
