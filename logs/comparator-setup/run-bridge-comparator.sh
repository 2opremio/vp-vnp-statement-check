# Run from this repository after `lake build`, with the tools of tools.txt built under $T.
set -u
ulimit -n 65536
export PATH="$($HOME/.elan/bin/lean --print-prefix)/bin:$HOME/.elan/bin:$PATH"
T=$HOME/formal-math-verify-scratch/tools
export COMPARATOR_LANDRUN=$T/bin/landrun-passthrough
export COMPARATOR_LEAN4EXPORT=$T/lean4export/.lake/build/bin/lean4export
export COMPARATOR_NANODA=$T/nanoda/target/release/nanoda_bin
export LEAN_ABORT_ON_PANIC=1
/usr/bin/time nice -n 15 lake env $T/comparator/.lake/build/bin/comparator comparator.json
echo COMPARATOR_EXIT=$?
