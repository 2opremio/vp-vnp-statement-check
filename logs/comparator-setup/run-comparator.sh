set -u
ulimit -n 65536
cd $HOME/formal-math/vp-vnp
export PATH="$($HOME/.elan/bin/lean --print-prefix)/bin:$HOME/.elan/bin:$PATH"
export COMPARATOR_LANDRUN=$HOME/formal-math-verify-scratch/tools/bin/landrun-passthrough
export COMPARATOR_LEAN4EXPORT=$HOME/formal-math-verify-scratch/tools/lean4export/.lake/build/bin/lean4export
export COMPARATOR_NANODA=$HOME/formal-math-verify-scratch/tools/nanoda/target/release/nanoda_bin
export LEAN_ABORT_ON_PANIC=1
echo "lean: $(which lean) $(lean --version)"
/usr/bin/time -l nice -n 15 lake env $HOME/formal-math-verify-scratch/tools/comparator/.lake/build/bin/comparator $HOME/formal-math-verify-scratch/comparator-checked.json
echo COMPARATOR_EXIT=$?
