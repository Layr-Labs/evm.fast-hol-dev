#!/usr/bin/env bash
# Trusted setup: pinned Poly/ML, the standard and tracing HOL4 trees, the pinned CakeML submodule,
# the baseline theories and the fixed verifier heap. No file under candidate/ is read here.
set -euo pipefail
cd "$(dirname "$0")/.."
tools="${PWD}/work"
pin() { python3 -c 'import json, sys; print(json.load(open("provenance.json"))[sys.argv[1]])' "$1"; }
# The tested verifier ran Poly/ML "5.9.2 Release (Git version v5.9.2-311-gd615dad7)" (README.md),
# HOL4 tested_hol with the standard kernel, and CakeML at the submodule pin (verification.json).
polyml_rev=d615dad7975f48d83c7e1873a9beeab1fb71c077
polyml_describe=v5.9.2-311-gd615dad7
hol_rev="$(pin tested_hol)"
cakeml_rev="$(pin cakeml)"
jobs="$(getconf _NPROCESSORS_ONLN)"
export PATH="${tools}/polyml/bin:${PATH}"
export LD_LIBRARY_PATH="${tools}/polyml/lib${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
mkdir -p "${tools}"

if command -v apt-get >/dev/null 2>&1; then
  packages=(build-essential git curl libgmp-dev python3 xz-utils bubblewrap)
  if ! dpkg -s "${packages[@]}" >/dev/null 2>&1; then
    sudo=(); [[ "$(id -u)" == 0 ]] || sudo=(sudo)
    ${sudo[@]+"${sudo[@]}"} apt-get update -qq
    ${sudo[@]+"${sudo[@]}"} apt-get install -y --no-install-recommends "${packages[@]}"
  fi
fi
command -v bwrap >/dev/null || { echo "The verifier runs proof sources in Bubblewrap: install bwrap" >&2; exit 1; }

if [[ "$(cat "${tools}/polyml.rev" 2>/dev/null)" != "${polyml_rev}" ]]; then
  rm -rf "${tools}/polyml" "${tools}/polyml.rev" "${tools}/polyml-src"
  # Poly/ML's configure embeds `git describe --tags --always`: keep tags and history, not blobs.
  git clone -q --filter=blob:none --no-checkout https://github.com/polyml/polyml.git "${tools}/polyml-src"
  git -C "${tools}/polyml-src" checkout -q --detach "${polyml_rev}"
  test "$(git -C "${tools}/polyml-src" describe --tags --always)" = "${polyml_describe}"
  (cd "${tools}/polyml-src" && ./configure --prefix="${tools}/polyml" --with-gmp && make -j"${jobs}" && make install)
  echo "${polyml_rev}" > "${tools}/polyml.rev"
fi
poly -v </dev/null | grep -F "Git version ${polyml_describe}"

if [[ "$(cat "${tools}/HOL.rev" 2>/dev/null)" != "${hol_rev}" ]]; then
  rm -rf "${tools}/HOL" "${tools}/HOL.rev"
  git init -q "${tools}/HOL"
  git -C "${tools}/HOL" fetch -q --depth 1 https://github.com/HOL-Theorem-Prover/HOL.git "${hol_rev}"
  git -C "${tools}/HOL" checkout -q --detach FETCH_HEAD
  (cd "${tools}/HOL" && poly --script tools/smart-configure.sml && bin/build --stdknl -j "${jobs}")
  echo "${hol_rev}" > "${tools}/HOL.rev"
fi
test "$(git -C "${tools}/HOL" rev-parse HEAD)" = "${hol_rev}"

# The author-side tracing kernel that exports proof sources to an article: a worktree of the
# standard tree at the same pin with tools/exporter-hol.patch applied.
export_stamp="${hol_rev} $(sha256sum tools/exporter-hol.patch | cut -d' ' -f1)"
if [[ "$(cat "${tools}/HOL-export.rev" 2>/dev/null)" != "${export_stamp}" ]] \
    || ! git -C "${tools}/HOL-export" rev-parse HEAD >/dev/null 2>&1; then
  rm -rf "${tools}/HOL-export" "${tools}/HOL-export.rev"
  git -C "${tools}/HOL" worktree prune
  python3 tools/prepare_exporter.py --hol-source "${tools}/HOL" --output "${tools}/HOL-export" -j "${jobs}"
  echo "${export_stamp}" > "${tools}/HOL-export.rev"
fi
test "$(git -C "${tools}/HOL-export" rev-parse HEAD)" = "${hol_rev}"

# Author stages run in verify_source.py's Bubblewrap sandbox: a cleared environment
# (PATH=/usr/local/bin:/usr/bin:/bin, no LD_LIBRARY_PATH) with /home, /opt, /tmp and /var masked.
# Check that Python and both trees start there before spending hours on a verification.
python3 - "${tools}/HOL" "${tools}/HOL-export" <<'PY'
from pathlib import Path
import shutil, sys, tempfile
sys.path.insert(0, 'verifier')
import verify_source
standard, author = (Path(path).resolve() for path in sys.argv[1:3])
work = Path(tempfile.mkdtemp(prefix='sandbox-smoke-', dir='work')).resolve()
try:
    for name in ('input', 'experiments', 'tools', 'home'):
        (work/name).mkdir()
    (work/'tools/allocationHintLib.sml').write_text('')
    (work/'smoke.sml').write_text('val _ = print "SANDBOX_OK\\n";\n')
    checks = [[sys.executable, '-c', 'print("SANDBOX_OK")']] + [
        [hol/'bin/hol', 'run', hol/'sigobj/holmake_not_interactive.uo', work/'smoke.sml'] for hol in (standard, author)]
    for command in checks:
        with (work/'smoke.log').open('wb') as log:
            result = verify_source.author_sandbox(work, standard, author, command, timeout=600, memory_gib=64, stdout=log)
        output = (work/'smoke.log').read_text(errors='replace')
        if 'SANDBOX_OK' not in output:
            raise SystemExit(f'{command[0]} does not run in the verifier sandbox (exit {result.returncode}):\n{output}')
finally:
    shutil.rmtree(work)
PY

if [[ ! -e cakeml/.git ]] || [[ "$(git -C cakeml rev-parse HEAD)" != "${cakeml_rev}" ]]; then
  git submodule update --init --depth 1 cakeml
fi
test "$(git -C cakeml rev-parse HEAD)" = "${cakeml_rev}"

# verify.py would prepare a missing or stale heap itself; do it here, before any candidate.
if ! python3 - "${tools}/HOL" 2>/dev/null <<'PY'
import json, sys
from pathlib import Path
sys.path.insert(0, 'verifier')
import verify
info = json.loads(Path('.build/verifier.json').read_text())
ok = (info['hol'] == str(Path(sys.argv[1]).resolve())
      and info['hol_revision'] == json.loads(Path('provenance.json').read_text())['tested_hol']
      and info['manifest_sha256'] == verify.file_digest(Path('verifier/trusted-files.json'))
      and info['heap_sha256'] == verify.file_digest(Path('.build/verifier.heap')))
raise SystemExit(0 if ok else 1)
PY
then
  # The verifier rebuilds candidate theories in a sandbox that mounts HOL read-only, so every HOL
  # example theory they load must already be built: build the baseline once, as README.md's
  # operator steps do, then the heap.
  python3 tools/build.py --hol "${tools}/HOL" --jobs 3 initBaselineCertificateTheory initProofLibraryTheory
  python3 tools/prepare_verifier.py --hol "${tools}/HOL"
fi
python3 -c 'import sys; sys.path.insert(0, "verifier"); import verify; verify.check_trusted()'
