#!/usr/bin/env bash
# Trusted setup: pinned Poly/ML and HOL4, the pinned CakeML submodule, the fixed verifier heap,
# and the operator-published baseline article. No file under candidate/ is read here.
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
  packages=(build-essential git curl libgmp-dev python3 xz-utils)
  if ! dpkg -s "${packages[@]}" >/dev/null 2>&1; then
    sudo=(); [[ "$(id -u)" == 0 ]] || sudo=(sudo)
    ${sudo[@]+"${sudo[@]}"} apt-get update -qq
    ${sudo[@]+"${sudo[@]}"} apt-get install -y --no-install-recommends "${packages[@]}"
  fi
fi

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
  python3 tools/prepare_verifier.py --hol "${tools}/HOL"
fi
python3 -c 'import sys; sys.path.insert(0, "verifier"); import verify; verify.check_trusted()'

# The baseline article (2.8 GB) fits neither git nor a Yukon archive. It is fetched from the
# operator URL in scripts/baseline-article.json and checked against the size and hash pinned there.
baseline_url="$(python3 -c 'import json; print(json.load(open("scripts/baseline-article.json"))["url"] or "")')"
baseline="${tools}/baseline/certificate.art"
if [[ -z "${baseline_url}" ]]; then
  echo 'scripts/baseline-article.json has no URL; the baseline candidate cannot be verified.' >&2
elif ! python3 scripts/baseline.py check "${baseline}" 2>/dev/null; then
  rm -rf "${tools}/baseline"
  mkdir -p "${tools}/baseline"
  headers=()
  if [[ "${baseline_url}" == https://api.github.com/* && -n "${GH_TOKEN:-}" ]]; then
    # Release assets of a non-public repository; curl drops these on the cross-host redirect.
    headers=(-H "Authorization: Bearer ${GH_TOKEN}" -H 'Accept: application/octet-stream')
  fi
  curl --fail --location --retry 3 --proto '=https' ${headers[@]+"${headers[@]}"} \
    -o "${tools}/baseline/download" "${baseline_url}"
  if [[ "$(head -c 6 "${tools}/baseline/download" | od -An -tx1 | tr -d ' \n')" == fd377a585a00 ]]; then
    xz -dc "${tools}/baseline/download" > "${baseline}"
    rm "${tools}/baseline/download"
  else
    mv "${tools}/baseline/download" "${baseline}"
  fi
  python3 scripts/baseline.py check "${baseline}"
fi
