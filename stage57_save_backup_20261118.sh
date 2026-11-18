#!/usr/bin/env bash
set -Eeuo pipefail
cd /workspaces/coq-axiom-test
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
OUT="stage57_backup_${STAMP}.zip"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/metadata" "$TMP/source_snapshot"

# Keep existing history and uncommitted sources intact: no reset/clean/rebase.
git status --porcelain=v1 > "$TMP/metadata/git_status_before.txt"
git rev-parse HEAD > "$TMP/metadata/head_before.txt"
git remote -v > "$TMP/metadata/remotes.txt"
coqc --version > "$TMP/metadata/coq_version.txt" 2>&1 || true

# Stage only research source and audit artifacts, not executable secrets or compiled artifacts.
# All current version-controlled modifications are included if already tracked.
# First verify the previously reported T3 closure before committing.
{
  coqc stage57_T3_injective_v1.v &&
  coqc stage57_T3_derivation_unique_20261118.v &&
  printf 'Require Import stage57_T3_derivation_unique_20261118.\nPrint Assumptions stage57_T3_derivation_unique_20261118.T3_derivation_unique.\n' | coqtop -quiet &&
  coqchk stage57_T3_derivation_unique_20261118
} > "$TMP/metadata/T3_recheck.log" 2>&1 && CHECK=PASS || CHECK=FAIL
printf '%s\n' "$CHECK" > "$TMP/metadata/T3_recheck_status.txt"
if [ "$CHECK" != PASS ]; then
  echo 'T3_RECHECK_FAILED: not committing/pushing; check existing sources and proof status.'
fi

find . -maxdepth 1 -type f \( -name 'stage57_*.v' -o -name 'stage57_*.md' -o -name 'stage57_*.txt' -o -name 'stage57_*.csv' \) -print0 | xargs -0 -r git add --
# Ensure the audited T3 files are included (both should exist).
for f in stage57_T3_injective_v1.v stage57_T3_derivation_unique_20261118.v; do
  test -f "$f" || { echo "MISSING required proof: $f"; exit 1; }
  git add -- "$f"
done

# Save a git commit, without replacing or rewriting existing history.
if [ "$CHECK" = PASS ] && ! git diff --cached --quiet; then
  git commit -m "Stage57: preserve verified T3 proofs and audit artifacts"
fi

git rev-parse HEAD > "$TMP/metadata/head_saved.txt"
git status --porcelain=v1 > "$TMP/metadata/git_status_after_commit.txt"

# Push failure does not destroy the local backup. It is explicitly reported.
PUSH_STATUS=0
if [ "$CHECK" = PASS ] && [ "$(git branch --show-current)" = main ] && git remote get-url origin >/dev/null 2>&1; then
  git push origin HEAD:main > "$TMP/metadata/push_log.txt" 2>&1 || PUSH_STATUS=$?
else
  printf 'Push skipped: no origin, non-main branch, or failed T3 check\n' > "$TMP/metadata/push_log.txt"
  PUSH_STATUS=99
fi
printf '%s\n' "$PUSH_STATUS" > "$TMP/metadata/push_exit_code.txt"

# Full committed repository history, plus the current research sources, independently.
git bundle create "$TMP/stage57_repository_history.bundle" --all
# Export tracked files at the saved commit, excluding .git internal files.
git archive HEAD | tar -xf - -C "$TMP/source_snapshot"
# Capture extra untracked Stage57 source/audit files not necessarily committed.
mkdir -p "$TMP/untracked_stage57"
while IFS= read -r -d '' f; do
  case "$f" in
    stage57_*.v|stage57_*.md|stage57_*.txt|stage57_*.csv)
      cp -- "$f" "$TMP/untracked_stage57/";;
  esac
done < <(git ls-files --others --exclude-standard -z)

(cd "$TMP" && find source_snapshot untracked_stage57 -type f -print0 | sort -z | xargs -0 -r sha256sum > metadata/source_sha256.txt)
printf 'Stage 57 backup. Whole-system closure NOT claimed.\nT3 local derivation uniqueness: check metadata/T3_recheck_status.txt.\nGitHub push: 0 means success; see metadata/push_log.txt.\n' > "$TMP/README.txt"
python3 - "$TMP" "$OUT" <<'PY'
from pathlib import Path
import sys,zipfile
src=Path(sys.argv[1]); dest=Path(sys.argv[2])
with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED,compresslevel=7) as z:
    for p in sorted(src.rglob('*')):
        if p.is_file(): z.write(p,p.relative_to(src))
with zipfile.ZipFile(dest) as z:
    bad=z.testzip()
    if bad: raise SystemExit('ZIP integrity failure: '+bad)
print('BACKUP_OK:',dest)
print('SIZE_BYTES:',dest.stat().st_size)
PY
sha256sum "$OUT"
echo "GITHUB_PUSH_EXIT_CODE=$PUSH_STATUS"
echo "T3_RECHECK=$CHECK"
echo "BACKUP_PATH=$(pwd)/$OUT"
