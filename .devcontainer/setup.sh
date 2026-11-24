#!/usr/bin/env bash
set -euo pipefail

root=$(git rev-parse --show-toplevel)
proof_dir="$(dirname "$root")/pnp-proof"
upstream_url=https://github.com/brilliant-hq/pequalnp-proofs.git

cd "$root"
if ! git config --get remote.upstream.url >/dev/null; then
  git remote add upstream "$upstream_url"
fi
case "$(git config --get remote.upstream.url)" in
  "$upstream_url"|"${upstream_url%.git}"|git@github.com:brilliant-hq/pequalnp-proofs.git) ;;
  *) echo "Check the upstream remote: it must point to brilliant-hq/pequalnp-proofs." >&2; exit 1 ;;
esac
git fetch --no-tags upstream refs/heads/main:refs/remotes/upstream/main

if [[ ! -e "$proof_dir" && ! -L "$proof_dir" ]]; then
  git worktree add --detach "$proof_dir" upstream/main
else
  common_dir=$(git rev-parse --path-format=absolute --git-common-dir)
  if [[ "$(git -C "$proof_dir" rev-parse --show-toplevel 2>/dev/null)" != "$proof_dir" ||
        "$(git -C "$proof_dir" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)" != "$common_dir" ]]; then
    echo "Choose another location for the existing $proof_dir before starting setup." >&2
    exit 1
  fi
fi

export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
if ! command -v elan >/dev/null; then
  installer=$(mktemp)
  trap 'rm -f "$installer"' EXIT
  curl --proto '=https' --tlsv1.2 -fsSL https://elan.lean-lang.org/elan-init.sh -o "$installer"
  sh "$installer" -y --default-toolchain none --no-modify-path
fi
if ! command -v codex >/dev/null; then
  npm install --global --prefix "$HOME/.local" @openai/codex
fi

cd "$proof_dir"
bash tools/pnp.sh setup
(cd lean && lake build PEqualNP.Defs.Base)
codex --version
printf 'Proof workspace ready: %s\n' "$proof_dir"

# Make a successful build visible to the owner outside the running Codespace.
if [[ ${CODESPACES:-} == true && ${GITHUB_REPOSITORY:-} == miz0139m1023-hue/pequalnp-proofs ]]; then
  config_commit=$(git -C "$root" rev-parse HEAD)
  gh api --method POST "repos/$GITHUB_REPOSITORY/statuses/$config_commit" \
    -f state=success -f context=codespaces/lean-setup \
    -f description="Built PEqualNP.Defs.Base and verified the Codex CLI in GitHub Codespaces" \
    --silent || printf 'GitHub could not display the build status. The local build passed.\n' >&2
fi
