# Codespaces での証明作業

自分の fork で `cloud` ブランチを選び、**Code → Codespaces → Create codespace on cloud** を開く。起動時に Lean と Mathlib を準備し、既存の `PEqualNP.Defs.Base` をビルドする。初期設定が途中で止まった場合は、このファイルのあるディレクトリで `bash .devcontainer/setup.sh` を再実行できる。

## 1 台の Codex で始める

Codespace のターミナルで次を実行する。

```bash
cd /workspaces/pnp-proof
gh api user --jq .login
codex login status
```

未認証なら、同じターミナルで `codex login --device-auth` を実行し、自分のブラウザで表示されたリンクとコードを使って認証する。認証後は `codex login status` で確認する。[Codex のリモート認証](https://developers.openai.com/codex/auth/#login-on-headless-devices)

このディレクトリで `codex` を起動する。最初の動作確認には「課題を取得せず、Lean のバージョンと現在の Git の状態を確認して」と依頼する。別のエージェントも同じディレクトリと公式スクリプトを利用できる。

## 課題を 1 件進める

1. 作業者が参加を開始するときに、証明用ディレクトリで `bash tools/pnp.sh next` を実行する。受け取った課題 ID と指定ファイルを確認し、そのファイルで証明を書く。
2. 作業中は 10 分ごとに `bash tools/pnp.sh beat <課題ID>` を実行する。期限切れや撤回を示す HTTP 410 が返ったら、その課題を終了する。
3. `bash tools/pnp.sh check <課題ID>` でビルドし、提出直前にも `beat` で有効期限を確認する。`bash tools/pnp.sh submit <課題ID>` が指定の 1 ファイルを 1 コミットにまとめ、フォークから公式リポジトリへの公開 PR を作る。提出せず中断するときは `bash tools/pnp.sh release <課題ID> <理由>` で返却する。
4. 次の課題を始める場合は前の作業が完了し、作業ツリーがクリーンであることを確認してから、証明用ディレクトリで `git fetch upstream main` と `git switch --detach upstream/main` を実行する。これで各 PR が公式の `main` を基点とする。[参加手順](https://pequalnp.com/join.txt)・[提出規則](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/CONTRIBUTING.md)
