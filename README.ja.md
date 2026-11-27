# axiom-fuzzer

axiom-fuzzer は一階の理論の矛盾を探す道具です。理論は、有限個の公理、インスタンスを自動で合成する
公理図式、または再帰的に列挙される任意の公理集合で与えます。探索が反駁を見つけると、Rocq の証明から
抽出した検査器が元の公理からその反駁を検査し直し、通ったときだけ `UNSAT` と答えます。それ以外は
`UNKNOWN` です。`SAT` とは答えません。

例えば素朴集合論（無制限の内包図式）では、条件式の候補を列挙・合成して `not (x in x)` という
インスタンスを見つけ、反駁します。この条件式も Russell の証明も探索器に組み込んではいません。

この文書は 0.1.0 の [英語の README](README.md) の日本語版で、内容が食い違うときは英語版が正です。詳しい文書は英語で書いています。

**位置付け。** 研究用の試作で、版は 0.1.0 です。競争力のある自動定理証明器ではありません。試した
TPTP の問題では、E や Vampire のほうが多くを解きます。この道具の要点は、報告するすべての反駁に、
Rocq の証明まで自分で検査し直せる証明書が付くことです。0.x の間は、コマンドライン、証明書と
checkpoint の形式、CSV の列が移行手段なしに変わることがあります。

このプロジェクトは AI の支援を受けて開発しました。

## `UNSAT` の意味

- `UNSAT` は、反駁の証明書を見つけ、`Kernel.check` がそれを受理したことを意味します。
  `Kernel.check` の最終判定は、[rocq/](rocq/) の Rocq の証明から抽出した検査器が行います。Rocq の定理
  `check_sound`、`avatar_check_sound`、`Reference.Certificate.Kernel.check_sound` により、受理は
  「この道具が読み込んだ理論」が空でない領域上のモデルを持たないことを意味します。
- `UNKNOWN` は何も主張しません。充足可能性や無矛盾性の証拠ではなく、難しさの証拠でもありません。
- 証明書は自分で検査し直せます。`axiom-replay` は別のプロセスで検査器をもう一度動かし、
  `axiom-replay --rocq` は反駁を Rocq 自身が検査するファイルとして出力します。
  [scripts/recheck.sh](scripts/recheck.sh) はその両方を行います。
- 信頼する対象として残るもの：Rocq の kernel と Stdlib、構文・意味論・組み込み図式の Rocq での定義、
  メタ理論の古典的な前提、入力の側（TPTP の読み込み、組み込み理論の manifest、自分で登録した図式の
  `check` callback）、そして Rocq の経路を使わない場合は抽出と OCaml のコンパイラ・ランタイム。
- どの証明も扱わないもの：ヒューリスティック探索の完全性、`UNKNOWN` について言えること、性能。

信頼モデルの全体は [docs/guarantees.md](docs/guarantees.md) にあります。

## インストール

| 部品 | 版 | 用途 |
| --- | --- | --- |
| OCaml | 5.2〜5.5（5.2.1、5.4.1、5.5.2 で確認） | すべて |
| Dune | 3.17 以上（3.17.2、3.24.2、3.25.0 で確認） | すべて |
| C コンパイラ | どれでも（Xcode Command Line Tools、gcc、clang） | 小さな C stub |
| Python | 3.12 以上 | テストとベンチマークのスクリプト |
| Rocq | 9.3.0 と Stdlib（`rocq-core` 9.3.0 と `rocq-stdlib` 9.2.0） | 証明：`dune build @rocq` と Rocq での再検査 |
| OCaml 5.5.2 + flambda | 任意 | 計測に使う release ビルド（`make release`） |

ライブラリの依存は OCaml の標準ライブラリと `unix` だけです。開発した環境は arm64 の macOS です。
Linux にも対応しています（ubuntu-24.04 のコンテナでテストが通り、CI は Linux と macOS でビルドと
テストを行います）。Windows には対応していません。プロセス版の portfolio が `fork`・process group・
POSIX の signal を使うためです。

新しく clone した状態から opam で準備する場合：

```sh
git clone https://github.com/t3tra-dev/axiom-fuzzer.git
cd axiom-fuzzer
opam switch create . 5.5.2 --no-install   # OCaml 5.2〜5.5 ならどれでもよい
eval $(opam env)
opam install . --deps-only --with-test
dune build
dune runtest
```

Rocq、flambda のビルド、エディタの設定、困ったときの対処は
[docs/installation.md](docs/installation.md) にあります。

## 使ってみる

素朴集合論を反駁して証明書を保存し、別のプロセスで検査し直します。

```sh
dune exec axiom-fuzz -- --theory naive --certificate russell.cert
dune exec axiom-replay -- --theory naive russell.cert
```

出力には、探索が試す図式のインスタンス（`[N] ...`）、短い要約、証明の節（`#N ...`）が並びます。

```text
[0] comprehension_0: x in x
[1] guided comprehension_1: not (x in x)
Theory: naive
Result: UNSAT
Reason: refutation verified
Used axioms: comprehension_1
Proof clauses: 5
#2  (v0 in v0) | (v0 in sk_1_0)
#3  (sk_1_0 in sk_1_0)
#5  ~(v0 in v0) | ~(v0 in sk_1_0)
#6  ~(sk_1_0 in sk_1_0)
#7  BOTTOM
Certificate: russell.cert
```

`--quiet` を付けると要約の行だけになり、`--stats` を付けると worker・probe lane・基準列挙の計数が
加わります。

replay は `VERIFIED: theory=naive axioms=1 steps=5 ...` と出力して終了コード 0 で終わります。別の
理論、例えば `--theory zf` を渡すと `REJECTED: theory manifest mismatch` と出力して終了コード 1 で
終わります。

TPTP の問題も同じように扱います。問題のファイルも検査の一部なので、replay にも渡します。

```sh
dune exec axiom-fuzz -- --problem theories/examples/equality.p --certificate equality.cert
dune exec axiom-replay -- --problem theories/examples/equality.p equality.cert
```

Stdlib 付きの Rocq 9.3.0 があれば、証明書を Rocq の証明まで検査し直せます（初回は `rocq/` の
Rocq の証明もコンパイルします。`PATH` の先頭にない `rocq` を使うときは `ROCQ=/path/to/rocq` を
指定します）。

```sh
scripts/recheck.sh --theory naive russell.cert
```

`zf` のように無矛盾と考えられている理論は、時間の上限で `UNKNOWN` になります。

```sh
dune exec axiom-fuzz -- --theory zf --seconds 2
```

## コマンドラインの道具

| 実行ファイル | 役割 |
| --- | --- |
| `axiom-fuzz` | 組み込みの理論（`--theory`）か TPTP の問題（`--problem`）を探索し、証明書・TSTP・Rocq・FOF/CNF の出力と CSV の指標を書く |
| `axiom-replay` | 指定した理論か問題に対して証明書を検査し直し、Rocq のソースとして出力する |
| `axiom-minimize` | 証明書を小さくし（公理を減らす、図式の条件式を縮める、自然演繹を短くする）、結果を検査し直す |
| `axiom-mutate` | 理論の公理の変異を作り、それぞれを探索する |
| `axiom-reference` | Rocq で証明した、自然演繹の証明書の基準列挙を段階ごとに実行する |

`axiom-fuzz` には探索戦略を選ぶオプションがありません。戦略は `--workers` だけで決まります。
どの実行ファイルも、使い方・入力・内部のエラーでは標準エラーに文言を出して終了コード 2 で終わり、
`UNKNOWN` で終わった実行は終了コード 0、`axiom-replay` が証明書を拒否したときは終了コード 1 です。
どの実行ファイルも `--version` を受け付けます。`AXIOM_*` という環境変数は評価専用の上書きで、
設定されていると `axiom-fuzz` は標準エラーに `Note: evaluation overrides active: ...` と出力します。
[docs/cli.md](docs/cli.md) と [docs/evaluation.md](docs/evaluation.md) を参照してください。

## 理論と公理図式

| `--theory` | 内容 | 既定の設定での結果 |
| --- | --- | --- |
| `naive` | 無制限の内包図式 | `UNSAT` |
| `separation-universal` | 分出図式と普遍集合 | `UNSAT` |
| `foundation-self` | 対・正則性と自分自身を要素に持つ集合 | `UNSAT` |
| `mutated-separation` | 分出図式から範囲の集合を除いたもの（意図的な変異） | `UNSAT` |
| `separation` | 分出図式だけ | `UNKNOWN` |
| `zf` | 外延性・空集合・対・和・冪集合・無限・正則性と、分出・置換の図式（選択公理なし） | `UNKNOWN` |

`--problem` は型のない一階の TPTP を読みます。`fof` と `cnf` の式だけで、`include`、TFF、THF、
算術は使えず、予想は否定した形（`negated_conjecture`）で与えます。OCaml のライブラリを使うと、
固定公理、独自のパラメータ型と検査器を持つ登録図式、定義、再帰的に列挙する公理集合からも理論を
作れます。その入口は不安定な 0.x の API です。[docs/theories.md](docs/theories.md) を参照してください。

## 限界

- 探索はヒューリスティックです。有限の実行は無矛盾性について何も示しません。いつかすべての反駁を
  見つけると証明した基準列挙にも、実用的な時間の上限はありません。
- メモリ予算は worker ごとの協調的な目標で、エンジン自身の単位で数えます。常駐メモリの厳密な上限
  ではなく、基準列挙は対象外です。
- 32 MiB を超える証明書も書き出しますが、`axiom-replay` では読めません。
- 自然演繹の証明書には TSTP の出力がなく、外部の証明器の証明は取り込めません。
- 証明書と checkpoint は版を持ちません。別の版はそれらを拒否するので、探索をやり直して作り直して
  ください。

## 文書

| 文書 | 内容 |
| --- | --- |
| [docs/installation.md](docs/installation.md) | 必要なもの、対応環境、Rocq と flambda のビルド、エディタ、困ったとき |
| [docs/cli.md](docs/cli.md) | 各実行ファイルのオプション・出力・終了コード |
| [docs/guarantees.md](docs/guarantees.md) | 信頼モデル：何を証明したか、何を信頼するか、どう検査し直すか |
| [docs/theories.md](docs/theories.md) | 組み込みの理論と図式、TPTP の範囲、OCaml ライブラリの API |
| [docs/formats.md](docs/formats.md) | 証明書・TSTP・Rocq 出力・checkpoint・CSV の形式 |
| [docs/architecture.md](docs/architecture.md) | 探索・検査器・プロセス版 portfolio の構成 |
| [docs/evaluation.md](docs/evaluation.md) | 評価専用の戦略と `AXIOM_*` スイッチ |
| [docs/benchmarks.md](docs/benchmarks.md) | ベンチマークと計測の方法 |
| [docs/preregistration.md](docs/preregistration.md) | held-out の TPTP v10.0.0 分割と、次の評価の規則 |
| [docs/development.md](docs/development.md) | ビルド、テスト、Rocq の再抽出、探索が同じであることの確認 |
| [CONTRIBUTING.md](CONTRIBUTING.md) | 誤った `UNSAT` の報告の仕方と、変更の規則 |
| [CHANGELOG.md](CHANGELOG.md) | 変更履歴 |

## 引用

[CITATION.cff](CITATION.cff) のメタデータで引用してください。

> t3tra. *axiom-fuzzer*, version 0.1.0. 2026.

## ライセンス

このプロジェクト自身のコードと文書は [MIT ライセンス](LICENSE)です。Rocq から抽出した 14 個の OCaml ファイル
（`lib/proof/{kernel,natural,avatar,rocq}_checker.ml(i)`、`lib/proof/{wire_normalizer,wire_checker}.ml(i)`、
`lib/syntax/source_checker.ml(i)`）は Rocq Stdlib のコードの翻訳を含むので LGPL-2.1-only です。
`benchmarks/problems/tptp/` と `tests/fixtures/tptp/` の TPTP の問題と公理のファイル（改変せずに再配布）は
TPTP の利用条件に従います。測定データとコーパスの manifest（`benchmarks/checker.csv`、`benchmarks/corpora/`）は
CC-BY-4.0 です。
[REUSE.toml](REUSE.toml)、[LICENSES/](LICENSES/)、[THIRD-PARTY.md](THIRD-PARTY.md) がパスごとの
ライセンスを示します。

## 謝辞

移植したヒューリスティックは E prover 3.5.9 の戦略と Vampire 5.1.0 の schedule のスライスを
OCaml で実装し直したものです。どちらの証明器も同梱せず、起動もしません。出典は
[THIRD-PARTY.md](THIRD-PARTY.md) にあります。ベンチマークの問題は TPTP Problem Library から取りました。
証明は Rocq Prover で検査しています。

---

この文書のコマンド、新しい clone からの opam での準備、理論の表の結果は、0.1.0 を使って arm64 の
macOS で実行して確かめました。
