# Decision Assurance Engine

組織の方針が、入力変換・判断ルール・提示する説明・承認に正しく反映されているかを検証する参照実装です。必要な条件が成立しない組合せには利用許可を発行せず、利用時にも対象と有効条件を再照合します。

自治体の審査支援を題材にした64状態モデルと、データの外部送信を題材にした32状態モデルを、同じエンジンで扱います。制度・人物・承認はすべて合成です。実際の給付決定、行政処分、外部送信は行いません。

## 使い方

ブラウザで **`index.html`** を開きます。通信・APIキー・サーバー起動は不要です。「正常な判断ルール」「未確認を確認済みに変換」「証明した以上のことを説明」を切り替えると、異なる不適合と反例を確認できます。「利用ゲートを試す」「承認を失効させる」で、供給の許可と停止を操作できます。

Pythonで実行する場合は、Python 3.10以上で次を実行します。基本実行に追加パッケージは不要です。

```bash
python poc.py
python poc.py verify output/results.json
python poc.py test
```

最初のコマンドで、21シナリオの検証記録・集計・許可された供給内容を **`output/results.json` 1ファイル**に保存します。通常の再実行はこのファイルを更新します。個別に保存する場合は `python poc.py run --out output/run-01.json` と指定します。保存は一時ファイルからの置換で行い、シナリオ別フォルダは作りません。

`results.json` は画面の「記録／モデルJSONを読み込む」から再検証・閲覧できます。ブラウザから保存した個別記録もPythonで再検証できます。過去の記録の再検証成功は、現在の利用許可や発行者の認証を意味しません。

## ファイル構成

```text
README.md                    説明・操作・検証範囲
poc.py                       検証本体・合成モデル・テスト・API
index.html                   自己完結型の操作画面
DecisionAssurance.lean       形式モデル・定理・有限モデル照合
lakefile.toml                Leanのビルド設定
lean-toolchain              Leanの固定バージョン
LICENSE                      権利表記
.gitignore                   実行結果・秘密情報等の登録除外
.github/workflows/verify.yml CI設定
```

モデル定義は `poc.py` に集約し、画面用データとLeanの有限表はその定義に照合します。モデルを変更したときは `python poc.py sync` で両者を更新し、テストを再実行します。テスト記録・画像・キャッシュはリポジトリに同梱していません。

## 検証すること

| 段階 | 検査内容 |
|---|---|
| 条件の両立 | 複数主体の必須条件を同時に満たす判断があるか |
| 入力表現 | 同じ機械入力にまとめられたすべての状況に、共通の許容判断があるか |
| 判断仕様 | 可能出力が空でなく、共通の許容判断の範囲に収まるか |
| 検証命題 | 前提が成立する対象で、可能出力が命題の結論を満たすか |
| 提示する説明 | 実際の表示本文を再解析し、条件・判断・根拠の種別が一致するか |
| 共同承認 | 必要な主体の権限・対象・版・提示内容・有効条件が一致するか |

結果は `ALLOW`、`BLOCK`、`UNKNOWN`、`INVALID` を区別します。未確認や未解析を成立と扱いません。安全命題を満たすだけの全件保留、承認の二重計上、別の版への承認、失効済みの許可、同じ操作名で送信内容だけを変更するケースも検査します。

数理的には、入力変換を φ、状況 x の許容判断を H(x) とすると、同一入力 z に対応する全状況の共通部分 C(z) = ∩ H(x) を求めます。表現適合には C(z) の非空性を、仕様適合には可能出力 M(z) の非空性と M(z) ⊆ C(z) を要求します。全許容判断の保存が要求されるモデルでは集合の一致も確認します。

## 別業務への接続

```bash
python poc.py export-model normal --out output/model.json
python poc.py evaluate output/model.json --out output/record.json
python poc.py verify output/record.json
python poc.py serve --port 8765
```

モデルJSONには `domain`、`actions`、主体別の `policies`、`mapping`、`specification`、`proposition`、`explanations`、`governance`、`approvals` を指定します。合成モデルの定義と検証器は業務別に分離されています。Pythonからは `import poc` で `evaluate`、`make_record`、`verify_record`、`use_permit`、`change_impact` を利用できます。

ローカルAPIは `127.0.0.1` に限定され、`GET /health`、`POST /v1/evaluate`、`POST /v1/replay`、`POST /v1/gate` を提供します。POST本文はそれぞれ `{"bundle": ...}`、`{"record": ...}`、`{"bundle": ..., "permit": ..., "state": ..., "action": ...}` です。実システムの操作は実行しません。外部公開用の認証サービスではありません。

## 自動検査

```bash
python poc.py ci                  # Node.jsも使用
python poc.py browser-test        # PlaywrightとChromiumが必要
lake build                       # lean-toolchainに指定したLeanを使用
```

`ci` はPythonテスト、Python／JavaScript照合、CLI・ローカルAPI、画面データとLean有限表の一致を検査します。ブラウザ検査の追加環境は `python -m pip install playwright==1.57.0` と `python -m playwright install chromium` で準備します。CIはブラウザ検査とLeanビルドも別ジョブで実行します。外部AIのAPIキーは不要です。

本構成で実行した検査は、Python **284件**、Python／JavaScript照合 **538項目**、CLI・ローカルAPI **25項目**、ブラウザ操作 **40項目**で、すべて成功しました。21シナリオの期待判定と記録の再検証は一致し、供給内容が生成されるのは利用可能な2シナリオだけです。検査群にはケースの再利用があり、件数の合計を独立した業務ケース数とは扱いません。

確認環境はLinux、Python 3.13.5、Node.js 22.16.0、Chromium 144.0.7559.96です。ブラウザは同一HTMLを `set_content` で読み込み、デスクトップとモバイル幅で確認しました。実行環境の制限により `file://` の直接起動は未確認です。Windows／macOS実機とPython 3.10実機では未確認です。

**LeanコンパイルとGitHub上でのActions実行は未確認です。** Leanの103定理宣言（一般・具体モデル23、有限表80）について、モデルとの対応と未証明プレースホルダー等の字句検査は実行していますが、それを証明成功とは扱いません。`lake build` の成功は別に確認する必要があります。

## 任意のAI実験

```bash
python poc.py api fixture --out output/api-fixture.json
python poc.py api verify output/api-fixture.json
python poc.py api live
```

`fixture` は24ケースの模擬応答を用いるオフライン検査です。原応答・評価・人工改変・人間レビュー候補を1つのJSONに保存します。実APIの観測結果とは区別します。`live` は既定では実行計画の表示だけで、通信しません。

実APIへの接続には `OPENAI_API_KEY` と、利用可能なモデルを明示した `python poc.py api live --execute --model YOUR_MODEL --smoke` が必要です。この操作は課金を伴い得ます。キーは記録に保存せず、自動再試行もしません。本構成の検査では実APIへの接続・課金を行っておらず、実接続の成否は未確認です。AI出力が検査に通っても人間の承認は自動生成せず、運用許可とは扱いません。

## 保証の範囲と権利

検証対象は、明示された方針・語彙・前提・有限領域です。制度解釈、現実の観測、自然言語全般の意味、人間の理解、本人認証や実際の承認権限は証明しません。説明の再解析は定義した限定記法が対象です。Leanモデルの証明が成功しても、Python／JavaScript全体や現実の行政業務の正しさを自動的に証明するものではありません。

共同承認は、定義した必須主体全員の一致を要求するプロファイルです。多数決・委任・部分開示・主体の制御入力による選択可能性は実装対象外です。変更影響の表示は再利用候補を示しますが、検証を省略するキャッシュ機構ではありません。SHA-256は内容の識別・再計算照合に用い、署名や真正性の証明とは区別します。方針・権限・承認を丸ごと作り直す攻撃に備えるには、別途、信頼する登録情報・本人認証・署名・最新状態照会等が必要です。

Copyright © 2026 AI Assurance, Inc. All rights reserved. 公開はオープンソースライセンスや特許実施許諾を意味しません。利用条件は `LICENSE` を参照してください。
