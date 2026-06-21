# Houdini Scene To Text

Houdini 21 の現在の HIP シーンを、LLM に渡しやすい Markdown と、後から検索しやすい JSON に書き出す Python スクリプトです。

## できること

- `/` 以下、または指定ルート以下の全ノードを再帰的に収集
- SOP/OBJ/LOP/DOP/CHOP/COP/VOP/TOP/ROP/Subnet/HDA を同じ形式で記録
- ノードの親子構造、タイプ、カテゴリ、フラグ、コメント、ユーザーデータを記録
- 何が何に接続されているかを、入力/出力ポート名・番号つきで記録
- 全パラメータの種類、ラベル、テンプレート情報、値、式、キーフレーム、メニュー項目などを記録
- Wrangle の `snippet`、Python SOP、Callback、VEX/VOP/HScript らしき文字列をコードブロックとして抽出
- VOP ネットワーク、サブネット、TOP、ROP も子ノードと接続としてそのままテキスト化
- 明示指定した場合だけ HDA の PythonModule / VEX / DialogScript などのセクションも記録
- 明示指定した場合だけ SOP ジオメトリを cook し、primitive / detail(global) アトリビュートを優先して記録

## Houdini 内から実行

### Python Source Editor からUIを開く

1. Houdini で対象の HIP を開きます。
2. 上部メニューから `Windows > Python Source Editor` を開きます。
3. 下のコードを貼り付けます。
4. `Accept` または `Run` を押します。

```python
import runpy

tool = runpy.run_path(r"C:\Users\ponpa\Documents\houdinitotext\houdini_scene_to_text.py")
tool["show_export_ui"]()
```

UIが開いたら、通常はそのまま `書き出す` を押します。標準設定では現在フレーム1枚だけパラメータを評価し、SOP/DOP のジオメトリ取得やノード状態問い合わせは行いません。形式や HDA、アトリビュートなどの追加設定は `詳細設定` の中に畳んであります。

短い1行で起動したい場合は、起動専用ファイルを実行します。

```python
exec(open(r"C:\Users\ponpa\Documents\houdinitotext\launch_ui.py", encoding="utf-8").read())
```

メインスクリプトを直接実行する方式も使えます。

```python
exec(open(r"C:\Users\ponpa\Documents\houdinitotext\houdini_scene_to_text.py", encoding="utf-8").read())
```

### Shelf Tool に登録する場合

Shelf に Python Tool を作り、Script 欄に同じ1行を入れます。

```python
exec(open(r"C:\Users\ponpa\Documents\houdinitotext\launch_ui.py", encoding="utf-8").read())
```

### runpy で読み込む場合

同じ Houdini セッション内で関数として読み込みたい場合は、次のようにします。

```python
import runpy

tool = runpy.run_path(r"C:\Users\ponpa\Documents\houdinitotext\houdini_scene_to_text.py")
tool["show_export_ui"]()
```

### UIを使わずPythonから直接書き出す場合

これはUIを出さずに、現在のシーンをそのまま書き出します。

```python
import runpy

tool = runpy.run_path(r"C:\Users\ponpa\Documents\houdinitotext\houdini_scene_to_text.py")
paths = tool["export_current_scene"](
    output=r"C:\tmp\houdini_scene_export",
)
print(paths)
```

この場合、コンパクトな Markdown が作られます。

- `C:\tmp\houdini_scene_export.md`

標準設定では現在フレーム1枚だけパラメータを評価します。SOP ジオメトリ取得、DOP/SOP/TOP/ROP の状態問い合わせ、アトリビュート取得は行いません。

アトリビュート情報が必要なときだけ `include_geometry_summary=True` を指定してください。この場合、対象 SOP が cook される可能性があります。

```python
paths = tool["export_current_scene"](
    output=r"C:\tmp\houdini_scene_export",
    include_geometry_summary=True,
)
```

DOP などで「別の1フレームだけ確認したい」場合は、cook系オプションを明示したうえで `temporary_frame` を指定できます。処理後に元のフレームへ戻します。

```python
paths = tool["export_current_scene"](
    output=r"C:\tmp\houdini_scene_export",
    include_geometry_summary=True,
    temporary_frame=1,
)
```

## hython から実行

Houdini Command Line Tools など、`hython` が通っている環境で、HIP ファイルを指定して実行できます。

```powershell
hython C:\Users\ponpa\Documents\houdinitotext\houdini_scene_to_text.py C:\path\to\scene.hip --out C:\tmp\houdini_scene_export
```

選択中ノードだけを書き出す場合。選んだノードそのものだけを書き出し、子ノードには潜りません:

```powershell
hython C:\Users\ponpa\Documents\houdinitotext\houdini_scene_to_text.py C:\path\to\scene.hip --selected --out C:\tmp\selected_export
```

特定ネットワークだけを書き出す場合:

```powershell
hython C:\Users\ponpa\Documents\houdinitotext\houdini_scene_to_text.py C:\path\to\scene.hip --root /obj/geo1 --out C:\tmp\geo1_export
```

## 重要オプション

- `--format markdown`
  - 既定値。Markdown だけを書き出します。JSON も必要なら `--format both` を使います。
- `--include-scene-paths`
  - HIP ファイルパスやロード済み HDA ファイルパスも含めます。既定では出しません。
- `--markdown-mode compact`
  - 既定値。HIP ファイルパスや重複しやすい Node Graph の全ツリーは省き、接続、各ノードの見えるインスペクタ設定、コードを短くまとめます。Wrangle は VEX と Run Over を優先し、autobind/export/vex_* 系の細かい内部設定は出しません。ノードの所属階層は `/obj/geo1/...` のようなパスから読めます。`0` や空文字の値も含め、現在フレームで評価できた値を優先して書きます。デフォルト値の代用表示はしません。パラメータがないノードは `Params` 行を出しません。インスペクタ設定は 1 ノード最大 24 項目まで出し、超過分は件数だけ表示します。従来の詳細版が必要なら `--markdown-mode verbose`。
- `--markdown-mode verbose`
  - 詳細版です。UI既定のまま現在フレーム1枚だけ `parm.eval()` し、評価値を記録します。式や未展開文字列も併記します。
- `--hda-section-mode none`
  - 既定値。HDA セクション本文を含めません。
- `--hda-section-mode scene`
  - Embedded HDA と、SideFX 本体以外の HDA セクションを含めます。
- `--hda-section-mode all`
  - SideFX 標準 HDA の内部セクションまで含めます。かなり巨大になります。
- `--include-hidden-parms`
  - 隠しパラメータも含めます。既定では出しません。
- `--include-bypassed-nodes`
  - バイパスされたノードも含めます。既定では出しません。
- `--recurse-locked`
  - Locked HDA の中も再帰的に見ます。既定では潜りません。
- `--sync-delayed`
  - 遅延ロードされた HDA 定義を強制同期します。既定では行いません。
- `--max-text-chars 0`
  - 文字列の省略を無効にします。巨大な HIP では出力も大きくなります。
- `--changed-only`
  - デフォルト値から変わっているパラメータだけに絞ります。デフォルト判定を問い合わせるため、完全に安全寄りで読みたい場合はOFF推奨です。
- `--evaluate-parameters`
  - 既定値。現在フレーム1枚だけパラメータの評価値も記録します。
- `--no-evaluate-parameters`
  - パラメータ評価を行わず、`rawValue` / `unexpandedString` / `expression` だけで記録します。
- `--include-node-status`
  - ノードのエラー/警告/メッセージも記録します。DOP/SOP/TOP/ROP の状態確認が cook を誘発する場合があるため、既定では無効です。
- `--include-parameter-state`
  - パラメータの default/disabled/time-dependent 状態も記録します。cook を避けるため、既定では無効です。
- `--temporary-frame 1`
  - 書き出し中だけ指定フレームに移動し、最後に元のフレームへ戻します。別フレーム1枚を確認したい時に使います。
- `--include-geometry-summary`
  - 重要そうな SOP だけ cook して、ポイント数・プリミティブ数・絞り込んだアトリビュート情報を入れます。既定では無効です。
- `--skip-geometry-summary`
  - SOP の cook とアトリビュート出力を無効にします。現在の既定動作と同じです。
- `--geometry-node-mode important`
  - ジオメトリを見る SOP を絞ります。既定は display/render/selected/current と output/null/cache 系だけです。全部見るなら `all`、完全に切るなら `none`。
- `--geometry-sample-count 0`
  - 既定では属性値サンプルを取りません。数値を増やすとサンプル値を取り、-1 にすると全要素の値を出します。
- `--include-standard-attributes`
  - `P`, `N`, `uv`, `Cd`, `v`, `pscale` などの定番 point/vertex 属性も含めます。既定では省略します。
- `--include-private-attributes`
  - private 属性も含めます。既定では省略します。

## LLM に渡すなら

まずはコンパクトな `.md` を渡すのが読みやすいです。正確に検索・比較したい場合や、後で別ツールで加工したい場合だけ `.json` や `--markdown-mode verbose` を使ってください。

かなり大きいシーンでは、まず `--root /obj/対象ノード` で範囲を絞るのがおすすめです。`--changed-only` はデフォルト判定を問い合わせるため、安全最優先の確認ではOFFのままにしてください。
