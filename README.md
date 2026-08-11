# Houdini Scene To Text

Houdini 21 の現在の HIP シーンを、LLM に渡しやすい Markdown と、後から検索しやすい JSON に書き出す Python スクリプトです。

## できること

- `/` 以下、または指定ルート以下の全ノードを再帰的に収集
- SOP/OBJ/LOP/DOP/CHOP/COP/VOP/TOP/ROP/Subnet/HDA を同じ形式で記録
- ノードの親子構造、タイプ、カテゴリ、フラグ、コメント、ユーザーデータを記録
- 何が何に接続されているかを、入力/出力ポート名・番号つきで記録
- 全パラメータの種類、ラベル、テンプレート情報、値、式、キーフレーム、メニュー項目などを記録
- パラメータに式がある場合は、現在フレームの評価結果より式そのものを優先して表示（コンパクトを含む全モード）
- 数値チャンネルの各キーフレーム式（`$F`、`ch()`、`bezier()` 等）と式言語、文字列の `$HIP` / `$F` / バッククォート、チャンネル参照先、チャンネルエイリアス、CHOP 上書きを記録（JSON／詳細版は全キー、コンパクト版は重複しない意味のあるキー）
- APEX/KineFX のパック済みキャラクターは、Rig Tree の Packed Folders に相当する階層を記録
- Wrangle の `snippet`、Python SOP、Callback、VEX/VOP/HScript らしき文字列をコードブロックとして抽出
- 通常パラメータの `ch()` 式、グループ式、HDA の callback タグはコード欄へ重複掲載せず、対応するパラメータ／チャンネル情報としてのみ記録
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

UIが開いたら、通常はそのまま `書き出す` を押します。標準設定では現在フレーム1枚だけパラメータを評価し、通常の SOP/DOP アトリビュート取得やノード状態問い合わせは行いません。パック済みリグの候補 SOP だけは、Rig Tree 階層を確認するため cook される場合があります。形式や HDA、アトリビュートなどの追加設定は `詳細設定` の中に畳んであります。

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

標準設定では現在フレーム1枚だけパラメータを評価します。通常の SOP ジオメトリアトリビュート取得、DOP/SOP/TOP/ROP の状態問い合わせは行いません。パック済みリグの候補 SOP だけは Rig Tree 階層の確認対象です。

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
- `--markdown-mode smart`
  - 「スマートモード（実験的）」です。RBD に限らず、Houdini の各ノードで現在の Parameter Pane に見えている項目を対象にします。Wrangle などのコード中心ノードは、VEX を読みやすく保つ専用のコンパクト表示を継続します。
  - 内部パラメーター名ではなく実際の UI ラベルとフォルダ名を使い、メニューの `0` / `1` / `2` などは `None` / `Ground Plane` / `Height Field` のような表示名へ変換します。式をユーザーが設定した項目は、現在の評価値と式の原文を両方出します。HDA 定義にもともと入っている既定の内部リンク式は省きます。
  - 全ノードの変更された有効設定を出し、RBDやソルバーなどの重要ノードでは Parameter Pane 上部の主要な既定設定も少量補います。現在の UI で隠れている内部項目と無効な既定項目は省きます。このモードでは UI 状態を正しく判定するため `--include-parameter-state` 相当が自動的に有効になります。旧名 `--markdown-mode rbd_smart` も互換用エイリアスとして使用できます。
  - 参照した公式仕様: [hou.Parm](https://www.sidefx.com/docs/houdini/hom/hou/Parm.html)、[hou.OpNode.updateParmStates](https://www.sidefx.com/docs/houdini/hom/hou/OpNode.html)、[RBD Bullet Solver](https://www.sidefx.com/docs/houdini/nodes/sop/rbdbulletsolver.html)、[RBD Material Fracture](https://www.sidefx.com/docs/houdini/nodes/sop/rbdmaterialfracture-.html)。
- `--markdown-mode compact`
  - 既定値。HIP ファイルパスや重複しやすい Node Graph の全ツリーは省き、接続、各ノードの見えるインスペクタ設定、コードを短くまとめます。Wrangle は VEX と Run Over を優先し、autobind/export/vex_* 系の細かい内部設定は出しません。共通のノードパスは `Path base` として一度だけ書き、各見出しはそこからの正確な相対パスで表します。パラメータに式があれば ``expression=`ch(...)` `` のように式を最優先し、式がない場合は `0` や空文字を含む現在フレームの評価値を書きます。通常の式を保存するためだけの「単一F1キー」は `Params` と重複するため再掲せず、複数キー、F1以外のキー、補間キー、チャンネル参照先、CHOP 上書きは個別に表示します。パラメータがないノードは `Params` 行を出しません。インスペクタ設定は 1 ノード最大 24 項目まで出し、超過分は件数だけ表示します。省略分は不明として扱い、デフォルト値とはみなしません。従来の詳細版が必要なら `--markdown-mode verbose`。
  - 接続はネットワーク（親ノード）ごとにまとめ、ノードは相対名で書きます。第1入力への直列接続は `grid1 -> subdivide1 -> COPY` のようにチェーン表記へ圧縮し、それ以外のポートは `[output2]` / `[input3: Constraint Geometry]` のようにポート名とラベルで明示します。
  - ワイヤー中継用のドット（丸い中継点）は透過して、ノード同士の直接接続として書きます（出力ポート番号もドット越しに保持。JSON では `via_dots` に経由したドットを記録）。
  - どこにも接続されていないノードは `Not wired:` 行に列挙します。
  - フォルダの開閉状態パラメータ（`folder3` 等）や、ランプの各ポイントのバラバラな内部パラメータは省き、ランプは `ramp (0, 1) (1, 1) @ Catmull-Rom` の1行に要約します。
  - 長大な16進列・エンコード済みストロークデータなどは本文を展開せず、文字数と SHA-256 に要約します。JSON 側の元データは維持します。
  - Inspector Settings のノード順は重要度ベースです。LLM は長文の先頭と末尾への注意力が高いため、ソルバー・Wrangle・フラクチャ等の重要ノードを最初と最後に、box / merge / transform 等の脇役を中央に配置します。
  - ソルバー等の重要ノードは、全パラメータがデフォルトでも `- Defaults:` 行として先頭側の主要パラメータを最大10個表示します（Houdini の UI は重要な設定ほど上に並ぶため、汎用的にどのノードタイプでも機能します）。
  - 末尾に LLM 向けの短い日本語の指示文（このダンプを根拠に、不確かな仕様は SideFX の最新公式ドキュメントを調べ、正確な Houdini 知識で答える等）と「ファイルキャッシュなどは毎回きちんと更新しています。」という注意書きを自動で付けます。全モード共通です。
  - ユーザーがリネームしたノード（名前からタイプが読めないノード）には `` `COPY` (Copy to Points) `` のようにノードタイプのラベルを併記します。
  - デフォルト値のままのパラメータは省略し、ユーザーが変更した値だけを出します（JSON には全パラメータが残ります）。
  - プルダウン（メニュー）パラメータは `2` のような内部インデックスではなく、UI に見えているメニューラベルで書きます。
- `--markdown-mode verbose`
  - 詳細版です。UI既定のまま現在フレーム1枚だけ `parm.eval()` し、評価値を記録します。式や未展開文字列も併記します。
- `--markdown-mode attributes`
  - アトリビュートモード（旧称 ultra。互換のため `--markdown-mode ultra` も同じ動作）。ジオメトリを cook して、各アトリビュートのサンプル値を既定で5個ずつ書き出します（`(first 5 of 12000 elements)` のように全体数も併記）。連続して同じ値は `0.5 (x5)` のようにまとめます。全要素が必要なら `--geometry-sample-count -1` を併用してください。
  - point / primitive / vertex / edge の各グループも `#### primitive group (3021 of 584176 primitives)` のようにアトリビュートと並べて出力します。detail（global）アトリビュートも値付きで出ます。
  - 複数ノード選択（`--selected` で複数選択）にも対応しており、選択した各ノードごとにパラメータとアトリビュートのセクションが並びます。cook が走るため、対象は必要なノードに絞るのがおすすめです。
  - パラメータはデフォルトから変更されたものだけをラベル・式付きで出し、残りは `N parameters at default omitted` の1行にまとめます（全パラメータ値が必要なら JSON か verbose を使ってください）。フォルダ・セパレータ・ラベル・ボタンなどUI専用パラメータは出しません。
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
- `--include-network-items`
  - 付箋（スティッキーノート）、ネットワークボックス、ワイヤー中継ドットのレコードも JSON に含めます。既定では見た目用の要素なので出しません。ドットは常に直結扱いへ変換されます。
- `--recurse-locked`
  - Locked HDA の中も再帰的に見ます。既定では潜りません。
- `--sync-delayed`
  - 遅延ロードされた HDA 定義を強制同期します。既定では行いません。
- `--max-text-chars 0`
  - 文字列の省略を無効にします。巨大な HIP では出力も大きくなります。
- `--changed-only`
  - JSON も含めて、デフォルト値から変わっているパラメータだけに絞ります。コンパクト Markdown は既定でもデフォルト値のパラメータを省略するので、主に JSON を小さくしたいときに使います。デフォルト判定を問い合わせるため、完全に安全寄りで読みたい場合はOFF推奨です。
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
- `--include-packed-rig-trees` / `--skip-packed-rig-trees`
  - 既定ではパック生成系の SOP だけからパック済みキャラクターのフォルダ階層を取得し、コンパクト／詳細／アトリビュート Markdown と JSON に出します。Rig Tree の `Packed Folders` 表示に相当します。アトリビュート取得を有効にした場合は、すでに cook 対象になっているジオメトリも確認します。通常の選択ノードをリグツリー確認だけのために cook することはありません。不要なら `--skip-packed-rig-trees` で無効化できます。

## LLM に渡すなら

まずはコンパクトな `.md` を渡すのが読みやすいです。正確に検索・比較したい場合や、後で別ツールで加工したい場合だけ `.json` や `--markdown-mode verbose` を使ってください。

かなり大きいシーンでは、まず `--root /obj/対象ノード` で範囲を絞るのがおすすめです。`--changed-only` はデフォルト判定を問い合わせるため、安全最優先の確認ではOFFのままにしてください。
