# kuromine-proof-lean4

黒峰方程式の簡略化された証明を Lean 4 で形式化したものです。

```text
2^x + 3^y + 5 = z^3.
```

主定理では、整数解が次の2つに限られることを証明します。

```text
(x, y, z) = (1, 0, 2), (5, 3, 4).
```

整数指数は `ℚ` 上の冪として解釈します。

## 主定理

```lean
theorem classify_integer_solutions
    {x y z : ℤ}
    (h : SolvesInteger x y z) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 5 ∧ y = 3 ∧ z = 4)
```

## 証明の構成

1. 分母を払ったうえで、法 `2` または法 `3` による議論を用いて負の指数を排除します。
2. 指数が小さい場合を直接分類します。
3. 素数
   `73, 13, 577, 97, 673, 337, 43, 1009`
   を用いる8段階の有限ふるいにより、`(1008, 336)` を法とする3つの剰余類だけが残ります。
4. これらの剰余類から
   `x ≡ 1 (mod 4)` および `y ≡ 45 (mod 48)`
   が従います。
5. 残る範囲を
   `A = z - 3^(y/3)` とヤコビ記号 `(-10 / A)`
   を用いて排除します。

Lean の各モジュールも同じ大筋の議論に従い、再利用可能な計算部分と健全性の証明を分離しています。

- `SmallCases` は直接的な場合分けを扱います。
- `Sieve.Core`、`Sieve.Soundness`、`Sieve.Initial`、`Sieve.Certificate` は、有限ふるいの計算とその数学的な正当化を分離します。
- `LargeCase` は、ふるいによって得られた合同条件がヤコビ記号を用いる議論と矛盾することを証明します。
- `NaturalClassification` は自然数の場合の分類をまとめます。
- `Main` は整数解の問題を自然数解の分類へ帰着します。

有限ふるいの最終的な計算は `native_decide` によって検証し、その健全性は別途証明しています。

## ビルド

このプロジェクトでは Lean 4.30.0 と mathlib 4.30.0 を使用しています。

```bash
lake exe cache get
lake build
```

GitHub Actions では、push および pull request のたびに同じ証明検証を実行します。

## 参考資料

ここで形式化した簡略化証明は、次の記事で説明されています。

- https://smooth-pudding.hatenablog.com/entry/2026/07/26/082029

以前の完全な Lean 形式化を技術的な参考資料として使用しました。

- https://github.com/nakashima-hikaru/kuromine-lean4

同リポジトリをもとに改変したコードは、Apache License 2.0 に基づいて使用しています。
