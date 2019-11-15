-- agad-modeの使い方
-- https://agda.readthedocs.io/en/latest/tools/emacs-mode.html
{-# OPTIONS --without-K --safe #-}
module Learn.Interactive where

-- ロード
-- タイプチェックする
-- C-c C-l
-- Ctrlを押しながら、cを押して次にlを押す
-- このとき、ソース内に"?"が存在すればそれをゴールにする
-- ゴールには番号が振られる

-- 型推論する
-- C-c C-d

-- 評価する
-- C-c C-n

-- 終了させる
-- C-c C-x C-q
-- Ctrlを押しながら、c、x、qと押す

-- 再スタートさせる
-- C-c C-x C-r

----------------------------------------------------------------------------
-- ゴールへの操作
-- ゴール内に値を書いてからゴールにカーソルを合わせ実行する。

-- 与える
-- C-c C-SPC
-- Ctrlを押しながら、cを押して次にスペースを押す
-- 型が合っていればゴールは消える

-- リファイン
-- C-c C-r
-- 何もない状態で行うと関数ならラムダ、レコード型ならコンストラクタを挿入する
-- ゴールに関数がある場合、関数の引数をゴールにする

-- ケーススプリット
-- C-c C-c
-- ゴール内に変数を書く、またはC-c C-cして出てきた入力枠に変数を入力すると
-- その変数でパターンマッチングを行う

-- ゴールの型を確認する
-- C-c C-t

-- 環境を確認する
-- C-c C-e

----------------------------------------------------------------------------
-- 自然数
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- 等価性
infix 3 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

-- 足し算
-- 右辺に?と書いてC-c C-l(ロード)する
-- モジュールは無視で
module Step1 where
  _+_ : ℕ → ℕ → ℕ
  m + n = {!   !}

-- ゴールに"m"と入力する
module Step2 where
  _+_ : ℕ → ℕ → ℕ
  m + n = {! m  !}

--　ゴールにカーソルを合わせ C-c C-c (ケーススプリット)する
module Step3 where
  _+_ : ℕ → ℕ → ℕ
  zero + n = {!   !}
  suc m + n = {!   !}

-- インデントを整える
module Step4 where
  _+_ : ℕ → ℕ → ℕ
  zero  + n = {!   !}
  suc m + n = {!   !}

-- ゴール内に右辺値を書く
module Step5 where
  _+_ : ℕ → ℕ → ℕ
  zero  + n = {! zero  !}
  suc m + n = {!   !}

-- ゴールにカーソルを合わせ C-c C-SPC (Give)する
module Step6 where
  _+_ : ℕ → ℕ → ℕ
  zero  + n = zero
  suc m + n = {!   !}

-- もう一方のゴールも同様にする
-- このときmは再帰的な呼び出しをするときに小さくなっている
_+_ : ℕ → ℕ → ℕ
zero  + n = zero
suc m + n = suc (m + n)

-- +の結合性
-- 証明したい型を書く。右辺を?にしてゴールにする
module Assoc1 where
  +-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
  +-assoc m n o = {!   !}

-- このとき+の定義から+の左の変数で帰納するとよいとわかる
-- 単一の変数であるならばパターンマッチングできるのでmを選びゴールに書く
module Assoc2 where
  +-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
  +-assoc m n o = {! m  !}

-- C-c C-cする
-- ここで +-assoc zero n o の右辺のゴールでC-c C-tすると　zero ≡ zero とわかる
-- 同じ形ならreflが使えるのでreflをC-c C-SPCする
module Assoc3 where
  +-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
  +-assoc zero    n o = refl
  +-assoc (suc m) n o = {!   !}

-- 次に +-assoc (suc m) n o の右辺でC-c C-tすると
-- suc ((m + n) + o) ≡ suc (m + (n + o)) とわかる
-- 両辺に同じ関数（suc）が掛かっているのでcongが使える
-- congとゴール内に書く
module Assoc4 where
  +-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
  +-assoc zero    n o = refl
  +-assoc (suc m) n o = {!cong   !}

-- C-c C-rするとゴールが分かれる
-- 前はsucを与える
module Assoc5 where
  +-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
  +-assoc zero    n o = refl
  +-assoc (suc m) n o = cong suc {!   !}

-- 後ろは+-assoc m n oの型と同じなのでそれを与える
-- これで証明終了
module Assoc6 where
  +-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
  +-assoc zero    n o = refl
  +-assoc (suc m) n o = cong suc (+-assoc m n o)
