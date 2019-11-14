-- agad-modeの使い方
-- https://agda.readthedocs.io/en/latest/tools/emacs-mode.html
{-# OPTIONS --without-K --safe #-}
module Learn.Interactive where

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
