{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Product.Generic.Properties where

-- agda-stdlib
open import Algebra

-- agda-misc
open import Math.NumberTheory.Summation.Generic.Properties

-- TODO add renamaings
module CommutativeMonoidProductProperties {c e} (CM : CommutativeMonoid c e) =
  CommutativeMonoidSummationProperties CM
  renaming
  ( Σ<-cong to Π<-cong
  ; Σ<-congˡ to Π<-congˡ
  ; Σ<-congʳ to Π<-congʳ
  ; Σ≤-cong to Π≤-cong
  ; Σ≤-congˡ to Π≤-congˡ
  ; Σ≤-congʳ to Π≤-congʳ
  ; Σ<range-cong to Π<range-cong
  ; Σ<range-cong₁ to Π<range-cong₁
  ; Σ<range-cong₂₃ to Π<range-cong₂₃
  ; Σ<range-cong₂ to Π<range-cong₂
  ; Σ<range-cong₃ to Π<range-cong₃
  ; Σ≤range-cong to Π≤range-cong
  ; Σ<-0 to Π<-1
  ; Σ≤-0 to Π≤-1
  ; Σ<[f,1]≈f[0] to Π<[f,1]≈f[0]
  ; Σ≤[f,0]≈f[0] to Π≤[f,0]≈f[0]
  ; n≤m⇒Σ<range[f,m,n]≈0 to n≤m⇒Π<range[f,m,n]≈1
  ; Σ<range[f,n,n]≈0 to Π<range[f,n,n]≈1
  ; n<m⇒Σ≤range[f,m,n]≈0 to n<m⇒Π≤range[f,m,n]≈1
  ; Σ≤range[f,n,n]≈f[n] to Π≤range[f,n,n]≈f[n]
  ; Σ<-+ to Π<-+
  ; Σ≤-Σ<-+ to Π≤-Π<-+
  ; Σ≤-+ to Π≤-+
  ; Σ<-push-suc to Π<-push-suc
  ; Σ≤-push-suc to Π≤-push-suc
  ; Σ<range[f,0,n]≈Σ<[f,n] to Π<range[f,0,n]≈Π<[f,n]
  ; Σ≤range[f,0,n]≈Σ≤[f,n] to Π≤range[f,0,n]≈Π≤[f,n]
  ; Σ<range[f,m,m+n+o]≈Σ<range[f,m,m+n]+Σ<range[m+n,m+n+o] to
      Π<range[f,m,m+n+o]≈Π<range[f,m,m+n]*Π<range[m+n,m+n+o]
  ; Σ<range[f,m,n]≈Σ<range[f,m,o]+Σ<range[f,o,n] to
      Π<range[f,m,n]≈Π<range[f,m,o]*Π<range[f,o,n]
  ; Σ<range[f,m,n]≈Σ<range[i→f[i∸o],o+m,o+n] to
      Π<range[f,m,n]≈Π<range[i→f[i∸o],o+m,o+n]
  ; Σ<-const to Π<-const
  ; Σ≤-const to Π≤-const
  ; Σ<range-const to Π<range-const
  ; Σ≤range-const to Π≤range-const
  ; Σ<-distrib-+ to Π<-distrib-*
  ; Σ≤-distrib-+ to Π≤-distrib-*
  ; Σ<range-distrib-+ to Π<range-distrib-*
  ; Σ≤range-distrib-+ to Π≤range-distrib-*
  ; Σ<-comm to Π<-comm
  ; Σ≤-comm to Π≤-comm
  ; Σ<range-comm to Π<range-comm
  ; Σ≤range-comm to Π≤range-comm
  ; Σ<-sumₜ-syntax to Π<-sumₜ-syntax
  )
  using ()
