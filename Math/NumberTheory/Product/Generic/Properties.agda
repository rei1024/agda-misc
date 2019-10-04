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
  ; Σ<range-cong₃ to Π<range-cong₃
  ; Σ<range-cong₁₂ to Π<range-cong₁₂
  ; Σ<range-cong₁ to Π<range-cong₁
  ; Σ<range-cong₂ to Π<range-cong₂
  ; Σ≤range-cong to Π≤range-cong
  ; Σ<-0 to Π<-1
  ; Σ≤-0 to Π≤-1
  ; Σ<[1,f]≈f[0] to Π<[1,f]≈f[0]
  ; Σ≤[0,f]≈f[0] to Π≤[0,f]≈f[0]
  ; n≤m⇒Σ<range[m,n,f]≈0 to n≤m⇒Π<range[m,n,f]≈1
  ; Σ<range[n,n,f]≈0 to Π<range[n,n,f]≈1
  ; n<m⇒Σ≤range[m,n,f]≈0 to n<m⇒Π≤range[m,n,f]≈1
  ; Σ≤range[n,n,f]≈f[n] to Π≤range[n,n,f]≈f[n]
  ; Σ<-+ to Π<-+
  ; Σ≤-Σ<-+ to Π≤-Π<-+
  ; Σ≤-+ to Π≤-+
  ; Σ<-push-suc to Π<-push-suc
  ; Σ≤-push-suc to Π≤-push-suc
  ; Σ<range[0,n,f]≈Σ<[n,f] to Π<range[0,n,f]≈Π<[n,f]
  ; Σ≤range[0,n,f]≈Σ≤[n,f] to Π≤range[0,n,f]≈Π≤[n,f]
  ; Σ<range[m,m+n+o,f]≈Σ<range[m,m+n,f]+Σ<range[m+n,m+n+o,f] to
      Π<range[m,m+n+o,f]≈Π<range[m,m+n,f]*Π<range[m+n,m+n+o,f]
  ; Σ<range[m,n,f]≈Σ<range[m,o,f]+Σ<range[o,n,f] to
      Π<range[m,n,f]≈Π<range[m,o,f]*Π<range[o,n,f]
  ; Σ<range[m,n,f]≈Σ<range[o+m,o+n,i→f[i∸o]] to
      Π<range[m,n,f]≈Π<range[o+m,o+n,i→f[i∸o]]
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
  ; Σ<-reverse to Π<-reverse
  ; Σ≤-reverse to Π≤-reverse
  )
  using ()
